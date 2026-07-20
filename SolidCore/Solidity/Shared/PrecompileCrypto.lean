import EvmYul.SpongeHash.Keccak256

/-!
Pure, total implementations of the cryptographic cores behind the EVM
precompiled contracts that the semantics answers in-model:

  * SHA-256 (precompile 0x2)
  * RIPEMD-160 (precompile 0x3)
  * secp256k1 public-key recovery / `ecrecover` (precompile 0x1)
  * BN254 (alt_bn128) G1 addition and scalar multiplication (0x6 / 0x7)
  * BLAKE2b compression function F (0x9)

Everything here is plain executable Lean over `Nat`/`UInt32`/`UInt64` — no
`@[extern]`, no axioms, no `sorry`. Byte-level parity against ground truth
(the pinned evmyul native `sha256` and published known-answer vectors) is
witnessed by `lake exe precompileParity`.

Bytes are the semantics' `List Nat` byte lists; callers pass NORMALIZED
bytes (each element < 256).
-/

namespace SolidCore.Solidity.Shared.Crypto

abbrev Byte := Nat
abbrev Bytes := List Byte

/-! ### Byte/word helpers -/

/-- Big-endian bytes of `value`, exactly `width` bytes (truncates above). -/
def natToBytesBE : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, value => natToBytesBE w (value / 256) ++ [value % 256]

def bytesToNatBE (bytes : Bytes) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b % 256) 0

/-- First `width` bytes of `bytes` starting at `offset`, zero-padded on the
    right (EVM calldata-read convention). -/
def sliceZeroPadded (bytes : Bytes) (offset width : Nat) : Bytes :=
  let slice := (bytes.drop offset).take width
  slice ++ List.replicate (width - slice.length) 0

/-! ### Modular arithmetic -/

/-- Binary modular exponentiation, total by `exp` halving. -/
def powModAux (m base exp acc : Nat) : Nat :=
  if h : exp = 0 then
    acc % m
  else
    let acc' := if exp % 2 == 1 then acc * base % m else acc
    powModAux m (base * base % m) (exp / 2) acc'
termination_by exp
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

def powMod (m base exp : Nat) : Nat :=
  powModAux m (base % m) exp 1

/-- Fermat inverse (callers guarantee `m` prime and `a % m ≠ 0`). -/
def invMod (m a : Nat) : Nat :=
  powMod m a (m - 2)

def subMod (m a b : Nat) : Nat :=
  (a % m + (m - b % m)) % m

/-! ### Short-Weierstrass curves `y² = x³ + b` over prime `p` (a = 0).

Both curves used by the precompiles have `a = 0`: secp256k1 (`b = 7`) and
BN254/alt_bn128 (`b = 3`). Points are affine with an explicit infinity
(`none`); all coordinates are kept reduced (`< p`). -/

abbrev Point := Option (Nat × Nat)

def onCurve (p b x y : Nat) : Bool :=
  y * y % p == (x * x % p * x + b) % p

def pointDouble (p : Nat) : Point → Point
  | none => none
  | some (x, y) =>
      if y % p == 0 then none
      else
        let lam := 3 * x * x % p * invMod p (2 * y % p) % p
        let x3 := subMod p (lam * lam) (2 * x)
        some (x3, subMod p (lam * subMod p x x3) y)

def pointAdd (p : Nat) : Point → Point → Point
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
      if x1 % p == x2 % p then
        if (y1 + y2) % p == 0 then none
        else pointDouble p (some (x1, y1))
      else
        let lam := subMod p y2 y1 * invMod p (subMod p x2 x1) % p
        let x3 := subMod p (lam * lam) (x1 + x2)
        some (x3, subMod p (lam * subMod p x1 x3) y1)

/-- Double-and-add scalar multiplication, total by `k` halving. -/
def pointMul (p : Nat) (k : Nat) (pt : Point) : Point :=
  if h : k = 0 then none
  else
    let rest := pointMul p (k / 2) (pointDouble p pt)
    if k % 2 == 1 then pointAdd p rest pt else rest
termination_by k
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

/-! ### secp256k1 recovery (`ecrecover`, precompile 0x1) -/

def secpP : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def secpN : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def secpGx : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

def secpGy : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- Recover the 64-byte uncompressed public key from `(digest, v, r, s)`,
    with EXACTLY evmyul's `Ξ_ECREC` validity gate (`v ∈ {27, 28}`,
    `0 < r < n`, `0 < s < n`); `none` for any invalid signature (including
    an `r` with no on-curve lifting or a point-at-infinity result). -/
def secpRecoverPubkey? (digest v r s : Nat) : Option (Nat × Nat) :=
  if v < 27 || 28 < v || r == 0 || secpN <= r || s == 0 || secpN <= s then
    none
  else
    let p := secpP
    -- Lift r to an on-curve point (p ≡ 3 mod 4, so sqrt is pow (p+1)/4).
    let ySq := (r * r % p * r + 7) % p
    let y0 := powMod p ySq ((p + 1) / 4)
    if y0 * y0 % p != ySq then
      none
    else
      let y := if y0 % 2 == v - 27 then y0 else p - y0
      let rInv := invMod secpN r
      -- Q = (-z·r⁻¹)·G + (s·r⁻¹)·R  (all scalars mod n)
      let u1 := (secpN - digest % secpN) % secpN * rInv % secpN
      let u2 := s % secpN * rInv % secpN
      pointAdd p
        (pointMul p u1 (some (secpGx, secpGy)))
        (pointMul p u2 (some (r, y)))

/-- `ecrecover` byte-level body: reads the first 128 calldata bytes
    zero-padded, returns the 32-byte zero-padded address on success and `[]`
    on any invalid signature — always with call success (mirrors `Ξ_ECREC`,
    which returns success with empty output on a bad signature). -/
def ecrecoverBytes (input : Bytes) : Bytes :=
  let digest := bytesToNatBE (sliceZeroPadded input 0 32)
  let v := bytesToNatBE (sliceZeroPadded input 32 32)
  let r := bytesToNatBE (sliceZeroPadded input 64 32)
  let s := bytesToNatBE (sliceZeroPadded input 96 32)
  match secpRecoverPubkey? digest v r s with
  | none => []
  | some (qx, qy) =>
      let pub := natToBytesBE 32 qx ++ natToBytesBE 32 qy
      let hash := EvmYul.SpongeHash.Keccak256.keccak256Bytes pub
      List.replicate 12 0 ++ hash.drop 12

/-! ### BN254 / alt_bn128 G1 (precompiles 0x6, 0x7) -/

def bnP : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Decode an EVM-encoded G1 point: `(0,0)` is infinity; other points must
    have reduced coordinates AND lie on `y² = x³ + 3`, else the precompile
    errors (`none`). -/
def bnDecodePoint? (x y : Nat) : Option Point :=
  if bnP <= x || bnP <= y then none
  else if x == 0 && y == 0 then some none
  else if onCurve bnP 3 x y then some (some (x, y))
  else none

def bnEncodePoint : Point → Bytes
  | none => List.replicate 64 0
  | some (x, y) => natToBytesBE 32 x ++ natToBytesBE 32 y

/-- `bnAdd` (0x6): reads 128 calldata bytes zero-padded; `none` is the
    precompile ERROR (invalid point), surfacing as a failed staticcall. -/
def bnAddBytes? (input : Bytes) : Option Bytes := do
  let x1 := bytesToNatBE (sliceZeroPadded input 0 32)
  let y1 := bytesToNatBE (sliceZeroPadded input 32 32)
  let x2 := bytesToNatBE (sliceZeroPadded input 64 32)
  let y2 := bytesToNatBE (sliceZeroPadded input 96 32)
  let p1 ← bnDecodePoint? x1 y1
  let p2 ← bnDecodePoint? x2 y2
  pure (bnEncodePoint (pointAdd bnP p1 p2))

/-- `bnMul` (0x7): reads 96 calldata bytes zero-padded; the scalar is any
    256-bit word (no reduction needed — the group order divides out in
    double-and-add). `none` is the precompile ERROR. -/
def bnMulBytes? (input : Bytes) : Option Bytes := do
  let x := bytesToNatBE (sliceZeroPadded input 0 32)
  let y := bytesToNatBE (sliceZeroPadded input 32 32)
  let k := bytesToNatBE (sliceZeroPadded input 64 32)
  let pt ← bnDecodePoint? x y
  pure (bnEncodePoint (pointMul bnP k pt))

/-! ### SHA-256 (precompile 0x2) -/

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat ((32 - n) % 32))

/-- Merkle–Damgård padding with a BIG-endian 64-bit bit-length (SHA-256). -/
def mdPadBE (msg : Bytes) : Bytes :=
  let len := msg.length
  let zeros := (64 + 55 - len % 64) % 64
  msg ++ [0x80] ++ List.replicate zeros 0 ++ natToBytesBE 8 (8 * len)

/-- Big-endian 32-bit words of a byte array (length a multiple of 4). -/
def bytesToWords32BE (bytes : Array Byte) : Array UInt32 := Id.run do
  let mut out : Array UInt32 := #[]
  for i in [0 : bytes.size / 4] do
    out := out.push (UInt32.ofNat
      (((bytes[4*i]!) % 256) * 16777216 + ((bytes[4*i+1]!) % 256) * 65536 +
        ((bytes[4*i+2]!) % 256) * 256 + (bytes[4*i+3]!) % 256))
  return out

def sha256Compress (h : Array UInt32) (block : Array UInt32) :
    Array UInt32 := Id.run do
  let mut w := block
  for i in [16 : 64] do
    let w15 := w[i-15]!
    let w2 := w[i-2]!
    let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0 : 64] do
    let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    hh := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-256 of a byte list; 32-byte digest. -/
def sha256Bytes (msg : Bytes) : Bytes := Id.run do
  let padded := (mdPadBE msg).toArray
  let words := bytesToWords32BE padded
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372,
    0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in [0 : words.size / 16] do
    h := sha256Compress h (words.extract (16 * blk) (16 * blk + 16))
  let mut out : Bytes := []
  for i in [0 : 8] do
    out := out ++ natToBytesBE 4 (h[i]!).toNat
  return out

/-! ### RIPEMD-160 (precompile 0x3) -/

def ripemdRL : Array Nat := #[
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
  7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
  3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,
  1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
  4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13]

def ripemdRR : Array Nat := #[
  5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,
  6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
  15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,
  8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
  12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11]

def ripemdSL : Array Nat := #[
  11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,
  7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
  11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,
  11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
  9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6]

def ripemdSR : Array Nat := #[
  8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,
  9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
  9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,
  15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
  8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11]

def rotl32 (x : UInt32) (n : Nat) : UInt32 :=
  (x <<< UInt32.ofNat n) ||| (x >>> UInt32.ofNat ((32 - n) % 32))

/-- The round function for step `j` (0-based, left lane order). -/
def ripemdF (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~x) &&& z)
  else if j < 48 then (x ||| (~~~y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (~~~z))
  else x ^^^ (y ||| (~~~z))

def ripemdKL (j : Nat) : UInt32 :=
  if j < 16 then 0 else if j < 32 then 0x5A827999
  else if j < 48 then 0x6ED9EBA1 else if j < 64 then 0x8F1BBCDC
  else 0xA953FD4E

def ripemdKR (j : Nat) : UInt32 :=
  if j < 16 then 0x50A28BE6 else if j < 32 then 0x5C4DD124
  else if j < 48 then 0x6D703EF3 else if j < 64 then 0x7A6D76E9
  else 0

/-- Merkle–Damgård padding with a LITTLE-endian 64-bit bit length. -/
def mdPadLE (msg : Bytes) : Bytes :=
  let len := msg.length
  let zeros := (64 + 55 - len % 64) % 64
  msg ++ [0x80] ++ List.replicate zeros 0 ++
    (natToBytesBE 8 (8 * len)).reverse

/-- Little-endian 32-bit words of a byte array (length a multiple of 4). -/
def bytesToWords32LE (bytes : Array Byte) : Array UInt32 := Id.run do
  let mut out : Array UInt32 := #[]
  for i in [0 : bytes.size / 4] do
    out := out.push (UInt32.ofNat
      (((bytes[4*i+3]!) % 256) * 16777216 + ((bytes[4*i+2]!) % 256) * 65536 +
        ((bytes[4*i+1]!) % 256) * 256 + (bytes[4*i]!) % 256))
  return out

def ripemdCompress (h : Array UInt32) (x : Array UInt32) :
    Array UInt32 := Id.run do
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!
  let mut d := h[3]!; let mut e := h[4]!
  let mut a' := h[0]!; let mut b' := h[1]!; let mut c' := h[2]!
  let mut d' := h[3]!; let mut e' := h[4]!
  for j in [0 : 80] do
    let t := rotl32 (a + ripemdF j b c d + x[ripemdRL[j]!]! + ripemdKL j)
        (ripemdSL[j]!) + e
    a := e; e := d; d := rotl32 c 10; c := b; b := t
    let t' := rotl32 (a' + ripemdF (79 - j) b' c' d' + x[ripemdRR[j]!]! +
        ripemdKR j) (ripemdSR[j]!) + e'
    a' := e'; e' := d'; d' := rotl32 c' 10; c' := b'; b' := t'
  return #[h[1]! + c + d', h[2]! + d + e', h[3]! + e + a',
           h[4]! + a + b', h[0]! + b + c']

/-- RIPEMD-160 of a byte list; 20-byte digest (little-endian words out). -/
def ripemd160Bytes (msg : Bytes) : Bytes := Id.run do
  let padded := (mdPadLE msg).toArray
  let words := bytesToWords32LE padded
  let mut h : Array UInt32 := #[0x67452301, 0xEFCDAB89, 0x98BADCFE,
    0x10325476, 0xC3D2E1F0]
  for blk in [0 : words.size / 16] do
    h := ripemdCompress h (words.extract (16 * blk) (16 * blk + 16))
  let mut out : Bytes := []
  for i in [0 : 5] do
    out := out ++ (natToBytesBE 4 (h[i]!).toNat).reverse
  return out

/-! ### BLAKE2b compression F (precompile 0x9, EIP-152) -/

def blake2Sigma : Array (Array Nat) := #[
  #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
  #[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
  #[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
  #[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
  #[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
  #[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
  #[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
  #[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
  #[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
  #[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

def blake2IV : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
  0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
  0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def rotr64 (x : UInt64) (n : Nat) : UInt64 :=
  (x >>> UInt64.ofNat n) ||| (x <<< UInt64.ofNat ((64 - n) % 64))

/-- One G mixing step on the 16-word state. -/
def blake2G (v : Array UInt64) (a b c d : Nat) (x y : UInt64) :
    Array UInt64 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 32)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 24)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 63)
  return v

/-- The BLAKE2b compression function F (EIP-152 semantics: caller-supplied
    round count; `f` is the final-block flag). -/
def blake2fCompress (rounds : Nat) (h : Array UInt64) (m : Array UInt64)
    (t0 t1 : UInt64) (f : Bool) : Array UInt64 := Id.run do
  let mut v : Array UInt64 := h ++ blake2IV
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  if f then
    v := v.set! 14 (~~~v[14]!)
  for r in [0 : rounds] do
    let s := blake2Sigma[r % 10]!
    v := blake2G v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := blake2G v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := blake2G v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := blake2G v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := blake2G v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := blake2G v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := blake2G v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := blake2G v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  let mut out := h
  for i in [0 : 8] do
    out := out.set! i (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

def bytesToU64LE (bytes : Array Byte) (offset : Nat) : UInt64 :=
  UInt64.ofNat (bytesToNatBE
    ((List.range 8).map (fun i => bytes[offset + 7 - i]! % 256)))

def u64ToBytesLE (x : UInt64) : Bytes :=
  (natToBytesBE 8 x.toNat).reverse

/-- Fail-closed bound on the caller-supplied BLAKE2f round count. Real gas
    metering (1 gas per round, EIP-152) bounds mainnet-reachable rounds; the
    gas-free model instead refuses (`none` → open-world fail-closed, exactly
    today's behaviour) above this bound rather than model unbounded work. -/
def blake2fRoundsCap : Nat := 1000000

/-- `blake2f` (0x9): `some (success, output)` when answered in-model —
    a malformed input (length ≠ 213 or final-flag byte ∉ {0,1}) is the
    precompile ERROR `some (false, [])`; `none` (unanswered, fail-closed)
    only above `blake2fRoundsCap`. -/
def blake2fBytes? (input : Bytes) : Option (Bool × Bytes) :=
  if input.length != 213 then
    some (false, [])
  else
    let arr := input.toArray
    let fByte := arr[212]! % 256
    if fByte != 0 && fByte != 1 then
      some (false, [])
    else
      let rounds := bytesToNatBE (sliceZeroPadded input 0 4)
      if blake2fRoundsCap < rounds then
        none
      else Id.run do
        let mut h : Array UInt64 := #[]
        for i in [0 : 8] do
          h := h.push (bytesToU64LE arr (4 + 8 * i))
        let mut m : Array UInt64 := #[]
        for i in [0 : 16] do
          m := m.push (bytesToU64LE arr (68 + 8 * i))
        let t0 := bytesToU64LE arr 196
        let t1 := bytesToU64LE arr 204
        let h' := blake2fCompress rounds h m t0 t1 (fByte == 1)
        let mut out : Bytes := []
        for i in [0 : 8] do
          out := out ++ u64ToBytesLE h'[i]!
        return some (true, out)

end SolidCore.Solidity.Shared.Crypto

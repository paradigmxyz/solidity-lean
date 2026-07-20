import SolidCore.Solidity.Shared.PrecompileCrypto

/-!
Pure, total pairing cryptography for the two hardest EVM precompiles:

  * BN254 / alt_bn128 pairing check (`ecpairing`, precompile 0x8, EIP-197)
  * BLS12-381 KZG point evaluation (precompile 0xa, EIP-4844)

Approach. Both checks only ask whether a PRODUCT of pairings equals one.
Any non-degenerate bilinear pairing `G1 × G2 → μ_r` decides that question
identically: two such pairings differ by a fixed exponent coprime to `r`
(both groups are cyclic of prime order `r`), so a product is 1 under one
pairing iff it is 1 under the other. We therefore implement the REDUCED
TATE pairing — a Miller loop `f_{r,P}(Q)` over the group order `r` with
denominator elimination, followed by the full final exponentiation
`(p¹² - 1) / r` — instead of the optimal-ate loop the specs describe.
This avoids the Frobenius/cyclotomic hard-part machinery entirely while
provably answering the same boolean.

Denominator elimination is sound here because vertical-line evaluations at
the (untwisted) G2 argument land in the subfield `Fp6 ⊂ Fp12`
(`x_Q ∈ Fp2·w²` for the BN254 D-twist, `Fp2·w⁴` for the BLS12-381 M-twist,
both inside `Fp2[w²] ≅ Fp6`), and the final exponent is divisible by
`p⁶ - 1` (since `r | p⁴ - p² + 1 | p⁶ + 1`), which annihilates all of
`Fp6*`.

The field tower is `Fp2 = Fp[i]/(i² + 1)` and `Fp12 = Fp2[w]/(w⁶ - ξ)`
with `ξ = 9 + i` (BN254) or `ξ = 1 + i` (BLS12-381); G2 points on the
sextic twist untwist to sparse `Fp12` coordinates by coefficient
placement.

Everything is plain executable Lean over `Nat` — no `@[extern]`, no
axioms, no `sorry`. Byte-parity against ground truth (the go-ethereum
precompile known-answer vectors, cross-checked case-by-case against a
real EVM via `forge`, plus the in-repo evmyul/execution-specs reference
constants) is witnessed by `lake exe precompileParity`.
-/

namespace SolidCore.Solidity.Shared.Crypto

/-! ### The quadratic extension `Fp2 = Fp[i]/(i² + 1)`

Elements are pairs `(re, im)` with both coordinates kept reduced. Both
target fields have `p ≡ 3 (mod 4)`, so `x² + 1` is irreducible. -/

abbrev Fp2 := Nat × Nat

def f2zero : Fp2 := (0, 0)
def f2one : Fp2 := (1, 0)

def f2add (p : Nat) (a b : Fp2) : Fp2 :=
  ((a.1 + b.1) % p, (a.2 + b.2) % p)

def f2sub (p : Nat) (a b : Fp2) : Fp2 :=
  (subMod p a.1 b.1, subMod p a.2 b.2)

def f2mul (p : Nat) (a b : Fp2) : Fp2 :=
  (subMod p (a.1 * b.1) (a.2 * b.2), (a.1 * b.2 + a.2 * b.1) % p)

def f2neg (p : Nat) (a : Fp2) : Fp2 :=
  (subMod p 0 a.1, subMod p 0 a.2)

/-- Inverse via the conjugate over the norm (callers guarantee `a ≠ 0`). -/
def f2inv (p : Nat) (a : Fp2) : Fp2 :=
  let n := invMod p ((a.1 * a.1 + a.2 * a.2) % p)
  (a.1 * n % p, subMod p 0 a.2 * n % p)

/-! ### Short-Weierstrass curves `y² = x³ + b` over `Fp2` (twists) -/

abbrev Point2 := Option (Fp2 × Fp2)

def f2onCurve (p : Nat) (b x y : Fp2) : Bool :=
  f2mul p y y == f2add p (f2mul p (f2mul p x x) x) b

def point2Double (p : Nat) : Point2 → Point2
  | none => none
  | some (x, y) =>
      if y == f2zero then none
      else
        let lam :=
          f2mul p (f2mul p (3, 0) (f2mul p x x)) (f2inv p (f2mul p (2, 0) y))
        let x3 := f2sub p (f2mul p lam lam) (f2add p x x)
        some (x3, f2sub p (f2mul p lam (f2sub p x x3)) y)

def point2Add (p : Nat) : Point2 → Point2 → Point2
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
      if x1 == x2 then
        if f2add p y1 y2 == f2zero then none
        else point2Double p (some (x1, y1))
      else
        let lam := f2mul p (f2sub p y2 y1) (f2inv p (f2sub p x2 x1))
        let x3 := f2sub p (f2mul p lam lam) (f2add p x1 x2)
        some (x3, f2sub p (f2mul p lam (f2sub p x1 x3)) y1)

/-- Double-and-add scalar multiplication over `Fp2`, total by halving. -/
def point2Mul (p : Nat) (k : Nat) (pt : Point2) : Point2 :=
  if h : k = 0 then none
  else
    let rest := point2Mul p (k / 2) (point2Double p pt)
    if k % 2 == 1 then point2Add p rest pt else rest
termination_by k
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

/-! ### The dodecic extension `Fp12 = Fp2[w]/(w⁶ - ξ)`

Represented as the array of 6 `Fp2` coefficients of powers of `w`. -/

abbrev Fp12 := Array Fp2

def f12one : Fp12 := #[(1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]

/-- Schoolbook 6×6 multiplication with the reduction `w⁶ = ξ`. -/
def f12mul (p : Nat) (xi : Fp2) (a b : Fp12) : Fp12 := Id.run do
  let mut c : Array Fp2 := Array.mk (List.replicate 11 f2zero)
  for i in [0 : 6] do
    for j in [0 : 6] do
      c := c.set! (i + j) (f2add p c[i + j]! (f2mul p a[i]! b[j]!))
  let mut out : Array Fp2 := Array.mk (List.replicate 6 f2zero)
  for k in [0 : 6] do
    let hi := if k + 6 < 11 then c[k + 6]! else f2zero
    out := out.set! k (f2add p c[k]! (f2mul p xi hi))
  return out

def f12powAux (p : Nat) (xi : Fp2) (base : Fp12) (exp : Nat) (acc : Fp12) :
    Fp12 :=
  if h : exp = 0 then acc
  else
    let acc' := if exp % 2 == 1 then f12mul p xi acc base else acc
    f12powAux p xi (f12mul p xi base base) (exp / 2) acc'
termination_by exp
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

def f12pow (p : Nat) (xi : Fp2) (a : Fp12) (e : Nat) : Fp12 :=
  f12powAux p xi a e f12one

/-! ### The Miller loop (reduced Tate pairing core) -/

/-- Bits of `n`, most significant first (`[]` for `n = 0`). -/
def natBitsMSB (n : Nat) : List Bool :=
  if h : n = 0 then []
  else natBitsMSB (n / 2) ++ [n % 2 == 1]
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 2)

/-- The line through the G1 point `(tx, ty)` with slope `lam`, evaluated at
    the untwisted G2 point `(xQ, yQ) ∈ Fp12²`:
    `l(Q) = yQ - lam·xQ - (ty - lam·tx)`. -/
def lineAt (p : Nat) (lam tx ty : Nat) (xQ yQ : Fp12) : Fp12 := Id.run do
  let negLam := subMod p 0 lam
  let c := subMod p (lam * tx) ty
  let mut l : Array Fp2 := Array.mk (List.replicate 6 f2zero)
  for k in [0 : 6] do
    let q := xQ[k]!
    l := l.set! k (f2add p yQ[k]! (negLam * q.1 % p, negLam * q.2 % p))
  l := l.set! 0 (f2add p l[0]! (c, 0))
  return l

/-- One Miller iteration (double step, plus an add step when `bit`).
    Vertical lines are eliminated (they evaluate into `Fp6`, which the
    final exponentiation annihilates), so the degenerate branches
    contribute the factor 1. -/
def millerStep (p : Nat) (xi : Fp2) (P : Nat × Nat) (xQ yQ : Fp12)
    (state : Fp12 × Point) (bit : Bool) : Fp12 × Point :=
  let (f, T) := state
  let (f, T) :=
    match T with
    | none => (f12mul p xi f f, none)
    | some (tx, ty) =>
        if ty % p == 0 then (f12mul p xi f f, none)
        else
          let lam := 3 * tx % p * tx % p * invMod p (2 * ty % p) % p
          (f12mul p xi (f12mul p xi f f) (lineAt p lam tx ty xQ yQ),
           pointDouble p (some (tx, ty)))
  if bit then
    match T with
    | none => (f, some P)
    | some (tx, ty) =>
        if tx % p == P.1 % p then
          if (ty + P.2) % p == 0 then (f, none)
          else
            let lam := 3 * tx % p * tx % p * invMod p (2 * ty % p) % p
            (f12mul p xi f (lineAt p lam tx ty xQ yQ),
             pointDouble p (some (tx, ty)))
        else
          let lam := subMod p P.2 ty * invMod p (subMod p P.1 tx) % p
          (f12mul p xi f (lineAt p lam tx ty xQ yQ),
           pointAdd p (some (tx, ty)) (some P))
  else (f, T)

/-- The Miller function `f_{r,P}(Q)` (denominator-eliminated) for the G1
    point `P` (affine, reduced, non-infinity) evaluated at the untwisted
    G2 point `(xQ, yQ)`. -/
def millerTate (p : Nat) (xi : Fp2) (r : Nat) (P : Nat × Nat)
    (xQ yQ : Fp12) : Fp12 :=
  match natBitsMSB r with
  | [] => f12one
  | _ :: bits => (bits.foldl (millerStep p xi P xQ yQ) (f12one, some P)).1

/-! ### BN254 / alt_bn128 pairing check (`ecpairing`, precompile 0x8) -/

def bnR : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def bnXi : Fp2 := (9, 1)

/-- The D-twist curve constant `b' = 3 / ξ`. -/
def bnTwistB : Fp2 := f2mul bnP (3, 0) (f2inv bnP bnXi)

/-- The full final exponent `(p¹² - 1) / r` (exact division). -/
def bnFinalExpExponent : Nat := (bnP ^ 12 - 1) / bnR

/-- Untwist a BN254 G2 point (D-type): `(x', y') ↦ (x'·w², y'·w³)`. -/
def bnUntwist (Q : Fp2 × Fp2) : Fp12 × Fp12 :=
  (#[f2zero, f2zero, Q.1, f2zero, f2zero, f2zero],
   #[f2zero, f2zero, f2zero, Q.2, f2zero, f2zero])

/-- Fail-closed bound on the pair count. Real gas metering (34000·k +
    45000, EIP-1108) bounds mainnet-reachable pair counts far below this;
    the gas-free model refuses (`none` → open-world fail-closed) above it
    rather than model unbounded work. -/
def bnPairingPairsCap : Nat := 4096

/-- `ecpairing` (0x8, EIP-197): input is `k` 192-byte groups, each a G1
    point `(x, y)` followed by a G2 point `(x_c1, x_c0, y_c1, y_c0)`
    (imaginary coefficients first). `some (true, word)` with word 1 iff
    the pairing product is 1 (empty input → 1); `some (false, [])` is the
    precompile ERROR (length not a multiple of 192, a coordinate ≥ p, a
    point off its curve, or a G2 point outside the r-order subgroup —
    G1 needs no subgroup check: the curve has cofactor 1); `none` only
    above `bnPairingPairsCap`. Semantics mirrors the evmyul/
    execution-specs `snarkv` reference and is byte-parity-checked against
    the go-ethereum vector suite. -/
def bnPairingBytes? (input : Bytes) : Option (Bool × Bytes) :=
  if input.length % 192 != 0 then some (false, [])
  else if bnPairingPairsCap * 192 < input.length then none
  else
    let step : Option Fp12 → Nat → Option Fp12 := fun acc? i =>
      match acc? with
      | none => none
      | some acc =>
          let v := fun (j : Nat) =>
            bytesToNatBE (sliceZeroPadded input (192 * i + 32 * j) 32)
          let x1 := v 0
          let y1 := v 1
          let xi2 := v 2
          let xr2 := v 3
          let yi2 := v 4
          let yr2 := v 5
          if bnP <= x1 || bnP <= y1 || bnP <= xi2 || bnP <= xr2 ||
              bnP <= yi2 || bnP <= yr2 then
            none
          else
            let g1Inf := x1 == 0 && y1 == 0
            let x2 : Fp2 := (xr2, xi2)
            let y2 : Fp2 := (yr2, yi2)
            let g2Inf := x2 == f2zero && y2 == f2zero
            if !g1Inf && !onCurve bnP 3 x1 y1 then none
            else if !g2Inf &&
                (!f2onCurve bnP bnTwistB x2 y2 ||
                  !(point2Mul bnP bnR (some (x2, y2))).isNone) then none
            else if g1Inf || g2Inf then some acc
            else
              let (xQ, yQ) := bnUntwist (x2, y2)
              some (f12mul bnP bnXi acc
                (millerTate bnP bnXi bnR (x1, y1) xQ yQ))
    match (List.range (input.length / 192)).foldl step (some f12one) with
    | none => some (false, [])
    | some acc =>
        let one := f12pow bnP bnXi acc bnFinalExpExponent == f12one
        some (true, natToBytesBE 32 (if one then 1 else 0))

/-! ### BLS12-381 KZG point evaluation (precompile 0xa, EIP-4844) -/

def blsP : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The BLS12-381 scalar field order (`BLS_MODULUS` of EIP-4844). -/
def blsR : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def blsXi : Fp2 := (1, 1)

/-- The M-twist curve constant `b' = 4·ξ = 4 + 4i`. -/
def blsTwistB : Fp2 := (4, 4)

/-- The full final exponent `(p¹² - 1) / r` (exact division). -/
def blsFinalExpExponent : Nat := (blsP ^ 12 - 1) / blsR

def blsG1 : Nat × Nat :=
  (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

def blsG2 : Fp2 × Fp2 :=
  ((0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
    0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e),
   (0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
    0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be))

/-- `[τ]G2` from the EIP-4844 KZG ceremony (`KZG_SETUP_G2_MONOMIAL_1`),
    decompressed to affine coordinates. Provenance: the parity executable
    re-compresses this point and checks the bytes against the canonical
    compressed constant (the one carried by the pinned evmyul
    execution-specs KZG reference), plus on-twist-curve and r-subgroup
    membership. -/
def kzgTauG2 : Fp2 × Fp2 :=
  ((0x185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2,
    0x15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72),
   (0x014353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99,
    0x1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f))

/-- Untwist a BLS12-381 G2 point (M-type):
    `(x', y') ↦ ((x'/ξ)·w⁴, (y'/ξ)·w³)`. -/
def blsUntwist (Q : Fp2 × Fp2) : Fp12 × Fp12 :=
  let xiInv := f2inv blsP blsXi
  (#[f2zero, f2zero, f2zero, f2zero, f2mul blsP Q.1 xiInv, f2zero],
   #[f2zero, f2zero, f2zero, f2mul blsP Q.2 xiInv, f2zero, f2zero])

/-- Decompress a 48-byte BLS12-381 G1 point (ZCash/EIP-2333 encoding) with
    EXACTLY the EIP-4844 `validate_kzg_g1` acceptance: compression flag
    set; the canonical infinity encoding `0xc0 ‖ 0⁴⁷` (and only it) is
    infinity; otherwise `x < p`, `x³ + 4` a square (`p ≡ 3 mod 4`, so the
    root is `pow (p+1)/4`), the sign chosen by the sort flag, and the
    point in the r-order subgroup. `none` is rejection. -/
def blsDecompressG1? (bytes : Bytes) : Option Point :=
  let z := bytesToNatBE bytes
  let cFlag := z / 2 ^ 383 % 2
  let bFlag := z / 2 ^ 382 % 2
  let aFlag := z / 2 ^ 381 % 2
  let x := z % 2 ^ 381
  if cFlag != 1 then none
  else if bFlag == 1 then
    if aFlag == 0 && x == 0 then some none else none
  else if blsP <= x then none
  else
    let ySq := (x * x % blsP * x + 4) % blsP
    let y0 := powMod blsP ySq ((blsP + 1) / 4)
    if y0 * y0 % blsP != ySq then none
    else
      let y := if 2 * y0 / blsP == aFlag then y0 else (blsP - y0) % blsP
      if (pointMul blsP blsR (some (x, y))).isNone then some (some (x, y))
      else none

/-- The fixed 64-byte success payload:
    `FIELD_ELEMENTS_PER_BLOB (4096) ‖ BLS_MODULUS`. -/
def kzgOutput : Bytes :=
  natToBytesBE 32 4096 ++ natToBytesBE 32 blsR

/-- One Miller factor `f_{r,P}(Q)` over BLS12-381; infinity on either side
    contributes 1. -/
def blsMillerFactor (P : Point) (Q : Point2) : Fp12 :=
  match P, Q with
  | some P, some Q =>
      let (xQ, yQ) := blsUntwist Q
      millerTate blsP blsXi blsR P xQ yQ
  | _, _ => f12one

/-- `pointEvaluation` (0xa, EIP-4844): input is exactly
    `versioned_hash(32) ‖ z(32) ‖ y(32) ‖ commitment(48) ‖ proof(48)`.
    Verifies `versioned_hash = 0x01 ‖ sha256(commitment)[1:]`, that
    `z, y < BLS_MODULUS`, that commitment and proof decompress to valid
    subgroup points, and the KZG relation
    `e(commitment - [y]₁, -[1]₂) · e(proof, [τ]₂ - [z]₂) = 1`.
    Success returns the fixed 64-byte payload; any failure is the
    precompile ERROR `some (false, [])`. -/
def kzgPointEvalBytes? (input : Bytes) : Option (Bool × Bytes) :=
  if input.length != 192 then some (false, [])
  else
    let vh := input.take 32
    let z := bytesToNatBE (sliceZeroPadded input 32 32)
    let y := bytesToNatBE (sliceZeroPadded input 64 32)
    let cb := (input.drop 96).take 48
    let pb := (input.drop 144).take 48
    if (1 :: (sha256Bytes cb).drop 1) != vh then some (false, [])
    else if blsR <= z || blsR <= y then some (false, [])
    else
      match blsDecompressG1? cb, blsDecompressG1? pb with
      | some c, some q =>
          let xMinusZ :=
            point2Add blsP (some kzgTauG2)
              (point2Mul blsP ((blsR - z) % blsR) (some blsG2))
          let pMinusY :=
            pointAdd blsP c
              (pointMul blsP ((blsR - y) % blsR) (some blsG1))
          let negG2 : Point2 := some (blsG2.1, f2neg blsP blsG2.2)
          let acc :=
            f12mul blsP blsXi (blsMillerFactor pMinusY negG2)
              (blsMillerFactor q xMinusZ)
          if f12pow blsP blsXi acc blsFinalExpExponent == f12one then
            some (true, kzgOutput)
          else
            some (false, [])
      | _, _ => some (false, [])

end SolidCore.Solidity.Shared.Crypto

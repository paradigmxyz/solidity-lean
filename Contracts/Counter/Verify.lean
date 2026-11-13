import Verify.Final
import Verify.Abi

/-!
# solar-verify's Counter: its specification and what certifies it

The contract is `crates/verify/examples/Counter.sol` of solar (branch `alpharush/verify`),
compiled by solar at 3a044a9d (`alpharush/tv-backend-stages`) with `-Ogas --evm-version osaka`
to 496 bytes of runtime bytecode (`manifest`, `code`; `bound` checks the hex and the SHA-256 in
the kernel). Its NatSpec, read as `Final.ContractSpec` over the abstract state `(count, limit)`
that slots 0 and 1 hold:

* `@custom:invariant count <= limit`;
* `increment()`: requires `count < limit`, ensures `count == old(count) + 1`;
* `bump(uint256 n)`: ensures `count == old(count) + n` (its loop's invariants and variant are
  the proof's, not the contract's);
* `max(uint256 a, uint256 b)`: ensures `result == (a >= b ? a : b)`, `result >= a` and
  `result >= b`;
* the getters `count()` and `limit()` have no specification but the invariants;
* nothing is payable.

The constructor's `@custom:ensures limit == _limit && count == 0` is about deployment, which
`Final` does not cover; it is what makes the invariant hold of the first storage.

`bump(n)` runs its loop `n` times, so its gas grows with `n` and SolidCore needs fuel that grows
with `n`: no fixed gas limit or fuel finishes every call. The statement is therefore
`Final.compose_anyGas`'s, against SolidCore with as much fuel as a call needs (`solidCoreAny`)
and at every gas: every result of the bytecode is SolidCore's or a failure that changes nothing,
and the specification holds at every gas. `certified_of_stages` gives it from the stages, each a
hypothesis named after its obligation. None of them is proved yet: the generic source stage,
solar-tv's backend stages and the assembly stage handle loop-free programs only.

The specification is not met trivially (`satisfiable`: every function has a state that meets the
invariant and its precondition; `ensures_rejects`: each postcondition rejects some result), and
the code runs in one frame (`frameLocal`), so no other contract can run during a call.
-/

namespace SolidCore.Refinement.Solar.VerifyCounter

open SolidCore.Refinement SolidCore.Refinement.Final

/-- The abstract state: `count` (slot 0) and `limit` (slot 1). -/
structure State where
  count : Nat
  limit : Nat

/-- The storage layout. -/
def layout (s : Nat → Nat) : State := ⟨s 0, s 1⟩

/-- The ABI return data of one word. -/
def returns (out : List Nat) (r : Nat) : Prop := out = SolidCore.Verify.word r

def countSpec : FnSpec State where
  name := "count"
  sel := 0x06661abd
  params := []
  requires _ _ := True
  ensures _ _ _ _ := True
  payable := false

def limitSpec : FnSpec State where
  name := "limit"
  sel := 0xa4d66daf
  params := []
  requires _ _ := True
  ensures _ _ _ _ := True
  payable := false

/-- `@custom:requires count < limit`, `@custom:ensures count == old(count) + 1`. -/
def incrementSpec : FnSpec State where
  name := "increment"
  sel := 0xd09de08a
  params := []
  requires _ s := s.count < s.limit
  ensures _ s s' _ := s'.count = s.count + 1
  payable := false

/-- `@custom:ensures count == old(count) + n`. -/
def bumpSpec : FnSpec State where
  name := "bump"
  sel := 0xb20eb4c4
  params := [.uint 256]
  requires _ _ := True
  ensures args s s' _ := s'.count = s.count + args.headD 0
  payable := false

/-- `@custom:ensures result == (a >= b ? a : b)`, `result >= a && result >= b`. -/
def maxSpec : FnSpec State where
  name := "max"
  sel := 0x6d5433e6
  params := [.uint 256, .uint 256]
  requires _ _ := True
  ensures args _ _ out :=
    let a := args.getD 0 0
    let b := args.getD 1 0
    ∃ r, returns out r ∧ r = (if a ≥ b then a else b) ∧ r ≥ a ∧ r ≥ b
  payable := false

/-- Counter's specification. -/
def spec : ContractSpec State where
  abs := layout
  invariant s := s.count ≤ s.limit
  fns := [countSpec, limitSpec, incrementSpec, bumpSpec, maxSpec]

/-! ## The bytecode and its manifest -/

def manifest : Manifest where
  contract := "Counter"
  sourceSha256 := "f1c87a334b8db31fc8f80541febeaf8617318d20b685634f44e26c74146ad326"
  compilerCommit := "0.8.38+commit.3a044a9d.solar.0.3.0-dev"
  options := ["-Ogas", "--evm-version", "osaka"]
  runtimeHex :=
    "34603c575f3560e01c806306661abd1460525780636d5433e6146101af578063a4d66daf14605b578063b20eb4c4146073578063d09de08a146065575b5f5ffd5b6011602052634e487b715f526024601cfd5b5f545f5260205ff35b6001545f5260205ff35b5f5460010180156040575f55005b60243610603c576004355f54818101818110604057600154106101d25780816080525f60a0528082820361019a575f5f91925060db565b506080516001840180158583036101675760405780608052600160a05260018301925f191480610182575093505060015b8482105f54808503610111575060aa5760a051815f10828203610152571561010f5750505050608051815f5581810361013e575b005b90506d011100000004000000010000000f939091935b60205260405260605263ed572b275b5f526064601cfd5b6d012100000004000000050000000e610127565b506d012100000004000000040000000c610127565b505090506d0121000000040000000300000008929192610127565b5f6d0102000000040000000a00000012919091610127565b506d010300000004000000070000000b610127565b60443610603c576004356024358082106101cb57505f5260205ff35b5f5260205ff35b636f76657260e01b6004602080526040526060526308c379a061013656"
  runtimeSha256 := "d74a847b897f855f93daf2805937efe40aec636c2ec3ca0c2d4ca6d21f214cc1"

/-- The runtime bytecode as one number, most significant byte first, as the milestones write
it: the kernel computes with it by GMP, where parsing the hex string would cost it minutes. -/
def runtimeNat : Nat := 0x34603c575f3560e01c806306661abd1460525780636d5433e6146101af578063a4d66daf14605b578063b20eb4c4146073578063d09de08a146065575b5f5ffd5b6011602052634e487b715f526024601cfd5b5f545f5260205ff35b6001545f5260205ff35b5f5460010180156040575f55005b60243610603c576004355f54818101818110604057600154106101d25780816080525f60a0528082820361019a575f5f91925060db565b506080516001840180158583036101675760405780608052600160a05260018301925f191480610182575093505060015b8482105f54808503610111575060aa5760a051815f10828203610152571561010f5750505050608051815f5581810361013e575b005b90506d011100000004000000010000000f939091935b60205260405260605263ed572b275b5f526064601cfd5b6d012100000004000000050000000e610127565b506d012100000004000000040000000c610127565b505090506d0121000000040000000300000008929192610127565b5f6d0102000000040000000a00000012919091610127565b506d010300000004000000070000000b610127565b60443610603c576004356024358082106101cb57505f5260205ff35b5f5260205ff35b636f76657260e01b6004602080526040526060526308c379a061013656

/-- The runtime bytecode. `bound` checks it against the manifest's hex and SHA-256. -/
def code : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat runtimeNat 496

/-! ## The bytecode is the manifest's

The kernel reads `code` (an `Array.ofFn`) and the manifest's strings slowly: deciding the
SHA-256 of 496 bytes directly runs out of memory. So the checks go through forms the kernel
computes with cheaply, each proved equal to the original: `code` as a list (`code_eq`), the hex
of bytes as a list of characters, compared with the manifest's string character by character
(`hexOf_eq`), the padded message as a list (`pad_code`), and the hash block by block through
the hash values between blocks (`block0` to `block7`). Those values and the padded bytes were
computed outside Lean; the kernel checks each, so a wrong one fails the proof. -/

/-- The lowest `k` bytes of `n`, most significant first. -/
def natBytes (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n >>> (8 * k)) :: natBytes n k

/-- `code` as a list of bytes. -/
def code' : ByteArray := ⟨⟨natBytes runtimeNat 496⟩⟩

/-- A hex digit, as `hexOf` writes it. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The characters `hexOf` writes. -/
def hexChars : List Nat → List Char
  | [] => []
  | b :: rest => hexDigit (b / 16 % 16) :: hexDigit (b % 16) :: hexChars rest

open EthLib.Cryptography.Hash

/-- The padded runtime bytecode, FIPS 180-4 §5.1.1, byte by byte. -/
def padded : List UInt8 := [
  0x34, 0x60, 0x3c, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x06, 0x66, 0x1a, 0xbd, 0x14,
  0x60, 0x52, 0x57, 0x80, 0x63, 0x6d, 0x54, 0x33, 0xe6, 0x14, 0x61, 0x01, 0xaf, 0x57, 0x80, 0x63,
  0xa4, 0xd6, 0x6d, 0xaf, 0x14, 0x60, 0x5b, 0x57, 0x80, 0x63, 0xb2, 0x0e, 0xb4, 0xc4, 0x14, 0x60,
  0x73, 0x57, 0x80, 0x63, 0xd0, 0x9d, 0xe0, 0x8a, 0x14, 0x60, 0x65, 0x57, 0x5b, 0x5f, 0x5f, 0xfd,
  0x5b, 0x60, 0x11, 0x60, 0x20, 0x52, 0x63, 0x4e, 0x48, 0x7b, 0x71, 0x5f, 0x52, 0x60, 0x24, 0x60,
  0x1c, 0xfd, 0x5b, 0x5f, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x60, 0x01, 0x54, 0x5f,
  0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x5f, 0x54, 0x60, 0x01, 0x01, 0x80, 0x15, 0x60, 0x40, 0x57,
  0x5f, 0x55, 0x00, 0x5b, 0x60, 0x24, 0x36, 0x10, 0x60, 0x3c, 0x57, 0x60, 0x04, 0x35, 0x5f, 0x54,
  0x81, 0x81, 0x01, 0x81, 0x81, 0x10, 0x60, 0x40, 0x57, 0x60, 0x01, 0x54, 0x10, 0x61, 0x01, 0xd2,
  0x57, 0x80, 0x81, 0x60, 0x80, 0x52, 0x5f, 0x60, 0xa0, 0x52, 0x80, 0x82, 0x82, 0x03, 0x61, 0x01,
  0x9a, 0x57, 0x5f, 0x5f, 0x91, 0x92, 0x50, 0x60, 0xdb, 0x56, 0x5b, 0x50, 0x60, 0x80, 0x51, 0x60,
  0x01, 0x84, 0x01, 0x80, 0x15, 0x85, 0x83, 0x03, 0x61, 0x01, 0x67, 0x57, 0x60, 0x40, 0x57, 0x80,
  0x60, 0x80, 0x52, 0x60, 0x01, 0x60, 0xa0, 0x52, 0x60, 0x01, 0x83, 0x01, 0x92, 0x5f, 0x19, 0x14,
  0x80, 0x61, 0x01, 0x82, 0x57, 0x50, 0x93, 0x50, 0x50, 0x60, 0x01, 0x5b, 0x84, 0x82, 0x10, 0x5f,
  0x54, 0x80, 0x85, 0x03, 0x61, 0x01, 0x11, 0x57, 0x50, 0x60, 0xaa, 0x57, 0x60, 0xa0, 0x51, 0x81,
  0x5f, 0x10, 0x82, 0x82, 0x03, 0x61, 0x01, 0x52, 0x57, 0x15, 0x61, 0x01, 0x0f, 0x57, 0x50, 0x50,
  0x50, 0x50, 0x60, 0x80, 0x51, 0x81, 0x5f, 0x55, 0x81, 0x81, 0x03, 0x61, 0x01, 0x3e, 0x57, 0x5b,
  0x00, 0x5b, 0x90, 0x50, 0x6d, 0x01, 0x11, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x01, 0x00,
  0x00, 0x00, 0x0f, 0x93, 0x90, 0x91, 0x93, 0x5b, 0x60, 0x20, 0x52, 0x60, 0x40, 0x52, 0x60, 0x60,
  0x52, 0x63, 0xed, 0x57, 0x2b, 0x27, 0x5b, 0x5f, 0x52, 0x60, 0x64, 0x60, 0x1c, 0xfd, 0x5b, 0x6d,
  0x01, 0x21, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x0e, 0x61, 0x01,
  0x27, 0x56, 0x5b, 0x50, 0x6d, 0x01, 0x21, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x00,
  0x00, 0x00, 0x0c, 0x61, 0x01, 0x27, 0x56, 0x5b, 0x50, 0x50, 0x90, 0x50, 0x6d, 0x01, 0x21, 0x00,
  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x08, 0x92, 0x91, 0x92, 0x61, 0x01,
  0x27, 0x56, 0x5b, 0x5f, 0x6d, 0x01, 0x02, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x0a, 0x00,
  0x00, 0x00, 0x12, 0x91, 0x90, 0x91, 0x61, 0x01, 0x27, 0x56, 0x5b, 0x50, 0x6d, 0x01, 0x03, 0x00,
  0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x0b, 0x61, 0x01, 0x27, 0x56, 0x5b,
  0x60, 0x44, 0x36, 0x10, 0x60, 0x3c, 0x57, 0x60, 0x04, 0x35, 0x60, 0x24, 0x35, 0x80, 0x82, 0x10,
  0x61, 0x01, 0xcb, 0x57, 0x50, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x5f, 0x52, 0x60, 0x20,
  0x5f, 0xf3, 0x5b, 0x63, 0x6f, 0x76, 0x65, 0x72, 0x60, 0xe0, 0x1b, 0x60, 0x04, 0x60, 0x20, 0x80,
  0x52, 0x60, 0x40, 0x52, 0x60, 0x60, 0x52, 0x63, 0x08, 0xc3, 0x79, 0xa0, 0x61, 0x01, 0x36, 0x56,
  0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x80]
/-- The hash value after 0 blocks. -/
def h0 : Sha256.State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩
/-- The hash value after 1 block. -/
def h1 : Sha256.State :=
  ⟨0xb2cdf007, 0xd0774cd6, 0xc0d18d33, 0x621e4545, 0x93fcd02d, 0x249721ff, 0xe4c7abfd, 0x9f6bed4f⟩
/-- The hash value after 2 blocks. -/
def h2 : Sha256.State :=
  ⟨0x8e1df3fe, 0x4d88a0fe, 0x3e78a777, 0xbb94b703, 0x0ab41627, 0x41e55e5a, 0xca25c8cb, 0x7543420f⟩
/-- The hash value after 3 blocks. -/
def h3 : Sha256.State :=
  ⟨0xcee21dfe, 0x0d9d89b5, 0x1e415593, 0xe71326a4, 0x9ebd6694, 0x90e15196, 0x09a11887, 0xf68fe034⟩
/-- The hash value after 4 blocks. -/
def h4 : Sha256.State :=
  ⟨0xe2dce301, 0x1bd38318, 0x4df49c6e, 0x869385f9, 0x06f59255, 0xa7187d72, 0x6a6af0a5, 0x6bebdc66⟩
/-- The hash value after 5 blocks. -/
def h5 : Sha256.State :=
  ⟨0x6aecb6ac, 0x059b35a9, 0x130454c0, 0x1aee959f, 0x52075dac, 0xb403e20b, 0x54889c4a, 0x7d1b2c51⟩
/-- The hash value after 6 blocks. -/
def h6 : Sha256.State :=
  ⟨0xb70e2627, 0x7e35bded, 0xa5d6b60a, 0x8452ca01, 0x2b374755, 0x139e3c51, 0xf0344fbe, 0xc15849d2⟩
/-- The hash value after 7 blocks. -/
def h7 : Sha256.State :=
  ⟨0x8d0c0858, 0x3afc1adf, 0x18d221be, 0xfd0d4bed, 0xada2d3ff, 0xe9e30dc6, 0xa9436abe, 0x3ca3a468⟩
/-- The hash value after 8 blocks. -/
def h8 : Sha256.State :=
  ⟨0xd74a847b, 0x897f855f, 0x93daf280, 0x5937efe4, 0x0aec636c, 0x2ec3ca0c, 0x2d4ca6d2, 0x1f214cc1⟩

theorem length_natBytes (n k : Nat) : (natBytes n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natBytes, ih]

theorem getElem_natBytes (n k i : Nat) (h : i < (natBytes n k).length) :
    (natBytes n k)[i] = EthLib.Execution.Evm.Logic.NatCode.natByte n k i := by
  induction k generalizing i with
  | zero => simp [natBytes] at h
  | succ k ih =>
    have hk : i < k + 1 := by simpa [length_natBytes] using h
    cases i with
    | zero => simp [natBytes, EthLib.Execution.Evm.Logic.NatCode.natByte]
    | succ i =>
      have hi : i < (natBytes n k).length := by rw [length_natBytes]; omega
      simp only [natBytes, List.getElem_cons_succ]
      rw [ih i hi]
      simp only [EthLib.Execution.Evm.Logic.NatCode.natByte]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      congr 3
      omega

theorem ofNat_eq (n k : Nat) :
    EthLib.Execution.Evm.Logic.NatCode.ofNat n k = ⟨⟨natBytes n k⟩⟩ := by
  unfold EthLib.Execution.Evm.Logic.NatCode.ofNat
  congr 1
  apply Array.ext
  · simp [length_natBytes]
  · intro i h1 h2
    simp only [Array.getElem_ofFn]
    exact (getElem_natBytes n k i (by simpa using h2)).symm

theorem code_eq : code = code' := ofNat_eq _ _

theorem hexOf_eq (l : List Nat) : hexOf l = String.ofList (hexChars l) := by
  induction l with
  | nil => simp [hexOf, hexChars]
  | cons b rest ih =>
    simp only [hexOf, List.map_cons, String.join_cons] at ih ⊢
    rw [ih, hexChars, ← String.ofList_append]
    rfl

def paddedBytes : ByteArray := ⟨⟨padded⟩⟩

theorem pad_code : Sha256.pad code = paddedBytes := by
  have h : (Sha256.pad code').data.toList = padded := by decide +kernel
  rw [code_eq]
  exact ByteArray.ext (Array.ext' h)

theorem state_eq {r s : Sha256.State} (ha : r.a = s.a) (hb : r.b = s.b) (hc : r.c = s.c)
    (hd : r.d = s.d) (he : r.e = s.e) (hf : r.f = s.f) (hg : r.g = s.g) (hh : r.h = s.h) :
    r = s := by
  cases r; cases s; simp_all

theorem block0 (h) : Sha256.compress h0 paddedBytes 0 h = h1 :=
  have fields : let r := Sha256.compress h0 paddedBytes 0 (by decide +kernel)
      r.a = h1.a ∧ r.b = h1.b ∧ r.c = h1.c ∧ r.d = h1.d ∧ r.e = h1.e ∧
        r.f = h1.f ∧ r.g = h1.g ∧ r.h = h1.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block1 (h) : Sha256.compress h1 paddedBytes 64 h = h2 :=
  have fields : let r := Sha256.compress h1 paddedBytes 64 (by decide +kernel)
      r.a = h2.a ∧ r.b = h2.b ∧ r.c = h2.c ∧ r.d = h2.d ∧ r.e = h2.e ∧
        r.f = h2.f ∧ r.g = h2.g ∧ r.h = h2.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block2 (h) : Sha256.compress h2 paddedBytes 128 h = h3 :=
  have fields : let r := Sha256.compress h2 paddedBytes 128 (by decide +kernel)
      r.a = h3.a ∧ r.b = h3.b ∧ r.c = h3.c ∧ r.d = h3.d ∧ r.e = h3.e ∧
        r.f = h3.f ∧ r.g = h3.g ∧ r.h = h3.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block3 (h) : Sha256.compress h3 paddedBytes 192 h = h4 :=
  have fields : let r := Sha256.compress h3 paddedBytes 192 (by decide +kernel)
      r.a = h4.a ∧ r.b = h4.b ∧ r.c = h4.c ∧ r.d = h4.d ∧ r.e = h4.e ∧
        r.f = h4.f ∧ r.g = h4.g ∧ r.h = h4.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block4 (h) : Sha256.compress h4 paddedBytes 256 h = h5 :=
  have fields : let r := Sha256.compress h4 paddedBytes 256 (by decide +kernel)
      r.a = h5.a ∧ r.b = h5.b ∧ r.c = h5.c ∧ r.d = h5.d ∧ r.e = h5.e ∧
        r.f = h5.f ∧ r.g = h5.g ∧ r.h = h5.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block5 (h) : Sha256.compress h5 paddedBytes 320 h = h6 :=
  have fields : let r := Sha256.compress h5 paddedBytes 320 (by decide +kernel)
      r.a = h6.a ∧ r.b = h6.b ∧ r.c = h6.c ∧ r.d = h6.d ∧ r.e = h6.e ∧
        r.f = h6.f ∧ r.g = h6.g ∧ r.h = h6.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block6 (h) : Sha256.compress h6 paddedBytes 384 h = h7 :=
  have fields : let r := Sha256.compress h6 paddedBytes 384 (by decide +kernel)
      r.a = h7.a ∧ r.b = h7.b ∧ r.c = h7.c ∧ r.d = h7.d ∧ r.e = h7.e ∧
        r.f = h7.f ∧ r.g = h7.g ∧ r.h = h7.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem block7 (h) : Sha256.compress h7 paddedBytes 448 h = h8 :=
  have fields : let r := Sha256.compress h7 paddedBytes 448 (by decide +kernel)
      r.a = h8.a ∧ r.b = h8.b ∧ r.c = h8.c ∧ r.d = h8.d ∧ r.e = h8.e ∧
        r.f = h8.f ∧ r.g = h8.g ∧ r.h = h8.h := by
    decide +kernel
  let ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := fields
  state_eq ha hb hc hd he hf hg hh

theorem chain_succ (step : Sha256.State → (bytes : ByteArray) → (start : Nat) →
      start + 64 ≤ bytes.size → Sha256.State) (bytes : ByteArray) (count start : Nat) (whole) (s) :
    Sha256.chain step bytes (count + 1) start whole s =
      Sha256.chain step bytes count (start + 64) (by omega) (step s bytes start (by omega)) := rfl

theorem chain_eq (h) : Sha256.chain Sha256.compress paddedBytes 8 0 h h0 = h8 := by
  rw [chain_succ, block0, chain_succ, block1, chain_succ, block2, chain_succ, block3, chain_succ,
    block4, chain_succ, block5, chain_succ, block6, chain_succ, block7]
  rfl

theorem size_padded : paddedBytes.size / 64 = 8 := by decide +kernel

theorem hash_eq_of_pad {m p : ByteArray} {c : Nat} (hp : Sha256.pad m = p) (hc : p.size / 64 = c) :
    Sha256.hash m = Sha256.digest (Sha256.chain Sha256.compress p c 0
      (by have := Nat.mul_div_le p.size 64; omega) Sha256.initial) := by
  subst hp; subst hc; rfl

set_option maxRecDepth 100000 in
theorem sha_bound :
    hexOf ((Sha256.hash code).data.toList.map (·.toNat)) = manifest.runtimeSha256 := by
  rw [hash_eq_of_pad pad_code size_padded, show Sha256.initial = h0 from rfl, chain_eq, hexOf_eq]
  rfl

set_option maxRecDepth 200000 in
theorem hex_bound : hexOf (code.data.toList.map (·.toNat)) = manifest.runtimeHex := by
  rw [code_eq, hexOf_eq]
  rfl

theorem size_code : code.size = 496 := by
  rw [code_eq]; decide +kernel

/-- No instruction of the code runs other code or reads outside its frame. -/
theorem frameLocal : FrameLocal code = true := by
  rw [code_eq]; decide +kernel

theorem bound : Bound manifest code := ⟨hex_bound, sha_bound⟩


/-! ## The specification is not trivial -/

/-- Every function has argument words and a state that meet the invariant and its
precondition. -/
theorem satisfiable : ∀ f ∈ spec.fns, ∃ args st, f.Typed args ∧ spec.invariant st ∧ f.requires args st := by
  intro f hf
  simp only [spec, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact ⟨[], ⟨0, 0⟩, List.Forall₂.nil, Nat.le_refl _, trivial⟩
  · exact ⟨[], ⟨0, 0⟩, List.Forall₂.nil, Nat.le_refl _, trivial⟩
  · exact ⟨[], ⟨0, 1⟩, List.Forall₂.nil, Nat.zero_le 1, Nat.zero_lt_one⟩
  · exact ⟨[0], ⟨0, 0⟩, List.Forall₂.cons (by decide) List.Forall₂.nil, Nat.le_refl _, trivial⟩
  · exact ⟨[0, 0], ⟨0, 0⟩, List.Forall₂.cons (by decide) (List.Forall₂.cons (by decide)
      List.Forall₂.nil), Nat.le_refl _, trivial⟩

/-- The postconditions of `increment`, `bump` and `max` each reject some result. -/
theorem ensures_rejects :
    ¬ incrementSpec.ensures [] ⟨0, 1⟩ ⟨0, 1⟩ [] ∧ ¬ bumpSpec.ensures [1] ⟨0, 1⟩ ⟨0, 1⟩ [] ∧
      ¬ maxSpec.ensures [1, 2] ⟨0, 0⟩ ⟨0, 0⟩ (SolidCore.Verify.word 1) := by
  refine ⟨by simp [incrementSpec], by simp [bumpSpec], ?_⟩
  rintro ⟨r, hret, hr, -⟩
  have h2 : r = 2 := by simpa using hr
  subst h2
  exact absurd hret (by unfold returns; decide +kernel)

/-! ## The certificate from its stages -/

/-- **solar-verify's Counter from its stages.** SolidCore's checked contract `c`, which meets the
specification and finishes every call of it with enough fuel, a stage from SolidCore to a lowered
MIR program, the backend's stage to an EVM IR program, and an assembly stage that gives at every
gas the EVM IR's result or a failure, give at every gas: every result of the bytecode is
SolidCore's or a failure that changes nothing, and the specification holds of the bytecode. -/
theorem certified_of_stages {mirSem evmirSem : Sem}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog} {evmir : evmirSem.Prog}
    (source : Holds solidCoreAny c spec)
    (fin : ∀ call, spec.Calls call → (solidCoreAny.run c call).isSome)
    (lowering : Stage solidCoreAny mirSem c mir spec.Calls)
    (backend : Stage mirSem evmirSem mir evmir spec.Calls)
    (assembly : ∀ gas, Within evmirSem (ethLibWith gas) evmir code spec.Calls) (gas : Nat) :
    Within solidCoreAny (ethLibWith gas) c code spec.Calls ∧ Holds (ethLibWith gas) code spec :=
  compose_anyGas source fin lowering backend assembly gas

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bound

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.certified_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified_of_stages

end SolidCore.Refinement.Solar.VerifyCounter

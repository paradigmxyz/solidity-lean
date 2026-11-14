import Verify.Final
import Verify.Abi

/-!
# solar-verify's Counter: its specification and what certifies it

The contract is `crates/verify/examples/Counter.sol` of solar (branch `alpharush/verify`),
compiled by solar at 3a044a9d (`alpharush/tv-backend-stages`) with `-Ogas --evm-version osaka`
to 496 bytes of runtime bytecode (`manifest`, `code`; `bound` checks the hex in
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

/-- The runtime bytecode. `bound` checks it against the manifest's hex. -/
def code : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat runtimeNat 496

/-! ## The bytecode is the manifest's

The kernel reads `code` (an `Array.ofFn`) and the manifest's strings slowly, so the check goes
through forms the kernel computes with cheaply, each proved equal to the original: `code` as a
list (`code_eq`) and the hex of bytes as a list of characters, compared with the manifest's
string character by character (`hexOf_eq`). Exact equality with the manifest's hex binds the
bytes; the manifest's SHA-256 is recorded data, not checked in the kernel. -/

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

set_option maxRecDepth 200000 in
theorem hex_bound : hexOf (code.data.toList.map (·.toNat)) = manifest.runtimeHex := by
  rw [code_eq, hexOf_eq]
  rfl

theorem size_code : code.size = 496 := by
  rw [code_eq]; decide +kernel

/-- No instruction of the code runs other code or reads outside its frame. -/
theorem frameLocal : FrameLocal code = true := by
  rw [code_eq]; decide +kernel

theorem bound : Bound manifest code := hex_bound


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

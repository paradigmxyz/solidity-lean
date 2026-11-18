import Verify.Lifecycle.Examples
import Verify.Lifecycle.Deploy.Ctors
import Verify.Generic.CtorArgs.Uint8Ctor
import SolidCore.Refinement.Generic.Statement

/-!
# Gates for typed constructor admission

Each gate is one kernel evaluation (`kernel_rfl`, with the Lifecycle examples' selector table and
bucket index) of `admitCtor?` on a checked fixture and solar's init code for it
(Verify/Lifecycle/Deploy/Ctors), or a theorem. None of these names exists before typed admission,
so this module fails to elaborate at 074be897 and passes after it.

Fixtures: `PairCtor` (`constructor(uint256 a, uint256 b)`, the admitted subset), `ArgCtor`
(`uint256`, `address`) and `Uint8Ctor` (`uint8`, Uint8Ctor.sol here), both outside it.

Which layer refuses a malformed creation suffix: one shorter than the parameters' heads is refused
by SolidCore's decoder (`decShort`) and by the exact suffix (`pairShort`); trailing bytes,
aligned (`pairTrailing`) or misaligned (`pairMisaligned`), pass the decoder (`decTrailing`,
`decMisaligned`), as solc's does, and are refused by the exact suffix alone.
-/

namespace Verify.Generic.CtorArgs.Admission

open EthLib.Base SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic Verify.Lifecycle
open Verify.Lifecycle.Examples (fuel selector_eq)

abbrev pairU := Examples.PairCtor.importedSourceUnit
abbrev argU := Examples.ArgCtor.importedSourceUnit
abbrev u8U := Uint8Ctor.importedSourceUnit
abbrev pI := Verify.Lifecycle.Deploy.Ctors.PairCtor.init
abbrev aI := Verify.Lifecycle.Deploy.Ctors.ArgCtor.init

/-- `admitCtor?` on the checked contract `name` of `u`; `none` when it does not check. -/
def admit? (u : SourceUnit) (name : String) (init creation : ByteArray) (ws : List Nat) :
    Option (Except CtorBlocked Unit) :=
  match TypeCheck.CheckedInput.contract u name with
  | .ok c => some (admitCtor? c init creation ws)
  | .error _ => none

/-- Whether admission succeeds. -/
def isOk : Option (Except CtorBlocked Unit) → Bool
  | some (.ok ()) => true
  | _ => false

/-- The creation code with raw suffix bytes. -/
def withBytes (init : ByteArray) (bs : List Nat) : ByteArray :=
  init ++ ⟨(bs.map UInt8.ofNat).toArray⟩

theorem admits_of {u : SourceUnit} {name : String} {init creation : ByteArray} {ws : List Nat}
    (h : isOk (admit? u name init creation ws) = true) {c : TypeCheck.CheckedContract}
    (hc : TypeCheck.CheckedInput.contract u name = .ok c) : CtorAdmits c init creation ws := by
  unfold admit? isOk at h
  rw [hc] at h
  apply admitCtor?_sound
  split at h
  next _ heq => simpa using heq
  next => simp at h

/-! ## Admitted: `uint256` words, up to 2^256 - 1 -/

def pairOk? : Bool := isOk (admit? pairU "PairCtor" pI (initArgs pI [42, 0xbeef]) [42, 0xbeef])
kernel_rfl pairOk_eq pairOk? true using selector_eq mkIdx_eq

def pairMax? : Bool :=
  isOk (admit? pairU "PairCtor" pI (initArgs pI [2 ^ 256 - 1, 0]) [2 ^ 256 - 1, 0])
kernel_rfl pairMax_eq pairMax? true using selector_eq mkIdx_eq

/-! ## Refused, with the reason -/

/-- 2^256 is no `uint256` word. -/
def pairOver? : Bool :=
  match admit? pairU "PairCtor" pI (initArgs pI [2 ^ 256, 0]) [2 ^ 256, 0] with
  | some (.error .wordRange) => true
  | _ => false
kernel_rfl pairOver_eq pairOver? true using selector_eq mkIdx_eq

/-- An `address` parameter is BLOCKED, even on the words solar's own creation carries. -/
def argBlocked? : Bool :=
  match admit? argU "ArgCtor" aI (initArgs aI [42, 0xbeef]) [42, 0xbeef] with
  | some (.error (.param 1 .address)) => true
  | _ => false
kernel_rfl argBlocked_eq argBlocked? true using selector_eq mkIdx_eq

/-- A `uint8` parameter is BLOCKED by its narrowing cleanup. -/
def u8Blocked? : Bool :=
  match admit? u8U "Uint8Ctor" pI (initArgs pI [5]) [5] with
  | some (.error (.cleanup 0 (.uint 8))) => true
  | _ => false
kernel_rfl u8Blocked_eq u8Blocked? true using selector_eq mkIdx_eq

/-- Wrong words for the creation code. -/
def pairWrong? : Bool :=
  match admit? pairU "PairCtor" pI (initArgs pI [42, 0xbeef]) [41, 0xbeef] with
  | some (.error .suffix) => true
  | _ => false
kernel_rfl pairWrong_eq pairWrong? true using selector_eq mkIdx_eq

/-- Missing and extra words. -/
def pairArity? : Bool :=
  (match admit? pairU "PairCtor" pI (initArgs pI [42]) [42] with
    | some (.error (.arity 2 1)) => true
    | _ => false) &&
  (match admit? pairU "PairCtor" pI (initArgs pI [42, 0xbeef, 5]) [42, 0xbeef, 5] with
    | some (.error (.arity 2 3)) => true
    | _ => false)
kernel_rfl pairArity_eq pairArity? true using selector_eq mkIdx_eq

/-! ## Malformed suffixes: which layer refuses -/

/-- The checked constructor's decoder on raw suffix bytes: `true` when it decodes. -/
def decodes? (bs : List Nat) : Bool :=
  match TypeCheck.CheckedInput.contract pairU "PairCtor" with
  | .ok c => match TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl with
    | some f => (SolidCore.Solidity.Source.ABI.decodeFunctionArgs? f bs).toBool
    | none => false
  | .error _ => false

def words2 : List Nat := (natToBytes 32 42 ++ natToBytes 32 0xbeef).map UInt8.toNat

/-- Decoder layer: 63 bytes are short of two heads. -/
def decShort? : Bool := decodes? (words2.take 63)
kernel_rfl decShort_eq decShort? false using selector_eq mkIdx_eq

/-- Trailing bytes pass the decoder. -/
def decTrailing? : Bool := decodes? (words2 ++ List.replicate 32 0)
kernel_rfl decTrailing_eq decTrailing? true using selector_eq mkIdx_eq

def decMisaligned? : Bool := decodes? (words2 ++ List.replicate 5 0)
kernel_rfl decMisaligned_eq decMisaligned? true using selector_eq mkIdx_eq

/-- Exact-suffix layer: short, trailing and misaligned creation codes are refused. -/
def pairShort? : Bool :=
  match admit? pairU "PairCtor" pI (withBytes pI (words2.take 63)) [42, 0xbeef] with
  | some (.error .suffix) => true
  | _ => false
kernel_rfl pairShort_eq pairShort? true using selector_eq mkIdx_eq

def pairTrailing? : Bool :=
  match admit? pairU "PairCtor" pI (withBytes pI (words2 ++ List.replicate 32 0)) [42, 0xbeef] with
  | some (.error .suffix) => true
  | _ => false
kernel_rfl pairTrailing_eq pairTrailing? true using selector_eq mkIdx_eq

def pairMisaligned? : Bool :=
  match admit? pairU "PairCtor" pI (withBytes pI (words2 ++ List.replicate 5 0)) [42, 0xbeef] with
  | some (.error .suffix) => true
  | _ => false
kernel_rfl pairMisaligned_eq pairMisaligned? true using selector_eq mkIdx_eq

/-! ## No rescue by other words -/

/-- Creation code carrying [41, 0xbeef] admits no other words, so no choice of `ctorArgs` makes it
the creation of [42, 0xbeef]: for any contract and init code. -/
theorem no_rescue (c : TypeCheck.CheckedContract) (init : ByteArray) (ws : List Nat)
    (h : CtorAdmits c init (initArgs init [41, 0xbeef]) ws) : ws ≠ [42, 0xbeef] := by
  have := ArgsBound.unique h.bound ⟨rfl, by decide⟩
  rw [this]; decide

/-! ## Driver-shaped: the premises of `Source.run_of_statement` for a pinned fixture -/

/-- `PairCtor`'s source, deployed with [42, 0xbeef]. -/
def pairSrc : SolidCore.Verify.Generic.Source [42, 0xbeef] := ⟨pairU, "PairCtor", fuel⟩

/-- **Every premise of `run_of_statement` for `PairCtor` at [42, 0xbeef]**: the source's own checked
contract, typed admission of solar's creation code (checked evidence: `pairOk_eq` through
`admitCtor?_sound`) and the lifecycle statement. -/
theorem pairCtor_premises : ∃ c, pairSrc.checked = .ok c ∧
    pairSrc.CreatedBy c pI (initArgs pI [42, 0xbeef]) ∧
    Verify.Lifecycle.Statement pairSrc.fuel c pI Verify.Lifecycle.Deploy.Ctors.PairCtor.code
      [42, 0xbeef] [(0, 42), (1, 48921)] := by
  obtain ⟨c, hc, d, hd⟩ := Examples.pairCtor_constructs
  exact ⟨c, hc, admits_of pairOk_eq hc, ⟨Verify.Lifecycle.Deploy.Ctors.PairCtor.deploys, d, hd⟩⟩

/-- `run_of_statement` applied: the creation code deploys, and the source semantics runs from the
constructor's state in every context. -/
theorem pairCtor_run : ∃ c, pairSrc.checked = .ok c ∧
    Deploys (initArgs pI [42, 0xbeef]) Verify.Lifecycle.Deploy.Ctors.PairCtor.code
      [(0, 42), (1, 48921)] := by
  obtain ⟨c, hc, hb, hl⟩ := pairCtor_premises
  exact ⟨c, hc, (SolidCore.Verify.Generic.Source.run_of_statement hc hb hl).1⟩

/-- The source's checked contract refuses `ArgCtor`'s creation: no `CreatedBy` premise. -/
theorem argCtor_not_created (c : TypeCheck.CheckedContract)
    (hc : TypeCheck.CheckedInput.contract argU "ArgCtor" = .ok c) :
    admitCtor? c aI (initArgs aI [42, 0xbeef]) [42, 0xbeef] =
      .error (.param 1 .address) := by
  have h := argBlocked_eq
  unfold argBlocked? admit? at h
  rw [hc] at h
  split at h
  next _ heq => simpa using heq
  next => simp at h

end Verify.Generic.CtorArgs.Admission

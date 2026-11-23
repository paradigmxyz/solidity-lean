import Verify.Lifecycle.Examples
import Verify.Generic.CtorArgs.OwnedCtor
import SolidCore.Refinement.Generic.Statement
import SolidCore.Refinement.Generic.LoopRun

/-!
# Gates for constructor arguments

Each gate is a closed computation of SolidCore, decided by the kernel (`kernel_rfl`, with the
Lifecycle examples' selector table and bucket index), or a theorem whose exact type is checked.
None of these names exists before the constructor-arguments interface, so this module fails to
elaborate at the base and passes after it.

The fixtures are the Lifecycle tier's (`ArgCtor`, `NoArgCtor`: Verify/Lifecycle/Examples) and
`OwnedCtor` (OwnedCtor.sol here): `constructor(uint256 x0, address owner0)` requires `x0 != 0`,
stores `x0`, `owner0` and the deployment's `msg.sender` in slots 0, 1 and 2, and `get()` returns
`x` to `owner` and 0 to anyone else.
-/

namespace Verify.Generic.CtorArgs

open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic Verify.Lifecycle
open Verify.Lifecycle.Examples (fuel selector_eq)

/-- A call of `get()` with the call storage `st`. -/
def getCall (st : List (Nat × Nat) := []) : Call :=
  ⟨⟨#[0x6d, 0x4c, 0xe6, 0x3c]⟩, 0, st⟩

/-- The big-endian word of output bytes. -/
def word (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- What `get()` from `caller`, with the call storage `st`, observes against the contract `name` of
`u` deployed with `ws`: success, the returned word and slot 2; `none` when there is no run. -/
def obs? (u : SourceUnit) (name : String) (ws : List Nat) (caller : Nat)
    (st : List (Nat × Nat) := []) : Option (Bool × Nat × Nat) :=
  match TypeCheck.CheckedInput.contract u name with
  | .ok c => (Source.runFromArgs caller fuel ws c (getCall st)).map
      fun o => (o.success, word o.output, o.storage 2)
  | .error _ => none

/-- `obs?` through `runFrom`, the empty-argument API. -/
def obsNil? (u : SourceUnit) (name : String) (caller : Nat) : Option (Bool × Nat × Nat) :=
  match TypeCheck.CheckedInput.contract u name with
  | .ok c => (Source.runFrom caller fuel c (getCall)).map
      fun o => (o.success, word o.output, o.storage 2)
  | .error _ => none

abbrev argU := Examples.ArgCtor.importedSourceUnit
abbrev ownU := OwnedCtor.importedSourceUnit
abbrev noU := Examples.NoArgCtor.importedSourceUnit

/-! ## 1. `[]` keeps its meaning -/

example : ∀ caller fuel c call, Source.resultFromArgs? caller fuel [] c call =
    Source.resultFrom? caller fuel c call := Source.resultFromArgs?_nil
example : ∀ caller fuel, Source.runFromArgs caller fuel [] = Source.runFrom caller fuel :=
  Source.runFromArgs_nil
example : ∀ caller fuel, solidCoreFromArgs caller fuel [] = solidCoreFrom caller fuel :=
  solidCoreFromArgs_nil
example : ∀ (src : SolidCore.Verify.Generic.Source) (ctx : SolidCore.Verify.Generic.Context),
    src.semAt ctx = solidCoreFrom ctx.caller src.fuel := SolidCore.Verify.Generic.Source.semAt_nil
example : ∀ fuel, Loop.runtimeRun fuel = Loop.runtimeRunFrom callerAddress fuel :=
  Loop.runtimeRun_eq_from
example : ∀ fuel, Loop.solidCoreRuntime fuel = Loop.solidCoreRuntimeFrom callerAddress fuel :=
  Loop.solidCoreRuntime_eq_from

/-- `NoArgCtor` with [] observes the same through both APIs: success, 7, slot 2 empty. -/
def nilSame? : Bool :=
  obs? noU "NoArgCtor" [] callerAddress == some (true, 7, 0) &&
    obsNil? noU "NoArgCtor" callerAddress == some (true, 7, 0)
kernel_rfl nilSame_eq nilSame? true using selector_eq mkIdx_eq

/-! ## 2. A parameterized constructor at two values -/

def argTwo? : Bool :=
  obs? argU "ArgCtor" [42, 0xbeef] callerAddress == some (true, 42, 0) &&
    obs? argU "ArgCtor" [7, 0xbeef] callerAddress == some (true, 7, 0)
kernel_rfl argTwo_eq argTwo? true using selector_eq mkIdx_eq

/-! ## 3. Changed, wrong and missing arguments -/

/-- Changed: the words [41, …] do not give [42, …]'s observation. -/
def argChanged? : Bool := obs? argU "ArgCtor" [41, 0xbeef] callerAddress == some (true, 42, 0)
kernel_rfl argChanged_eq argChanged? false using selector_eq mkIdx_eq

/-- Missing: with no words, or one, the two-parameter constructor leaves no run. -/
def argMissing? : Bool :=
  obs? argU "ArgCtor" [] callerAddress == none && obs? argU "ArgCtor" [42] callerAddress == none
kernel_rfl argMissing_eq argMissing? true using selector_eq mkIdx_eq

/-- Wrong: SolidCore's constructor takes the words as values, so an `address` word of 2^160 is not
refused (solc's ABI decoder would revert), and a word of 2^256 wraps to 0. Pinned as found:
on the bytecode side such a creation reverts, so `Deploys` and with it `Source.run_of_statement`
cannot hold, and `ArgsBound` refuses a word past 2^256. -/
def argWrong? : Bool :=
  obs? argU "ArgCtor" [42, 2 ^ 160] callerAddress == some (true, 42, 0) &&
    obs? argU "ArgCtor" [2 ^ 256, 5] callerAddress == some (true, 0, 0)
kernel_rfl argWrong_eq argWrong? true using selector_eq mkIdx_eq

example (init creation : ByteArray) : ¬ ArgsBound init creation [2 ^ 256, 5] := fun h =>
  absurd (h.words _ (List.mem_cons_self ..)) (by decide)

/-- Extra: a third word for a two-parameter constructor leaves no run. -/
def argExtra? : Bool := obs? argU "ArgCtor" [42, 0xbeef, 5] callerAddress == none
kernel_rfl argExtra_eq argExtra? true using selector_eq mkIdx_eq

/-- The creation code binds the words: no other list of words fits it. -/
example (init : ByteArray) :
    ¬ ArgsBound init (initArgs init [42, 0xbeef]) [41, 0xbeef] := fun h =>
  absurd (ArgsBound.unique ⟨rfl, by decide⟩ h) (by decide)

example (init : ByteArray) : ¬ ArgsBound init (initArgs init [42, 0xbeef]) [42] := fun h =>
  absurd (ArgsBound.unique ⟨rfl, by decide⟩ h) (by decide)

/-! ## 4. Constructor failure -/

/-- `require(x0 != 0)` fails at 0: no run. -/
def ownRevert? : Bool := obs? ownU "OwnedCtor" [0, 0xbeef] 0xbeef == none
kernel_rfl ownRevert_eq ownRevert? true using selector_eq mkIdx_eq

example : ∀ {fuel ws c}, (∀ d vs, Source.deployArgs? fuel ws c ≠ some (SolidCore.Solidity.Source.CallResult.returned d vs)) →
    ∀ caller call, Source.runFromArgs caller fuel ws c call = none := runFromArgs_eq_none

/-! ## 5. Constructor-written storage against the call's storage -/

/-- The call's storage is written over the deployed storage: a call entry at slot 0 wins, one
elsewhere leaves the constructor's value. -/
def collide? : Bool :=
  obs? argU "ArgCtor" [42, 0xbeef] callerAddress [(0, 99)] == some (true, 99, 0) &&
    obs? argU "ArgCtor" [42, 0xbeef] callerAddress [(5, 99)] == some (true, 42, 0)
kernel_rfl collide_eq collide? true using selector_eq mkIdx_eq

/-! ## 6. Context mismatch, and 7. a nondefault caller on the parameterized route -/

/-- The owner (0xbeef, not `callerAddress`) gets `x`; the default caller gets 0. The deployment's
sender in slot 2 is `selfAddress` from both: the runtime caller never reaches the constructor. -/
def ownCaller? : Bool :=
  obs? ownU "OwnedCtor" [42, 0xbeef] 0xbeef == some (true, 42, selfAddress) &&
    obs? ownU "OwnedCtor" [42, 0xbeef] callerAddress == some (true, 0, selfAddress) &&
    obs? ownU "OwnedCtor" [43, 0xbeef] 0xbeef == some (true, 43, selfAddress)
kernel_rfl ownCaller_eq ownCaller? true using selector_eq mkIdx_eq

/-- Claiming the runtime caller as the deployment's sender fails. -/
def ownDeployerIsCaller? : Bool :=
  obs? ownU "OwnedCtor" [42, 0xbeef] 0xbeef == some (true, 42, 0xbeef)
kernel_rfl ownDeployerIsCaller_eq ownDeployerIsCaller? false using selector_eq mkIdx_eq

/-- The two contexts give different semantics for the same source and words. -/
theorem semAt_ctx_differ : obs? ownU "OwnedCtor" [42, 0xbeef] 0xbeef ≠
    obs? ownU "OwnedCtor" [42, 0xbeef] callerAddress := by
  have h := ownCaller_eq
  simp only [ownCaller?, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1, h.1.2]; decide

end Verify.Generic.CtorArgs

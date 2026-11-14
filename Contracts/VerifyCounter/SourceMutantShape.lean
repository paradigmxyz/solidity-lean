import Contracts.VerifyCounter.Source
import Contracts.VerifyCounter.SourceMutantAst

/-!
# The mutant `Counter` type checks, and its `bump`

The kernel checks (`shapeM_eq`, `kernel_rfl` on the type checker's copies, selectors by
`Source.selector_eq`) that SolidCore's type checker accepts `SourceMutantAst.lean`, with
`Counter`'s storage fields and no events, and that its function of selector `bump(uint256)` is
`bumpFnM`: bump's body with the loop `for (; i < n;) {}` (`loopM`). See `SourceMutant.lean`.
-/

namespace Contracts.VerifyCounter.Mutant
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open Contracts.VerifyCounter.Source

/-- The mutant's checked `Counter`. -/
def contractM? : Except SolidCore.Solidity.TypeCheck.TypeError SolidCore.Solidity.TypeCheck.CheckedContract :=
  SolidCore.Solidity.TypeCheck.CheckedInput.contract
    SolidCore.Refinement.Source.VerifyCounterMutant.importedSourceUnit "Counter"

/-- The mutant's loop: `for (; i < n;) {}` (its `init` is the declaration before it). -/
def loopM : Stmt := .forLoop .skip cond .skip (.block [])

/-- The mutant's body. -/
def bumpBodyM : Stmt := .block [s1, .block [s2, .block [s3, loopM]]]

/-- The mutant's `bump`. -/
def bumpFnM : FunctionDef := { bumpFn with body := bumpBodyM }

def shapeM? : Option (List StorageField × List EventDecl × Option FunctionDef) :=
  match contractM? with
  | .ok c => some (c.core.storageFields, c.core.eventDecls, c.core.findFunctionBySelector? bumpSel)
  | .error _ => none

kernel_rfl shapeM_eq shapeM? (some (vcFields, [], some bumpFnM)) using selector_eq

theorem shapeM_of {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contractM? = .ok c) :
    c.core.storageFields = vcFields ∧ c.core.eventDecls = [] ∧
      c.core.findFunctionBySelector? bumpSel = some bumpFnM := by
  have h := shapeM_eq
  unfold shapeM? at h
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h

theorem contractM_ok : ∃ c, contractM? = .ok c := by
  have h := shapeM_eq
  unfold shapeM? at h
  cases hc : contractM? with
  | ok c => exact ⟨c, rfl⟩
  | error _ => rw [hc] at h; simp at h

end Contracts.VerifyCounter.Mutant

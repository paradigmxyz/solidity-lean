import Verify.SourceText.Bridge
import SolidCore.Refinement.Generic.SourceRun

/-!
# A reading's call, as SolidCore's run, by the kernel

`runTree r sel args σ` is the same computation for every reading: check its source, test that the
constructor leaves no storage and no logs, find the function with selector `sel`, erase it to its
branch tree (`eraseFn`), and evaluate the tree on the argument words and the storage `σ`.
`run_eq_runTree` says that whenever it gives a result, that result is SolidCore's `Source.run` of the
call, by the generic `Generic.source_run`; no second interpreter and no storage model of its own. The
kernel evaluates `runTree` (`kernel_rfl`), so a run's storage is proved with Lean's three axioms.
Contracts whose constructor writes storage are outside it (`none`), as is any function
`eraseFn` does not erase.
-/

namespace SolidCore.Verify.SourceText

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity

/-- The checked contract of a reading, with fuel `fuel`. -/
def Reading.checkedAt (r : Reading) (fuel : Nat) : Option TypeCheck.CheckedContract :=
  match (r.source fuel).checked with
  | .ok c => some c
  | .error _ => none

/-- The erased tree's result of a call: storage `σ` and argument words `args`, no value, to the
function with selector `sel`, when the constructor leaves empty storage and no logs. -/
def runTree (fuel : Nat) (r : Reading) (sel : Nat) (args : List Nat) (σ : List (Nat × Nat)) :
    Option SolarTV.Observable :=
  match r.checkedAt fuel with
  | none => none
  | some c =>
    if Wide.deployedAt fuel c [] = true ∧ sel < 2 ^ 32 ∧ args.all (· < 2 ^ 256) = true then
      match c.core.findFunctionBySelector? sel with
      | none => none
      | some fn =>
        if args.length = fn.params.length then
          (eraseFn (envOf c.core) fuel fn).map fun T =>
            (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs
        else none
    else none

/-- **The tree's result is SolidCore's run.** -/
theorem run_eq_runTree {fuel : Nat} {r : Reading} {sel : Nat} {args : List Nat}
    {σ : List (Nat × Nat)} {o : SolarTV.Observable} (h : runTree fuel r sel args σ = some o) :
    ∃ c, r.checkedAt fuel = some c ∧
      Source.run fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } = some o := by
  unfold runTree at h
  cases hc : r.checkedAt fuel with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    refine ⟨c, rfl, ?_⟩
    simp only at h
    by_cases hg : Wide.deployedAt fuel c [] = true ∧ sel < 2 ^ 32 ∧ args.all (· < 2 ^ 256) = true
    · rw [if_pos hg] at h
      obtain ⟨hdep, hsel, hargs⟩ := hg
      cases hfn : c.core.findFunctionBySelector? sel with
      | none => rw [hfn] at h; cases h
      | some fn =>
        rw [hfn] at h
        simp only at h
        by_cases hlen : args.length = fn.params.length
        · rw [if_pos hlen] at h
          cases hT : eraseFn (envOf c.core) fuel fn with
          | none => rw [hT] at h; cases h
          | some T =>
            rw [hT] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep
            have hcov : Covers [] σ := fun _ h => by simp at h
            have hargs' : ∀ a ∈ args, a < 2 ^ 256 := by
              intro a ha
              simpa using List.all_eq_true.mp hargs a ha
            exact source_run hd hcov hsel hfn hT args hlen hargs'
        · rw [if_neg hlen] at h; cases h
    · rw [if_neg hg] at h; cases h

end SolidCore.Verify.SourceText

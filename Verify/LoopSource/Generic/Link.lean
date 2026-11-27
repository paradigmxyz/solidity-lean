import Verify.LoopSource.Generic.Statement

/-!
# The generic link: a body that runs to its tree gives the driver Statement

`generic_link : GenericLink`. Every valid call runs, on `solidCoreRuntime fuel`, to the observable
of the tree (`runtime_run_clean`, whose only premise about the body is `BodyRuns`), so:

* termination: `some` of the tree's observable, which `Allowed` holds of;
* the specification: every result is the tree's observable, which `Post` holds of;
* inhabitation: the call with all-zero argument words, which are clean at every bound
  (`argsClean_zeros`);
* equivalence and resources: the premises.

Nothing here names a contract, a selector or a file: the theorem is about every checked contract
and function the hypotheses describe.
-/

namespace Verify.LoopSource.Generic
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- All-zero argument words are clean at every bound. -/
theorem argsClean_zeros : ∀ (ws : List Nat) (k : Nat), argsClean ws (List.replicate k 0) = true
  | [], _ => by cases ‹Nat› <;> rfl
  | _ :: _, 0 => rfl
  | w :: ws, k + 1 => by
    show (decide (0 ≤ w) && argsClean ws (List.replicate k 0)) = true
    rw [argsClean_zeros ws k]
    simp

/-- **Every valid call runs to the tree's observable**, from `BodyRuns`. -/
theorem runs_of_bodyRuns {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract} {sel : Nat}
    {fn : FunctionDef} {ws : List Nat} {b : Br} {T : Tree} (hsel : sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? sel = some fn)
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    (hT : brTree fn (argFacts ws 0) b = some T) (σ : List (Nat × Nat)) {args : List Nat}
    (ha : ArgsOk fn ws args) :
    (solidCoreRuntime fuel).run c (selCall sel σ args) =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  obtain ⟨hlen, hargs, hclean⟩ := ha
  have hdec := decode_args hw args hlen hargs
  rw [if_pos hclean] at hdec
  exact runtime_run_clean hsel hfind hw hret hb hT args hlen hargs hclean hdec

/-- **The generic whole-Statement link.** -/
theorem generic_link : GenericLink := by
  intro fuel c sel fn ws b T hsel hfind hw hret hb hT code Allowed Post G hA hP heq hres
  have hinh : ArgsOk fn ws (List.replicate fn.params.length 0) :=
    ⟨List.length_replicate .., fun a ha => by
      rw [List.eq_of_mem_replicate ha]; exact Nat.two_pow_pos 256, argsClean_zeros ws _⟩
  refine ⟨⟨_, [], _, hinh, rfl⟩, heq, ?_, ?_, hres⟩
  · rintro _ ⟨σ, args, ha, rfl⟩
    exact ⟨_, runs_of_bodyRuns hsel hfind hw hret hb hT σ ha, hA σ args ha⟩
  · rintro _ ⟨σ, args, ha, rfl⟩ obs hs
    rw [runs_of_bodyRuns hsel hfind hw hret hb hT σ ha] at hs
    obtain rfl := Option.some.inj hs
    exact hP σ args ha

end Verify.LoopSource.Generic

/-- info: 'Verify.LoopSource.Generic.generic_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Generic.generic_link

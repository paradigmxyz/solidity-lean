import Verify.Spec.TreeLoopCheck
import Verify.Spec.TreeArgs
import Verify.LoopSource.Equiv.CtorBridge
import Verify.LoopSource.Generic.Link

/-!
# A loop function's exported spec, for the contract deployed with constructor arguments

The loop route's spec bridge (spec_connect.py `--loops`, TreeLoopCheck.lean) states a loop function's
exported spec on its loop erasure's tree, `TreeLoop.LoopSpec`, in the fixed frame and over the runtime
code alone (`Generic.Loop.solidCoreRuntime`): no constructor runs. This module carries it to the
contract SolidCore's constructor leaves on the argument words `ws0` (`solidCoreFromArgs callerAddress
fuel ws0`), as TreeArgs.lean carries the generic stage's functions:

* `loopScope sel ws s`: the loop function's calls (its selector, clean argument words of its widths, no
  value) from any storage covering `s`;
* `holdsFn_of_loopSpec_args`: from `LoopSpec`, a load-level deployment on `ws0`
  (`Loop.LoadDeployed`) and a storage list `s` every cover of which gives its load cover, every
  function spec of the bundle holds of the deployed contract on `loopScope sel ws s`: on such a call the
  deployed run is the runtime code's (`CtorBridge.semAt_eq_runtime_load`), which runs to the erasure's
  tree (`Generic.runs_of_bodyRuns`), on which the exported postcondition holds (`LoopSpec`'s `OnTree`);
* `holdsFn_of_sel_ne`, `HoldsFn.or`, `selectorOf_loopScope`, `selectorOf_stageScope`: what assembles one
  `Holds` over the union of every function's calls: a function spec imposes nothing on a call of
  another selector.

Fixed frame: the caller `callerAddress`, value 0, as the loop route's.
-/

namespace SolidCore.Spec.TreeLoop

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity.Source
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Generic
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep selectorOf_calldata)

/-- A loop function's calls from storage covering `s`: selector `sel`, clean argument words of the
widths `ws`, no value. -/
def loopScope (sel : Nat) (ws : List Nat) (s : List (Nat × Nat)) (call : Call) : Prop :=
  ∃ σ args, args.length = ws.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧ argsClean ws args = true ∧
    Covers s σ ∧ call = selCall sel σ args

/-- **A loop function's exported spec holds of the contract deployed with `ws0`**, on its calls from
storage covering `s`, for every function spec of the bundle. -/
theorem holdsFn_of_loopSpec_args {c : SolidCore.Solidity.TypeCheck.CheckedContract} {fuel sel : Nat}
    {ws : List Nat} {T : Tree} {b : Bundle} (hL : LoopSpec c fuel sel ws T b) (hsel : sel < 2 ^ 32)
    {ws0 : List Nat} {d : SolidCore.Solidity.Source.State} (hd : LoadDeployed fuel c ws0 d)
    {s : List (Nat × Nat)} (hcov : ∀ σ, Covers s σ → CoversLoad d σ) {fs : FnSpec}
    (hfs : fs ∈ b.spec.specs) :
    HoldsFn (solidCoreFromArgs callerAddress fuel ws0) c (loopScope sel ws s) b ctxOfCall idStep fs := by
  obtain ⟨f, br, hf, hw, hret, hb, hT, hlen, -, hP, -⟩ := hL
  rintro _ ⟨σ, args, hl, ha, hcl, hc, rfl⟩ iargs pre hpre
  have hok : ArgsOk f ws args := ⟨hl.trans hlen.symm, ha, hcl⟩
  have hrun : (solidCoreFromArgs callerAddress fuel ws0).run c (selCall sel σ args) =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
    rw [semAt_eq_runtime_load hd hsel hf hw hret (bodyRuns_of_eraseLoop hb) hT
      ⟨⟨σ, args, hok, rfl⟩, hcov σ hc⟩]
    exact runs_of_bodyRuns hsel hf hw hret (bodyRuns_of_eraseLoop hb) hT σ hok
  exact ⟨_, hrun, hP σ args hok fs hfs iargs pre hpre⟩

/-- A function spec holds on any calls of another selector: its precondition never holds there. -/
theorem holdsFn_of_sel_ne {S : Sem} {p : S.Prog} {V : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} {fs : FnSpec} {sel : Nat}
    (hV : ∀ call, V call → selectorOf call = sel) (hne : sel ≠ fs.selector) :
    HoldsFn S p V b ctxOf step fs := by
  intro call hv args pre hpre
  exact absurd (hpre.1.2.1.symm.trans (hV call hv)).symm hne

/-- A function spec on two sets of calls holds on their union. -/
theorem HoldsFn.or {S : Sem} {p : S.Prog} {V₁ V₂ : Call → Prop} {b : Bundle}
    {ctxOf : Call → Ctx} {step : GhostStep} {fs : FnSpec}
    (h₁ : HoldsFn S p V₁ b ctxOf step fs) (h₂ : HoldsFn S p V₂ b ctxOf step fs) :
    HoldsFn S p (fun call => V₁ call ∨ V₂ call) b ctxOf step fs := by
  rintro call (h | h)
  · exact h₁ call h
  · exact h₂ call h

theorem selectorOf_loopScope {sel : Nat} (hsel : sel < 2 ^ 32) {ws : List Nat}
    {s : List (Nat × Nat)} : ∀ call, loopScope sel ws s call → selectorOf call = sel := by
  rintro _ ⟨σ, args, -, -, -, -, rfl⟩
  exact selectorOf_calldata hsel args 0 σ

theorem selectorOf_stageScope {fn : SolidCore.Refinement.Abi.Fn} (hsel : fn.sel < 2 ^ 32)
    {s : List (Nat × Nat)} :
    ∀ call, SolidCore.Verify.VC.stageScope fn s call → selectorOf call = fn.sel := by
  rintro _ ⟨σ, -, g, hg, args, -, -, rfl⟩
  simp only [List.mem_singleton] at hg
  subst hg
  exact selectorOf_calldata hsel args 0 σ

/-- info: 'SolidCore.Spec.TreeLoop.holdsFn_of_loopSpec_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_loopSpec_args

end SolidCore.Spec.TreeLoop

import Verify.VC.Model
import Verify.VC.Check

/-!
# From an erased function to solar-verify's obligations, once for every function

The generic source stage erases a function of its fragment to a `Tree` (`eraseFn`), and
`source_run` proves that SolidCore runs every call of it as the tree. solar-verify's verdict on a
script is `Valid`, and `checkScript` ties the script's obligations to Lean obligations
(`checkScript_sound`). What is left per function is the binding: the Lean obligations, at the
assignment of solar-verify's names a call binds, say what the tree's result is.

* `ObsAt obs σ`: every Lean obligation of `obs` holds at the assignment `σ`.
* `Binds fn T obs env P`: on every call's argument words `args` (as many as `fn` takes, each
  below `2 ^ 256`) and every storage `s` of words, the obligations at `env args s` give `P args s`
  of the tree's observable. This is the one proof a function needs, and it is about the tree and
  the obligations alone: no SolidCore run, no fuel, no ABI.
* `triple_of_binds`: for every function the stage erases, its obligations' validity and the
  binding give the triple `{True} c {treePost fn P}` against SolidCore on the stage's scope
  (`stageScope`). Unlike `implements_tree`, the tree may emit logs: the observable is the tree's,
  logs included.
* `triple_of_checked`: the same from solar-verify's script, its verdict `Valid cs` and the
  kernel's `checkScript cs obs = true`.

A verdict is a hypothesis (`Valid cs`): solar-verify's solver is not trusted, so the theorem says
what holds if its verdict is right, and `checkScript` makes sure the verdict is about the
obligations the binding uses. An obligation that is valid by solar-verify's own encoding needs no
verdict: `triple_of_binds` takes `ObsValid obs` proved in Lean.
-/

namespace SolidCore.Verify.VC

open SolidCore.Verify SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- Every Lean obligation of `obs` holds at the assignment `σ`. -/
def ObsAt (obs : List (List Tm × Tm)) (σ : Env) : Prop :=
  ∀ o ∈ obs, (∀ x ∈ o.1, x.Holds σ) → o.2.Holds σ

theorem ObsValid.at {obs : List (List Tm × Tm)} (h : ObsValid obs) (σ : Env) : ObsAt obs σ :=
  fun o ho hh => h o ho σ hh

/-- The binding of a function's tree to Lean obligations: on every call's argument words and
storage of words, the obligations at the assignment `env args s` give `P` of the tree's
observable. -/
def Binds (fn : Fn) (T : Tree) (obs : List (List Tm × Tm)) (env : List Nat → Storage → Env)
    (P : List Nat → Storage → Observable → Prop) : Prop :=
  ∀ (args : List Nat) (s : Storage), args.length = fn.params.length → (∀ a ∈ args, a < 2 ^ 256) →
    (∀ k, s k < 2 ^ 256) → ObsAt obs (env args s) → P args s (T.eval (valOf args s)).obs

/-- `P` of a call: of its argument words, its initial storage and its observable. -/
def treePost (fn : Fn) (P : List Nat → Storage → Observable → Prop) (call : Call)
    (o : Observable) : Prop :=
  P (argWords fn.params.length call) (initStorage call) o

/-- **Every function the generic source stage erases meets the triple its binding gives**, from
valid Lean obligations. -/
theorem triple_of_binds {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {obs : List (List Tm × Tm)}
    {env : List Nat → Storage → Env} {P : List Nat → Storage → Observable → Prop}
    (hobs : ObsValid obs) (hbind : Binds fn T obs env P) :
    Triple fuel c (stageScope fn s) (fun _ => True) (treePost fn P) := by
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ -
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hrun := source_run hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  refine ⟨by simp [hrun], fun o ho => ?_⟩
  rw [hrun] at ho
  cases ho
  have hw : argWords fn'.params.length
      ({ calldata := Abi.calldata fn'.sel args, callvalue := 0, storage := σ } : Call) = args :=
    hl ▸ argWords_calldata _ args hargs 0 σ
  unfold treePost
  rw [hw]
  exact hbind args (slotValue σ) hl hargs (fun k => Generic.slotValue_lt σ k) (hobs.at _)

/-- **The same from solar-verify's script**: its verdict and the kernel's check that its
obligations are the Lean ones. -/
theorem triple_of_checked {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {cs : List Cmd} {obs : List (List Tm × Tm)}
    {env : List Nat → Storage → Env} {P : List Nat → Storage → Observable → Prop}
    (hcheck : checkScript cs obs = true) (hv : Valid cs) (hbind : Binds fn T obs env P) :
    Triple fuel c (stageScope fn s) (fun _ => True) (treePost fn P) :=
  triple_of_binds hd hsel hfind hlen hT (checkScript_sound hcheck hv) hbind

end SolidCore.Verify.VC

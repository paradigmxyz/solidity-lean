import Verify.Generic.Certificate
import Verify.VC.EndToEnd

/-!
# The specification from kernel-discharged verification conditions

The certificate's `meets` and `allowed` from solar-verify's verification conditions, through the
existing pieces: for each function of the specification, `Verify.VC.triple_of_discharged`
(Verify/VC/EndToEnd.lean: the kernel's `dischargeScript`, Verify/Discharge, the check of the
script's obligations and their binding to the function's erased tree) gives SolidCore's triple on
the function's calls; `meets_of_triples` combines one triple per function into the specification's
`Meets` on any valid calls, with the postcondition `vcPost`: on a call of a function's scope, its
postcondition. A function whose loops need invariants supplies them in its script; the kernel
checks them with the rest, and nothing changes here.
-/

namespace SolidCore.Verify.Generic

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity SolidCore.Verify
open SolidCore.Refinement.Abi SolidCore.Refinement.Generic SolidCore.Verify.VC

/-- The postcondition of a family of functions: on a call of a function's scope, its
postcondition. -/
def vcPost {ι : Type} (fns : List ι) (scope : ι → Call → Prop)
    (post : ι → Call → Observable → Prop) (call : Call) (obs : Observable) : Prop :=
  ∀ i ∈ fns, scope i call → post i call obs

/-- One triple is the specification of its scope. -/
theorem meets_of_triple {fuel : Nat} {c : TypeCheck.CheckedContract} {scope : Call → Prop}
    {post : Call → Observable → Prop} (h : Triple fuel c scope (fun _ => True) post) :
    Meets (solidCore fuel) c scope post :=
  fun call hc obs hs => (h call hc trivial).2 obs hs

/-- One triple shows the source ends on its scope. -/
theorem defined_of_triple {fuel : Nat} {c : TypeCheck.CheckedContract} {scope : Call → Prop}
    {post : Call → Observable → Prop} (h : Triple fuel c scope (fun _ => True) post) :
    ∀ call, scope call → ((solidCore fuel).run c call).isSome = true :=
  fun call hc => (h call hc trivial).1

/-- **One triple per function is the specification of every valid call.** -/
theorem meets_of_triples {fuel : Nat} {c : TypeCheck.CheckedContract} {ι : Type} {fns : List ι}
    {scope : ι → Call → Prop} {post : ι → Call → Observable → Prop} {Valid : Call → Prop}
    (h : ∀ i ∈ fns, Triple fuel c (scope i) (fun _ => True) (post i)) :
    Meets (solidCore fuel) c Valid (vcPost fns scope post) :=
  fun call _ obs hs i hi hsc => (h i hi call hsc trivial).2 obs hs

/-- **A discharged script per function is the specification of every valid call**: the kernel's
discharge (`dischargeScript`), the obligations' check and their binding, for each function. -/
theorem meets_of_discharged {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fns : List Fn}
    {P : Fn → List Nat → Storage → Observable → Prop} {Valid : Call → Prop}
    (h : ∀ fn ∈ fns, ∃ (f : Source.FunctionDef) (T : Tree) (cs : List Cmd)
      (obs : List (List Tm × Tm)) (env : List Nat → Storage → Env),
      fn.sel < 2 ^ 32 ∧ c.core.findFunctionBySelector? fn.sel = some f ∧
      f.params.length = fn.params.length ∧ eraseFn (envOf c.core) fuel f = some T ∧
      dischargeScript cs = true ∧ checkScript cs obs = true ∧ Binds fn T obs env (P fn)) :
    Meets (solidCore fuel) c Valid
      (vcPost fns (fun fn => stageScope fn s) (fun fn => treePost fn (P fn))) := by
  refine meets_of_triples fun fn hfn => ?_
  obtain ⟨f, T, cs, obs, env, hsel, hfind, hlen, hT, hdis, hcheck, hbind⟩ := h fn hfn
  exact VC.triple_of_discharged hd hsel hfind hlen hT hdis hcheck hbind

/-- info: 'SolidCore.Verify.Generic.meets_of_discharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_of_discharged

end SolidCore.Verify.Generic

import SolidCore.Refinement.Generic.Total
import SolidCore.Refinement.Generic.Value

/-!
# Generic stages at every value, and refinement from "SolidCore ends"

The contract-independent part of `SolidCore.Refinement.Solar.Totality`, moved here unchanged so that
a module that needs only these lemmas (`Verify.ShapeGeneric`) does not import the bank, events and
mulx certificates:

* `definedAtValue`, `definedValue`: SolidCore finishes every call of the generic stage's scope at
  every value.
* `satisfies_of_defined`, `refines_of_defined_stages`: a total refinement from three stages and
  "SolidCore ends".
* `not_defined_of_none`, `not_refines_of_none`: a call on which SolidCore returns nothing refutes
  both.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi

/-- SolidCore finishes every call of the generic stage's scope at every value: at value 0 by
`definedAt`, and at any other value because the check on values (`checkValue`) says the
function is not payable, so SolidCore rejects the call (`source_run_value`). -/
theorem definedAtValue {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hcov, hv, f, hf, args, hlen, hargs, rfl⟩
  by_cases hv0 : v = 0
  · subst hv0
    exact definedAt hd hchk _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  have hcf := List.all_eq_true.mp hchk f hf
  have hcv := List.all_eq_true.mp hval f hf
  unfold checkFn at hcf
  unfold checkValueFn at hcv
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFn (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTreeValue m f.sel f.params.length mirFuel env with
  | none => simp [hfind, ht2] at hcv
  | some T =>
  simp only [hfind, ht1, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  simp only [hfind, ht2, Bool.and_eq_true, Bool.not_eq_true'] at hcv
  obtain ⟨hpay, -⟩ := hcv
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  have hsrc := source_run_value hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ
  change (Source.run fuel c _).isSome = true
  rw [hsrc]
  rfl

/-- At every value, from any storage, for a constructor that leaves no storage. -/
theorem definedValue {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ v, fullScopeValue fns σ v call) :=
  fun call ⟨σ, v, h⟩ =>
    definedAtValue hd hchk hval call ⟨σ, v, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- A program that finishes every call of the scope satisfies the specification "it ends". -/
theorem satisfies_of_defined {S : Sem} {p : S.Prog} {scope : Call → Prop}
    (h : Defined S p scope) : Satisfies S p scope (fun _ => True) (fun _ _ => True) :=
  fun call hc _ =>
    let ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp (h call hc)
    ⟨obs, hobs, trivial⟩

/-- `bytecode_total_of_stages` with the specification "SolidCore ends": three stages from a
source that finishes every call of the scope are a total refinement on it. -/
theorem refines_of_defined_stages {fuel : Nat} {mirSem evmirSem : Sem}
    {c : TypeCheck.CheckedContract} {mir : mirSem.Prog} {evmir : evmirSem.Prog} {code : ByteArray}
    {scope : Call → Prop} (ends : Defined (solidCore fuel) c scope)
    (lowering : Stage (solidCore fuel) mirSem c mir scope)
    (backend : Stage mirSem evmirSem mir evmir scope)
    (assembly : Stage evmirSem ethLib evmir code scope) :
    Refines fuel c code scope :=
  fun call hc =>
    (bytecode_total_of_stages (satisfies_of_defined ends) lowering backend assembly).1 call
      ⟨hc, trivial⟩

/-- **Negative**: a call of the scope on which SolidCore returns nothing (it runs out of fuel or
fails) refutes `Defined`. -/
theorem not_defined_of_none {fuel : Nat} {c : TypeCheck.CheckedContract} {scope : Call → Prop}
    {call : Call} (hc : scope call) (hnone : Source.run fuel c call = none) :
    ¬ Defined (solidCore fuel) c scope := fun h => by
  have := h call hc
  change (Source.run fuel c call).isSome = true at this
  rw [hnone] at this
  exact Bool.false_ne_true this

/-- **Negative**: and so refutes `Refines`, whatever the bytecode: running out of fuel is a failure
of the total refinement, never a vacuous success. -/
theorem not_refines_of_none {fuel : Nat} {c : TypeCheck.CheckedContract} {code : ByteArray}
    {scope : Call → Prop} {call : Call} (hc : scope call)
    (hnone : Source.run fuel c call = none) : ¬ Refines fuel c code scope := fun h =>
  not_defined_of_none hc hnone ((refines_iff_total.mp h).source_defined)

end SolidCore.Refinement.Generic

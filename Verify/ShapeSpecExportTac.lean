import Verify.ShapeSpecExport

/-!
# Tactics for the generated non-vacuity theorems

A certified contract's proof module (tools/certify/shape_gen.py) states, for every function of the
exported spec, that its precondition holds on zero words with no value from the constructor's
slots written with 0 (`pre_sat_F`), and for one function that its succeeds-if conditions hold
there too (`nonvacuous`). Both are evaluations of the exported spec's terms:

* `spec_pre_zero [B]` proves `Pre B fs (ctxOfCall call) ⟨fun _ => 0, Ghost.zero, 0⟩ call (replicate n 0)`
  for the zero call of `fs`'s selector;
* `spec_sat [B]` proves `B.satAll conds env` by unfolding the bundle `B` and evaluating.
-/

namespace SolidCore.Refinement.Shapes

/-- Evaluate a bundle's conditions: `B.satAll conds env` with `B` unfolded. -/
macro "spec_sat" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp [SolidCore.Spec.Bundle.satAll, SolidCore.Spec.Bundle.sat, $ds,*, SolidCore.Spec.eval,
    SolidCore.Spec.BinOp.apply, SolidCore.Spec.mkEnv, SolidCore.Spec.Env.cur, SolidCore.Spec.ofProp,
    SolidCore.Spec.slotOf, SolidCore.Spec.Ty.ofBits, SolidCore.Spec.toWord,
    SolidCore.Refinement.Shapes.ctxOfCall])

/-- The precondition of a function of the bundle on its zero call: the words decode, the storage is
the zeros', the call has no value, and the requires and the invariants evaluate to true. -/
macro "spec_pre_zero" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine ⟨SolidCore.Refinement.Shapes.decodes_zero (by decide) (by rfl)
    (by first | rfl | decide | simp [$ds,*, SolidCore.Spec.decodeWords, SolidCore.Spec.Ty.ofWord]) 0 _,
    (SolidCore.Refinement.Shapes.slotValue_zeros _).symm,
    by simp [SolidCore.Refinement.Shapes.ctxOfCall], ?_, ?_⟩ <;>
  spec_sat [$ds,*]))

end SolidCore.Refinement.Shapes

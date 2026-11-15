import Contracts.C4.Spec.Bytecode
import Verify.Spec.GhostFree

/-! The axioms of the spec semantics' theorems: `propext`, `Classical.choice` and `Quot.sound` at
most, and no `sorry`, `native_decide` (`Lean.ofReduceBool`) or `bv_decide`. -/

#print axioms SolidCore.Spec.Ghost.sound
#print axioms SolidCore.Spec.Ghost.complete
#print axioms SolidCore.Spec.Ghost.spec_of_erased
#print axioms SolidCore.Spec.Ghost.spec_of_erased_real
#print axioms SolidCore.Spec.Ghost.ghostTotal_of_straight
#print axioms SolidCore.Spec.eval_ghostEquiv
#print axioms SolidCore.Spec.Bundle.sat_ghostEquiv
#print axioms SolidCore.Spec.Holds.of_stage
#print axioms SolidCore.Spec.spec_of_verdict
#print axioms SolidCore.Spec.Export.C4.Main_wf
#print axioms SolidCore.Spec.Solar.C4.post_of_postAt
#print axioms SolidCore.Spec.Solar.C4.holds_source
#print axioms SolidCore.Spec.Solar.C4.holds_bytecode
#print axioms SolidCore.Spec.Solar.C4.holds_bytecode_at
#print axioms SolidCore.Spec.Solar.C4.certified
#print axioms SolidCore.Spec.Solar.C4.wrong_fails

import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Solar.MulX.Certified

/-! Axiom pass, part 3 of 4: mulx against solar's mulx export (see `Main.lean`). -/

#print axioms SolidCore.Refinement.Solar.MulX.certified
#print axioms SolidCore.Refinement.Solar.MulX.certified_at
#print axioms SolidCore.Refinement.Solar.MulX.certified_deployed
#print axioms SolidCore.Refinement.Solar.MulX.certified_deployed_value
#print axioms SolidCore.Refinement.Solar.MulX.certified_at_value
#print axioms SolidCore.Refinement.Solar.MulX.lowering
#print axioms SolidCore.Refinement.Solar.MulX.loweringAt
#print axioms SolidCore.Refinement.Solar.MulX.loweringValue
#print axioms SolidCore.Refinement.Solar.MulX.loweringAtValue
#print axioms SolidCore.Refinement.Solar.MulX.check_rejects_unchecked
#print axioms SolidCore.Refinement.Solar.MulX.check_rejects_add
#print axioms SolidCore.Refinement.Solar.MulX.checkValue_rejects_payable
#print axioms SolidCore.Refinement.Solar.MulX.stageAll

#axiom_audit ".lake/axiom-closure-mulx.txt" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic"

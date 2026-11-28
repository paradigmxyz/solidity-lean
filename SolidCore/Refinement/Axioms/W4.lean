import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Solar.W4.Milestone

/-! Axiom pass, part 4 of 4: w4 against solar's w4 export (see `Main.lean`). -/

#print axioms SolidCore.Refinement.Solar.W4.certified
#print axioms SolidCore.Refinement.Solar.W4.certifiedAt
#print axioms SolidCore.Refinement.Solar.W4.stage
#print axioms SolidCore.Refinement.Solar.W4.stageAt
#print axioms SolidCore.Refinement.Solar.W4.lowering
#print axioms SolidCore.Refinement.Solar.W4.loweringAt
#print axioms SolidCore.Refinement.Solar.W4.loweringValue
#print axioms SolidCore.Refinement.Solar.W4.loweringAtValue

#axiom_audit ".lake/axiom-closure-w4.txt" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic"

import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Solar.C4.Certified

/-! Axiom pass, part 2 of 4: c4 against solar's c4 export (see `Main.lean`). -/

#print axioms SolidCore.Refinement.Solar.C4.certified
#print axioms SolidCore.Refinement.Solar.C4.certified_at
#print axioms SolidCore.Refinement.Solar.C4.certified_deployed
#print axioms SolidCore.Refinement.Solar.C4.certified_deployed_value
#print axioms SolidCore.Refinement.Solar.C4.certified_at_value
#print axioms SolidCore.Refinement.Solar.C4.satisfies_at
#print axioms SolidCore.Refinement.Solar.C4.lowering
#print axioms SolidCore.Refinement.Solar.C4.loweringAt
#print axioms SolidCore.Refinement.Solar.C4.certifiedAt
#print axioms SolidCore.Refinement.Solar.C4.lowering_generic
#print axioms SolidCore.Refinement.Solar.C4.loweringAt_generic
#print axioms SolidCore.Refinement.Solar.C4.lowering_value
#print axioms SolidCore.Refinement.Solar.C4.loweringAt_value
#print axioms SolidCore.Refinement.Solar.C4.check_rejects_bad
#print axioms SolidCore.Refinement.Solar.C4.stage
#print axioms SolidCore.Refinement.Solar.C4.stageAll

#axiom_audit ".lake/axiom-closure-c4.txt" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic"

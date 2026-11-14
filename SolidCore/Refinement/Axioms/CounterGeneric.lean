import SolidCore.Refinement.Axioms.Audit
import SolidCore.Refinement.Solar.Counter.LoweringGeneric

/-! Axiom pass, part 5 of 5: counter's generic source stage, which declares names that
`Counter.SpecAt` and `Counter.LoweringAt` also declare (see `Main.lean`). -/

#print axioms SolidCore.Refinement.Solar.Counter.lowering_generic
#print axioms SolidCore.Refinement.Solar.Counter.loweringAt
#print axioms SolidCore.Refinement.Solar.Counter.loweringAtValue
#print axioms SolidCore.Refinement.Solar.Counter.check_rejects_bad

#axiom_audit ".lake/axiom-closure-countergeneric.txt" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic"

import SolidCore.Refinement.Axioms.Audit
import Contracts.VerifyCounter.Bytecode
import Contracts.VerifyCounter.StageMir
import Contracts.VerifyCounter.StageSource
import Contracts.VerifyCounter.ShapeSource
import Contracts.VerifyCounter.SourceMutant

/-! Axiom pass, the VerifyCounter headline from solar-verify's spec to solar's bytecode, and the
bump shape certified from SolidCore's source (with the mutant that does not terminate), in its own
environment (its exported stages share names with the other contracts'). Run with
`scripts/refinement/axiom-audit.sh`. -/

#print axioms SolidCore.Refinement.Solar.VerifyCounter.spec_holds_of_bytecode
#print axioms SolidCore.Refinement.Solar.VerifyCounter.spec_holds_of_bytecode_generic
#print axioms SolarTV.Milestone.VerifyCounter.Bump.xstage0_ends
#print axioms Contracts.VerifyCounter.Source.mir_eq
#print axioms Contracts.VerifyCounter.ShapeSource.published
#print axioms Contracts.VerifyCounter.Mutant.not_terminates
#print axioms Contracts.VerifyCounter.Mutant.not_certified

#axiom_audit ".lake/axiom-closure-verifycounter.txt" "Contracts.VerifyCounter" "SolidCore.Refinement.Solar" "SolidCore.Refinement.Generic"

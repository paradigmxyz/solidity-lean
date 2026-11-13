import SolidCore.Refinement.Axioms.Audit
import Contracts.VerifyCounter.Bytecode

/-! Axiom pass, the VerifyCounter headline from solar-verify's spec to solar's bytecode, in its own
environment (its exported stages share names with the other contracts'). Run with
`scripts/refinement/axiom-audit.sh`. -/

#print axioms SolidCore.Refinement.Solar.VerifyCounter.spec_holds_of_bytecode

#axiom_audit ".lake/axiom-closure-verifycounter.txt" "Contracts.VerifyCounter" "SolidCore.Refinement.Solar"

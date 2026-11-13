import SolidCore.Refinement.Axioms.Audit
import Contracts.Token.EndToEnd

/-! Axiom pass, the Token headline from solar-verify's spec to solar's bytecode, in its own
environment (its exported stages share names with the other contracts'). Run with
`scripts/refinement/axiom-audit.sh`. -/

#print axioms Contracts.Token.spec_holds_of_bytecode
#print axioms Contracts.Token.burn_spec_bytecode
#print axioms Contracts.Token.certified

#axiom_audit ".lake/axiom-closure-token.txt" "Contracts.Token" "SolidCore.Refinement.Solar"

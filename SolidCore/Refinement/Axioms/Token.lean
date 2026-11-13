import SolidCore.Refinement.Axioms.Audit
import Contracts.Token.EndToEnd
import Contracts.Token.Exports
import Contracts.Token.VC.FromScript

/-! Axiom pass, the Token headline from solar-verify's spec to solar's bytecode, in its own
environment (its exported stages share names with the other contracts'). Run with
`scripts/refinement/axiom-audit.sh`. -/

#print axioms Contracts.Token.spec_holds_of_bytecode
#print axioms Contracts.Token.burn_spec_bytecode
#print axioms Contracts.Token.certified
#print axioms SolidCore.Verify.VC.Token.Discharged.script_valid
#print axioms SolidCore.Verify.VC.Token.transfer_triple_of_script

#axiom_audit ".lake/axiom-closure-token.txt" "Contracts.Token" "SolidCore.Refinement.Solar"

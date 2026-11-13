import SolidCore.Refinement.Axioms.Audit
import Contracts.Counter.Headline
import Contracts.Counter.EndToEnd
import Contracts.Counter.Final
import Contracts.Counter.Verdict
import Contracts.Counter.VC.Inc
import Contracts.Counter.VC.Get
import Contracts.Counter.VC.Mutants
import Contracts.Token.VC.Burn
import Contracts.Token.VC.Transfer
import Contracts.Token.VC.Mutants
import Contracts.Counter.Exports
import Contracts.Counter.SpecTree
import Contracts.Counter.VC.Discharged
import Contracts.Counter.VC.ScriptEndToEnd
import SolidCore.Refinement.Solar.EndToEnd
import Verify.LoomAxioms
import Verify.Spec.TrustedBase.Axioms

/-! Axiom pass, part 6: the per-contract headlines under Contracts/ (Counter from source spec to
solar's bytecode, and the Counter and Token verification conditions), with the Loom and trusted
base pieces they build on. Every `#print axioms` below must report a subset of [propext,
Classical.choice, Quot.sound], and the sweep must report no violation. Run with
`scripts/refinement/axiom-audit.sh`. -/

-- Counter, source spec to bytecode.
#print axioms SolidCore.Refinement.Solar.Counter.Headline.spec_holds_of_bytecode
#print axioms SolidCore.Refinement.Solar.Counter.Headline.wrong_fails
#print axioms SolidCore.Refinement.Solar.Counter.EndToEnd.inc_spec_bytecode
#print axioms SolidCore.Refinement.Solar.Counter.EndToEnd.get_spec_bytecode
#print axioms SolidCore.Refinement.Solar.Counter.Final.certified
#print axioms SolidCore.Refinement.Solar.Counter.Final.certified_trace
#print axioms SolidCore.Refinement.Solar.Counter.Verdict.bytecode_spec_of_verdict
#print axioms SolidCore.Refinement.Solar.Counter.Verdict.bytecode_of_triple

-- Verification conditions.
#print axioms SolidCore.Verify.VC.Counter.inc_triple
#print axioms SolidCore.Verify.VC.Counter.get_triple
#print axioms SolidCore.Verify.VC.Counter.srcMut_rejected
#print axioms SolidCore.Verify.VC.Counter.specMut_rejected
#print axioms SolidCore.Verify.VC.Token.burn_triple
#print axioms SolidCore.Verify.VC.Token.transfer_triple

-- Scripts discharged in the kernel and carried to bytecode.
#print axioms SolidCore.Verify.VC.dischargeScript_sound
#print axioms SolidCore.Verify.VC.bytecode_of_discharged
#print axioms SolidCore.Verify.VC.bytecode_of_checked
#print axioms SolidCore.Verify.VC.Counter.Discharged.script_valid
#print axioms SolidCore.Verify.VC.Counter.inc_bytecode_of_script
#print axioms SolidCore.Refinement.Solar.Counter.SpecTree.inc_spec_bytecode
#print axioms Contracts.Counter.deploys

-- The generic composition of the backend stages with the assembler checks.
#print axioms SolidCore.Refinement.Solar.EndToEnd.stage_of_check
#print axioms SolidCore.Refinement.Solar.EndToEnd.within_of_checkL
#print axioms SolidCore.Refinement.Solar.EndToEnd.holds_of_checkL

#axiom_audit ".lake/axiom-closure-contracts.txt" "Contracts" "Verify" "Loom"

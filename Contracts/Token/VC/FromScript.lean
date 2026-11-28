import Contracts.Token.VC.Discharged
import Contracts.Token.VC.Transfer

/-!
# Token's triples from solar-verify's script, its verdict discharged by the kernel

\`transfer_triple\` and \`burn_obligation\` (Contracts/Token/VC) take solar-verify's verdict
\`Valid Export.Token.script\` as a hypothesis; \`Discharged.script_valid\` proves it in the kernel
(\`dischargeScript\`), so they hold with \`HashInj\` as the only hypothesis.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Verify.VC

/-- \`Token.transfer\`'s three clauses from solar-verify's own obligations, with no verdict. -/
theorem transfer_triple_of_script (inj : HashInj)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnTransfer [(2, 4096)]) (fun _ => True) trPost :=
  transfer_triple Discharged.script_valid inj hc

/-- info: 'SolidCore.Verify.VC.Token.transfer_triple_of_script' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_triple_of_script

end SolidCore.Verify.VC.Token

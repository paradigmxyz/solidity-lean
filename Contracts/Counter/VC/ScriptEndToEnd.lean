import Contracts.Counter.EndToEnd
import Contracts.Counter.VC.Generic
import Contracts.Counter.VC.MilestoneDischarged
import Verify.VC.EndToEnd

/-!
# Counter's `inc`: solar-verify's script to the bytecode, by the generic composition

`inc_bytecode_of_script` is `bytecode_of_checked` (Verify/VC/EndToEnd.lean) for `inc`: solar-verify's
script for scripts/verify/CounterMilestone.sol, discharged by the kernel
(`MilestoneDischarged.script_valid`), its obligation checked to be `inc`'s Lean obligation
(`inc_check`), the binding of `inc`'s erased tree to it (`inc_binds`), and the certified stage from
SolidCore's checked `Counter` to solar's bytecode (`Verdict.agree`) give EthLib's run of the exact
bytecode on every call of `inc(uint256)`. No verdict, no hand-proved obligation.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic SolidCore.Solidity

/-- **`inc` on solar's bytecode, from solar-verify's discharged script.** -/
theorem inc_bytecode_of_script :
    ∀ call, stageScope fnInc [] call →
      ∃ o, Target.run SolidCore.Refinement.Solar.Counter.code call = some o ∧ treePost fnInc incP call o := by
  obtain ⟨c, hc⟩ := SolidCore.Refinement.Solar.Counter.contract_ok
  have hc' : contract? = .ok c := by exact hc
  have hshape := incShape_eq
  simp only [incShape?, hc', Option.some.injEq, Prod.mk.injEq] at hshape
  obtain ⟨hdep, hmap⟩ := hshape
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact bytecode_of_checked (fn := fnInc) hdd (by decide) hf hlen hT MilestoneDischarged.script_valid
    inc_check inc_binds
    (fun call h => (SolidCore.Refinement.Solar.Counter.Verdict.agree hc).stage call
      (SolidCore.Refinement.Solar.Counter.EndToEnd.inc_in_scope h))

/-- info: 'SolidCore.Verify.VC.Counter.inc_bytecode_of_script' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_bytecode_of_script

end SolidCore.Verify.VC.Counter


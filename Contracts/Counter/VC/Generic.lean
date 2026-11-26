import Contracts.Counter.VC.Inc
import Verify.VC.Obligations

/-!
# `Counter.inc` through the generic theorem

`inc_triple` (Contracts/Counter/VC/Inc.lean) is itself an instance of `triple_of_binds`: the only
proof about `inc` is the binding `inc_binds`, which speaks of the erased tree `incTree` and
solar-verify's obligation alone (no SolidCore run, no fuel, no ABI); `triple_of_binds` supplies the
rest for every function the generic source stage erases. The obligation `incHyps ⟹ incGoal` is the
one `inc_check` finds in solar-verify's script, and it is valid by solar-verify's own encoding
(`inc_obs_valid`), so the theorem takes no verdict.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Solidity

/-- `inc_triple`, from the generic theorem and the binding. -/
theorem inc_triple_of_binds {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnInc []) (fun _ => True) incPost :=
  inc_triple hc

/-- info: 'SolidCore.Verify.VC.Counter.inc_triple_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_triple_of_binds

end SolidCore.Verify.VC.Counter

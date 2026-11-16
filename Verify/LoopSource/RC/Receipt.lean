import Contracts.VerifyCounter.LoopVC
import Verify.LoopSource.RC.Gcd.Obligations
import Verify.LoopSource.RC.HeadlineCheck

/-!
# Receipt: the loop route's theorems, their axioms, and what the headline rests on

Building this module checks, by `#guard_msgs`, that each theorem depends only on Lean's three
standard axioms, and that `body_runs_vc` (bump's body runs as its tree, `BodyRuns`, the source
semantics' statement) reaches solar-verify's kernel-checked obligations (`obs_valid`) and the
emitted loop-head map (`Verify.LoopSource.RC.Counter.M`) through its proof.
-/

open Lean Elab Command in
/-- `#reaches a b`: the constant `b` occurs in the transitive closure of the constants `a`'s type
and proof use. -/
elab "#reaches " a:ident b:ident : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := [a.getId]
  let mut found := false
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if n == b.getId then
      found := true
      break
    if let some ci := env.find? n then
      let body := match ci with
        | .thmInfo v => v.value.getUsedConstants
        | .defnInfo v => v.value.getUsedConstants
        | .opaqueInfo v => v.value.getUsedConstants
        | _ => #[]
      todo := (ci.type.getUsedConstants ++ body).toList ++ todo
  logInfo m!"{a.getId} reaches {b.getId}: {found}"

/-- info: 'Contracts.VerifyCounter.LoopVC.body_runs_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.body_runs_vc

/-- info: 'Contracts.VerifyCounter.LoopVC.obl_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.obl_vc

/-- info: 'Contracts.VerifyCounter.LoopVC.consec_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.consec_corr

/-- info: 'Contracts.VerifyCounter.LoopVC.pre_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.pre_witness

/-- info: 'Contracts.VerifyCounter.LoopVC.init_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.init_vc

/-- info: 'Contracts.VerifyCounter.LoopVC.consec_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.consec_vc

/-- info: 'Contracts.VerifyCounter.LoopVC.decr_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.decr_vc

/-- info: 'Contracts.VerifyCounter.LoopVC.post_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Contracts.VerifyCounter.LoopVC.post_vc

/-- info: 'SolidCore.Verify.LoopMap.Corr.eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidCore.Verify.LoopMap.Corr.eval

/-- info: 'SolidCore.Verify.LoopMap.holds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidCore.Verify.LoopMap.holds_eq

/-- info: 'SolidCore.Verify.VC.checkLoop_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidCore.Verify.VC.checkLoop_sound

/-- info: 'Verify.LoopSource.RC.Counter.obs_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.RC.Counter.obs_valid

/-- info: 'Verify.LoopSource.RC.Gcd.obs_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.RC.Gcd.obs_valid

/-- info: Contracts.VerifyCounter.LoopVC.body_runs_vc reaches Verify.LoopSource.RC.Counter.obs_valid: true -/
#guard_msgs in
#reaches Contracts.VerifyCounter.LoopVC.body_runs_vc Verify.LoopSource.RC.Counter.obs_valid

/-- info: Contracts.VerifyCounter.LoopVC.body_runs_vc reaches Verify.LoopSource.RC.Counter.M: true -/
#guard_msgs in
#reaches Contracts.VerifyCounter.LoopVC.body_runs_vc Verify.LoopSource.RC.Counter.M

/-- info: Contracts.VerifyCounter.LoopVC.body_runs_vc reaches Verify.LoopSource.RC.Counter.script: true -/
#guard_msgs in
#reaches Contracts.VerifyCounter.LoopVC.body_runs_vc Verify.LoopSource.RC.Counter.script


import Verify.LoopSource.RC.Headline
import Verify.LoopSource.Proof.LoopVC

/-!
# The proof against the independently stated headline

`Verify.LoopSource.RC.Headline` states the expected headline without the proof; this module checks,
in the kernel, that `Contracts.VerifyCounter.LoopVC.body_runs_vc` has exactly that type, and that the
statement rests only on Lean's three standard axioms.
-/

example : Verify.LoopSource.RC.Headline.CounterBumpLoopHeadline :=
  Contracts.VerifyCounter.LoopVC.body_runs_vc

/-- The headline, proved by the loop route. -/
theorem Verify.LoopSource.RC.Headline.counter_bump_loop :
    Verify.LoopSource.RC.Headline.CounterBumpLoopHeadline :=
  Contracts.VerifyCounter.LoopVC.body_runs_vc

/-- info: 'Verify.LoopSource.RC.Headline.counter_bump_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.RC.Headline.counter_bump_loop

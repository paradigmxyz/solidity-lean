import SolidCore.Solidity.Interpreter

/-!
# Lane F baseline: `1 ** e` by unfolding `checkedExp`

Same statement as `Verify.Eval.F.fixture_one_pow` (CheckedExp.lean). Without the bridge, the
direct route unfolds `checkedExp`, `natPowCapped` and `natPowMod` into `expBySquaring` with
257 fuel on a symbolic exponent. `simp` keeps splitting on `e = 0` and `e % 2 = 1` down the
257 levels and hits the default heartbeat limit (200000). The file passes: the timeout is
asserted by `#guard_msgs`, and its receipt records the time to the timeout. The only other route is to re-prove the induction
of `expBySquaring_eq` inline.
-/

open SolidCore.Solidity.Source

/- An `example` under `#guard_msgs`: the timeout is checked and nothing with `sorryAx` enters the
environment. The heartbeat limit is pinned to Lean's default so the message is stable. -/
/--
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (error, drop warning, drop info) in
set_option maxHeartbeats 200000 in
example (checked : Bool) (e : Word) : checkedExp checked 1 e = .ok 1 := by
  unfold checkedExp natPowCapped natPowMod expFuel
  simp [expBySquaring]

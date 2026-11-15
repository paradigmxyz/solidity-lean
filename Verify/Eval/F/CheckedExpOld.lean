import SolidCore.Solidity.Interpreter

/-!
# Lane F baseline: `1 ** e` by unfolding `checkedExp`

Same statement as `Verify.Eval.F.fixture_one_pow` (CheckedExp.lean). Without the bridge, the
direct route unfolds `checkedExp`, `natPowCapped` and `natPowMod` into `expBySquaring` with
257 fuel on a symbolic exponent. `simp` keeps splitting on `e = 0` and `e % 2 = 1` down the
257 levels and hits the default heartbeat limit (200000). This file is EXPECTED TO FAIL; its
receipt records the time to the timeout. The only other route is to re-prove the induction
of `expBySquaring_eq` inline.
-/

open SolidCore.Solidity.Source

theorem fixture_one_pow_old (checked : Bool) (e : Word) : checkedExp checked 1 e = .ok 1 := by
  unfold checkedExp natPowCapped natPowMod expFuel
  simp [expBySquaring]

import SolarTV.Word

/-!
# Lane F baseline: the same concrete power, by unfolding `SolarTV.Word.power`

Same statement as `Verify.Eval.F.fixture_power_big` (Power.lean). Unfolding the well-founded
definition 256 times overflows the default `maxRecDepth` (512); with it raised, `simp` gets
there and the kernel re-checks every BitVec multiplication. `decide` and `rfl` do not reduce
the well-founded recursion at all, and `power_eq_pow` leads to `BitVec.pow`'s 2^255 steps.
-/

namespace Verify.Eval.F.Old

open SolarTV.Word

/- At the default `maxRecDepth` (512) the same `simp [power]` fails with "maximum recursion
depth has been reached" (observed; not guarded here because that error escapes
`fail_if_success`). -/
set_option maxRecDepth 100000 in
theorem fixture_power_big_old :
    power (3#256) (2 ^ 255 + 12345) =
      42433521838168360224194192642435598547821817833025597527132038330417986287139#256 := by
  simp [power]

end Verify.Eval.F.Old

/-- info: 'Verify.Eval.F.Old.fixture_power_big_old' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.Old.fixture_power_big_old

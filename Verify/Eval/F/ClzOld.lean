import SolidCore.Solidity.Shared.Word

/-!
# Lane F baseline: `clzWord` facts by unfolding the 256-step scan

Same statements as Clz.lean's `clzWord_le` and `fixture_clz_top`, without the bridge to core's
`BitVec.clz`: unfold `clzWordAux` 256 times and split on every bit test.
-/

namespace Verify.Eval.F.ClzOld

open SolidCore.Solidity.Shared

set_option maxRecDepth 100000 in
theorem clzWord_le_old (v : Nat) : clzWord v ≤ 256 := by
  unfold clzWord
  refine Nat.le_trans (Nat.mod_le _ _) ?_
  simp only [clzWordAux]
  split_ifs <;> omega

theorem fixture_clz_concrete_old : clzWord (2 ^ 200 + 7) = 55 := by decide

end Verify.Eval.F.ClzOld

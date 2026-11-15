import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Memory16: the definitions of Verify/Eval/A/Fixtures/Memory16.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 79653b03c6f2744b), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Memory16

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM (List Nat) := do
  let x ← sload 0
  sstore 100 (x + 0)
  sstore 101 (x + 1)
  sstore 102 (x + 2)
  sstore 103 (x + 3)
  sstore 104 (x + 4)
  sstore 105 (x + 5)
  sstore 106 (x + 6)
  let r0 ← sload 100
  let r1 ← sload 101
  let r2 ← sload 102
  let r3 ← sload 103
  let r4 ← sload 104
  let r5 ← sload 105
  let r6 ← sload 106
  pure [r0, r1, r2, r3, r4, r5, r6]

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop),
    wp model (fun out _ _ => out = [(s 0 + 0) % 2 ^ 256, (s 0 + 1) % 2 ^ 256, (s 0 + 2) % 2 ^ 256, (s 0 + 3) % 2 ^ 256, (s 0 + 4) % 2 ^ 256, (s 0 + 5) % 2 ^ 256, (s 0 + 6) % 2 ^ 256]) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Memory16

#print axioms Verify.Eval.D.Scale.Memory16.vcgen_new
#proof_stats Verify.Eval.D.Scale.Memory16.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Memory16.vcgen_new

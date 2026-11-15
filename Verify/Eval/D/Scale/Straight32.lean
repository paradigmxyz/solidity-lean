import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Straight32: the definitions of Verify/Eval/A/Fixtures/Straight32.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix aaea55b51b5eba23), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Straight32

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM Unit := do
  let v0 ← sload 0
  sstore 1 (v0 + 1)
  let v1 ← sload 1
  sstore 2 (v1 + 1)
  let v2 ← sload 2
  sstore 3 (v2 + 1)
  let v3 ← sload 3
  sstore 4 (v3 + 1)
  let v4 ← sload 4
  sstore 5 (v4 + 1)
  let v5 ← sload 5
  sstore 6 (v5 + 1)
  let v6 ← sload 6
  sstore 7 (v6 + 1)
  let v7 ← sload 7
  sstore 8 (v7 + 1)
  let v8 ← sload 8
  sstore 9 (v8 + 1)
  let v9 ← sload 9
  sstore 10 (v9 + 1)
  let v10 ← sload 10
  sstore 11 (v10 + 1)
  let v11 ← sload 11
  sstore 12 (v11 + 1)
  let v12 ← sload 12
  sstore 13 (v12 + 1)
  let v13 ← sload 13
  sstore 14 (v13 + 1)
  let v14 ← sload 14
  sstore 15 (v14 + 1)
  let v15 ← sload 15
  sstore 16 (v15 + 1)

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop), s 0 < 2 ^ 128 →
    wp model (fun _ _ s' => s' 16 = s 0 + 16) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Straight32

#print axioms Verify.Eval.D.Scale.Straight32.vcgen_new
#proof_stats Verify.Eval.D.Scale.Straight32.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Straight32.vcgen_new

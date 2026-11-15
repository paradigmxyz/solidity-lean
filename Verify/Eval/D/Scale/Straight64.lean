import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Straight64: the definitions of Verify/Eval/A/Fixtures/Straight64.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix e7c1ecb8e3260532), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Straight64

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
  let v16 ← sload 16
  sstore 17 (v16 + 1)
  let v17 ← sload 17
  sstore 18 (v17 + 1)
  let v18 ← sload 18
  sstore 19 (v18 + 1)
  let v19 ← sload 19
  sstore 20 (v19 + 1)
  let v20 ← sload 20
  sstore 21 (v20 + 1)
  let v21 ← sload 21
  sstore 22 (v21 + 1)
  let v22 ← sload 22
  sstore 23 (v22 + 1)
  let v23 ← sload 23
  sstore 24 (v23 + 1)
  let v24 ← sload 24
  sstore 25 (v24 + 1)
  let v25 ← sload 25
  sstore 26 (v25 + 1)
  let v26 ← sload 26
  sstore 27 (v26 + 1)
  let v27 ← sload 27
  sstore 28 (v27 + 1)
  let v28 ← sload 28
  sstore 29 (v28 + 1)
  let v29 ← sload 29
  sstore 30 (v29 + 1)
  let v30 ← sload 30
  sstore 31 (v30 + 1)
  let v31 ← sload 31
  sstore 32 (v31 + 1)

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop), s 0 < 2 ^ 128 →
    wp model (fun _ _ s' => s' 32 = s 0 + 32) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Straight64

#print axioms Verify.Eval.D.Scale.Straight64.vcgen_new
#proof_stats Verify.Eval.D.Scale.Straight64.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Straight64.vcgen_new

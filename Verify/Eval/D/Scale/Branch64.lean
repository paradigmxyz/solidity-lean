import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Branch64: the definitions of Verify/Eval/A/Fixtures/Branch64.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 29f81ebec15f6c81), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Branch64

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM Unit := do
  let v0 ← sload 0
  if v0 < 2 ^ 255 then pure () else revert [0]
  sstore 1000 (v0 + v0)
  let v1 ← sload 1
  if v1 < 2 ^ 255 then pure () else revert [1]
  sstore 1001 (v1 + v1)
  let v2 ← sload 2
  if v2 < 2 ^ 255 then pure () else revert [2]
  sstore 1002 (v2 + v2)
  let v3 ← sload 3
  if v3 < 2 ^ 255 then pure () else revert [3]
  sstore 1003 (v3 + v3)
  let v4 ← sload 4
  if v4 < 2 ^ 255 then pure () else revert [4]
  sstore 1004 (v4 + v4)
  let v5 ← sload 5
  if v5 < 2 ^ 255 then pure () else revert [5]
  sstore 1005 (v5 + v5)
  let v6 ← sload 6
  if v6 < 2 ^ 255 then pure () else revert [6]
  sstore 1006 (v6 + v6)
  let v7 ← sload 7
  if v7 < 2 ^ 255 then pure () else revert [7]
  sstore 1007 (v7 + v7)
  let v8 ← sload 8
  if v8 < 2 ^ 255 then pure () else revert [8]
  sstore 1008 (v8 + v8)
  let v9 ← sload 9
  if v9 < 2 ^ 255 then pure () else revert [9]
  sstore 1009 (v9 + v9)
  let v10 ← sload 10
  if v10 < 2 ^ 255 then pure () else revert [10]
  sstore 1010 (v10 + v10)
  let v11 ← sload 11
  if v11 < 2 ^ 255 then pure () else revert [11]
  sstore 1011 (v11 + v11)
  let v12 ← sload 12
  if v12 < 2 ^ 255 then pure () else revert [12]
  sstore 1012 (v12 + v12)
  let v13 ← sload 13
  if v13 < 2 ^ 255 then pure () else revert [13]
  sstore 1013 (v13 + v13)
  let v14 ← sload 14
  if v14 < 2 ^ 255 then pure () else revert [14]
  sstore 1014 (v14 + v14)
  let v15 ← sload 15
  if v15 < 2 ^ 255 then pure () else revert [15]
  sstore 1015 (v15 + v15)
  let v16 ← sload 16
  if v16 < 2 ^ 255 then pure () else revert [16]
  sstore 1016 (v16 + v16)
  let v17 ← sload 17
  if v17 < 2 ^ 255 then pure () else revert [17]
  sstore 1017 (v17 + v17)
  let v18 ← sload 18
  if v18 < 2 ^ 255 then pure () else revert [18]
  sstore 1018 (v18 + v18)
  let v19 ← sload 19
  if v19 < 2 ^ 255 then pure () else revert [19]
  sstore 1019 (v19 + v19)
  let v20 ← sload 20
  if v20 < 2 ^ 255 then pure () else revert [20]
  sstore 1020 (v20 + v20)

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop), (∀ e, herr e) →
    wp model (fun _ _ s' =>
      s' 1000 = 2 * s 0 ∧
      s' 1001 = 2 * s 1 ∧
      s' 1002 = 2 * s 2 ∧
      s' 1003 = 2 * s 3 ∧
      s' 1004 = 2 * s 4 ∧
      s' 1005 = 2 * s 5 ∧
      s' 1006 = 2 * s 6 ∧
      s' 1007 = 2 * s 7 ∧
      s' 1008 = 2 * s 8 ∧
      s' 1009 = 2 * s 9 ∧
      s' 1010 = 2 * s 10 ∧
      s' 1011 = 2 * s 11 ∧
      s' 1012 = 2 * s 12 ∧
      s' 1013 = 2 * s 13 ∧
      s' 1014 = 2 * s 14 ∧
      s' 1015 = 2 * s 15 ∧
      s' 1016 = 2 * s 16 ∧
      s' 1017 = 2 * s 17 ∧
      s' 1018 = 2 * s 18 ∧
      s' 1019 = 2 * s 19 ∧
      s' 1020 = 2 * s 20) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Branch64

#print axioms Verify.Eval.D.Scale.Branch64.vcgen_new
#proof_stats Verify.Eval.D.Scale.Branch64.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Branch64.vcgen_new

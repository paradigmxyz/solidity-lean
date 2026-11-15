import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Branch16: the definitions of Verify/Eval/A/Fixtures/Branch16.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix df7709403db2663c), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Branch16

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

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop), (∀ e, herr e) →
    wp model (fun _ _ s' =>
      s' 1000 = 2 * s 0 ∧
      s' 1001 = 2 * s 1 ∧
      s' 1002 = 2 * s 2 ∧
      s' 1003 = 2 * s 3 ∧
      s' 1004 = 2 * s 4) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Branch16

#print axioms Verify.Eval.D.Scale.Branch16.vcgen_new
#proof_stats Verify.Eval.D.Scale.Branch16.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Branch16.vcgen_new

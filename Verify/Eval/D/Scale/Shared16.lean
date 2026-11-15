import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Shared16: the definitions of Verify/Eval/A/Fixtures/Shared16.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 6b9f8a271df62173), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Shared16

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def model : SolM Unit := do
  let x ← sload 0
  sstore 1 ((x + 1) * (x + 2) + x * 3)
  sstore 2 ((x + 1) * (x + 2) + x * 3)
  sstore 3 ((x + 1) * (x + 2) + x * 3)
  sstore 4 ((x + 1) * (x + 2) + x * 3)
  sstore 5 ((x + 1) * (x + 2) + x * 3)
  sstore 6 ((x + 1) * (x + 2) + x * 3)
  sstore 7 ((x + 1) * (x + 2) + x * 3)
  sstore 8 ((x + 1) * (x + 2) + x * 3)
  sstore 9 ((x + 1) * (x + 2) + x * 3)
  sstore 10 ((x + 1) * (x + 2) + x * 3)
  sstore 11 ((x + 1) * (x + 2) + x * 3)
  sstore 12 ((x + 1) * (x + 2) + x * 3)
  sstore 13 ((x + 1) * (x + 2) + x * 3)
  sstore 14 ((x + 1) * (x + 2) + x * 3)
  sstore 15 ((x + 1) * (x + 2) + x * 3)

def stmt : Prop :=
  ∀ (s : Storage) (herr : Revert → Prop),
    wp model (fun _ _ s' =>
      s' 1 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 2 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 3 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 4 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 5 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 6 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 7 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 8 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 9 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 10 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 11 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 12 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 13 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 14 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 15 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Shared16

#print axioms Verify.Eval.D.Scale.Shared16.vcgen_new
#proof_stats Verify.Eval.D.Scale.Shared16.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Shared16.vcgen_new

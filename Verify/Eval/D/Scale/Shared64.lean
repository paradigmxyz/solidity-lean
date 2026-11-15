import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture Shared64: the definitions of Verify/Eval/A/Fixtures/Shared64.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 044cb752688011e3), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.Shared64

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
  sstore 16 ((x + 1) * (x + 2) + x * 3)
  sstore 17 ((x + 1) * (x + 2) + x * 3)
  sstore 18 ((x + 1) * (x + 2) + x * 3)
  sstore 19 ((x + 1) * (x + 2) + x * 3)
  sstore 20 ((x + 1) * (x + 2) + x * 3)
  sstore 21 ((x + 1) * (x + 2) + x * 3)
  sstore 22 ((x + 1) * (x + 2) + x * 3)
  sstore 23 ((x + 1) * (x + 2) + x * 3)
  sstore 24 ((x + 1) * (x + 2) + x * 3)
  sstore 25 ((x + 1) * (x + 2) + x * 3)
  sstore 26 ((x + 1) * (x + 2) + x * 3)
  sstore 27 ((x + 1) * (x + 2) + x * 3)
  sstore 28 ((x + 1) * (x + 2) + x * 3)
  sstore 29 ((x + 1) * (x + 2) + x * 3)
  sstore 30 ((x + 1) * (x + 2) + x * 3)
  sstore 31 ((x + 1) * (x + 2) + x * 3)
  sstore 32 ((x + 1) * (x + 2) + x * 3)
  sstore 33 ((x + 1) * (x + 2) + x * 3)
  sstore 34 ((x + 1) * (x + 2) + x * 3)
  sstore 35 ((x + 1) * (x + 2) + x * 3)
  sstore 36 ((x + 1) * (x + 2) + x * 3)
  sstore 37 ((x + 1) * (x + 2) + x * 3)
  sstore 38 ((x + 1) * (x + 2) + x * 3)
  sstore 39 ((x + 1) * (x + 2) + x * 3)
  sstore 40 ((x + 1) * (x + 2) + x * 3)
  sstore 41 ((x + 1) * (x + 2) + x * 3)
  sstore 42 ((x + 1) * (x + 2) + x * 3)
  sstore 43 ((x + 1) * (x + 2) + x * 3)
  sstore 44 ((x + 1) * (x + 2) + x * 3)
  sstore 45 ((x + 1) * (x + 2) + x * 3)
  sstore 46 ((x + 1) * (x + 2) + x * 3)
  sstore 47 ((x + 1) * (x + 2) + x * 3)
  sstore 48 ((x + 1) * (x + 2) + x * 3)
  sstore 49 ((x + 1) * (x + 2) + x * 3)
  sstore 50 ((x + 1) * (x + 2) + x * 3)
  sstore 51 ((x + 1) * (x + 2) + x * 3)
  sstore 52 ((x + 1) * (x + 2) + x * 3)
  sstore 53 ((x + 1) * (x + 2) + x * 3)
  sstore 54 ((x + 1) * (x + 2) + x * 3)
  sstore 55 ((x + 1) * (x + 2) + x * 3)
  sstore 56 ((x + 1) * (x + 2) + x * 3)
  sstore 57 ((x + 1) * (x + 2) + x * 3)
  sstore 58 ((x + 1) * (x + 2) + x * 3)
  sstore 59 ((x + 1) * (x + 2) + x * 3)
  sstore 60 ((x + 1) * (x + 2) + x * 3)
  sstore 61 ((x + 1) * (x + 2) + x * 3)
  sstore 62 ((x + 1) * (x + 2) + x * 3)
  sstore 63 ((x + 1) * (x + 2) + x * 3)

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
      s' 15 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 16 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 17 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 18 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 19 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 20 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 21 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 22 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 23 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 24 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 25 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 26 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 27 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 28 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 29 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 30 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 31 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 32 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 33 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 34 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 35 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 36 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 37 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 38 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 39 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 40 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 41 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 42 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 43 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 44 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 45 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 46 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 47 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 48 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 49 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 50 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 51 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 52 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 53 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 54 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 55 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 56 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 57 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 58 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 59 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 60 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 61 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 62 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256 ∧
      s' 63 = ((s 0 + 1) * (s 0 + 2) + s 0 * 3) % 2 ^ 256) herr s

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro s herr
  intros
  refine loom_wp_of_triple_pt ?_
  vcgen [model] with finish

end Verify.Eval.D.Scale.Shared64

#print axioms Verify.Eval.D.Scale.Shared64.vcgen_new
#proof_stats Verify.Eval.D.Scale.Shared64.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.Shared64.vcgen_new

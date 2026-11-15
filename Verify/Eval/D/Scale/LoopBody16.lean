import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture LoopBody16: the definitions of Verify/Eval/A/Fixtures/LoopBody16.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix ffb804a45ac0083a), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.LoopBody16

open SolidCore.Verify SolidCore.Verify.Eval.D
open scoped Std.WP

open SolidCore.Verify

def body (i : Nat) : SolM Nat := do
  let c0 ← sload 0
  sstore 0 (c0 + 1)
  let c1 ← sload 1
  sstore 1 (c1 + 1)
  let c2 ← sload 2
  sstore 2 (c2 + 1)
  let c3 ← sload 3
  sstore 3 (c3 + 1)
  let c4 ← sload 4
  sstore 4 (c4 + 1)
  let c5 ← sload 5
  sstore 5 (c5 + 1)
  let c6 ← sload 6
  sstore 6 (c6 + 1)
  let c7 ← sload 7
  sstore 7 (c7 + 1)
  pure (i + 1)

/-- The supplied invariant: `i ≤ N`, every counter advanced by `i`, and the bound the
caller established. -/
def inv (N : Nat) (s : Storage) (i : Nat) : Assn := fun _ s' =>
      i ≤ N ∧
      s' 0 = s 0 + i ∧
      s' 1 = s 1 + i ∧
      s' 2 = s 2 + i ∧
      s' 3 = s 3 + i ∧
      s' 4 = s 4 + i ∧
      s' 5 = s 5 + i ∧
      s' 6 = s 6 + i ∧
      s' 7 = s 7 + i ∧
      s 0 + N < 2 ^ 256 ∧
      s 1 + N < 2 ^ 256 ∧
      s 2 + N < 2 ^ 256 ∧
      s 3 + N < 2 ^ 256 ∧
      s 4 + N < 2 ^ 256 ∧
      s 5 + N < 2 ^ 256 ∧
      s 6 + N < 2 ^ 256 ∧
      s 7 + N < 2 ^ 256

/-- The supplied variant. -/
def variant (N i : Nat) : Nat := N - i

def stmt : Prop :=
  ∀ (N : Nat) (s : Storage) (i : Nat), decide (i < N) = true →
    triple (inv N s i) (body i) (fun i' => inv N s i' ⊓ ⌜variant N i' < variant N i⌝)

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro N s i hi herr s' hinv
  refine loom_wp_of_triple_pt ?_
  simp only [inv] at hinv
  vcgen [body] <;> simp [inv, variant, LE.pure, ite_apply] at * <;> grind

end Verify.Eval.D.Scale.LoopBody16

#print axioms Verify.Eval.D.Scale.LoopBody16.vcgen_new
#proof_stats Verify.Eval.D.Scale.LoopBody16.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.LoopBody16.vcgen_new

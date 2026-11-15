import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture LoopBody32: the definitions of Verify/Eval/A/Fixtures/LoopBody32.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 5dac223f15228ff1), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.LoopBody32

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
  let c8 ← sload 8
  sstore 8 (c8 + 1)
  let c9 ← sload 9
  sstore 9 (c9 + 1)
  let c10 ← sload 10
  sstore 10 (c10 + 1)
  let c11 ← sload 11
  sstore 11 (c11 + 1)
  let c12 ← sload 12
  sstore 12 (c12 + 1)
  let c13 ← sload 13
  sstore 13 (c13 + 1)
  let c14 ← sload 14
  sstore 14 (c14 + 1)
  let c15 ← sload 15
  sstore 15 (c15 + 1)
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
      s' 8 = s 8 + i ∧
      s' 9 = s 9 + i ∧
      s' 10 = s 10 + i ∧
      s' 11 = s 11 + i ∧
      s' 12 = s 12 + i ∧
      s' 13 = s 13 + i ∧
      s' 14 = s 14 + i ∧
      s' 15 = s 15 + i ∧
      s 0 + N < 2 ^ 256 ∧
      s 1 + N < 2 ^ 256 ∧
      s 2 + N < 2 ^ 256 ∧
      s 3 + N < 2 ^ 256 ∧
      s 4 + N < 2 ^ 256 ∧
      s 5 + N < 2 ^ 256 ∧
      s 6 + N < 2 ^ 256 ∧
      s 7 + N < 2 ^ 256 ∧
      s 8 + N < 2 ^ 256 ∧
      s 9 + N < 2 ^ 256 ∧
      s 10 + N < 2 ^ 256 ∧
      s 11 + N < 2 ^ 256 ∧
      s 12 + N < 2 ^ 256 ∧
      s 13 + N < 2 ^ 256 ∧
      s 14 + N < 2 ^ 256 ∧
      s 15 + N < 2 ^ 256

/-- The supplied variant. -/
def variant (N i : Nat) : Nat := N - i

def stmt : Prop :=
  ∀ (N : Nat) (s : Storage) (i : Nat), decide (i < N) = true →
    triple (inv N s i) (body i) (fun i' => inv N s i' ⊓ ⌜variant N i' < variant N i⌝)

#timed theorem vcgen_new : stmt := by
  unfold stmt
  intro N s i hi herr s' hinv
  refine loom_wp_of_triple_pt ?_
  simp only [inv, variant, LE.pure] at hinv ⊢
  vcgen [body] with finish

end Verify.Eval.D.Scale.LoopBody32

#print axioms Verify.Eval.D.Scale.LoopBody32.vcgen_new
#proof_stats Verify.Eval.D.Scale.LoopBody32.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.LoopBody32.vcgen_new

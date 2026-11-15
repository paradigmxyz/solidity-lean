import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure

/-! Lane D on lane A's fixture LoopBody64: the definitions of Verify/Eval/A/Fixtures/LoopBody64.lean copied
verbatim by scripts/eval/gen_d_scale.py (sha256 prefix 5e6062d47e045103), stmt proved with vcgen. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

namespace Verify.Eval.D.Scale.LoopBody64

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
  let c16 ← sload 16
  sstore 16 (c16 + 1)
  let c17 ← sload 17
  sstore 17 (c17 + 1)
  let c18 ← sload 18
  sstore 18 (c18 + 1)
  let c19 ← sload 19
  sstore 19 (c19 + 1)
  let c20 ← sload 20
  sstore 20 (c20 + 1)
  let c21 ← sload 21
  sstore 21 (c21 + 1)
  let c22 ← sload 22
  sstore 22 (c22 + 1)
  let c23 ← sload 23
  sstore 23 (c23 + 1)
  let c24 ← sload 24
  sstore 24 (c24 + 1)
  let c25 ← sload 25
  sstore 25 (c25 + 1)
  let c26 ← sload 26
  sstore 26 (c26 + 1)
  let c27 ← sload 27
  sstore 27 (c27 + 1)
  let c28 ← sload 28
  sstore 28 (c28 + 1)
  let c29 ← sload 29
  sstore 29 (c29 + 1)
  let c30 ← sload 30
  sstore 30 (c30 + 1)
  let c31 ← sload 31
  sstore 31 (c31 + 1)
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
      s' 16 = s 16 + i ∧
      s' 17 = s 17 + i ∧
      s' 18 = s 18 + i ∧
      s' 19 = s 19 + i ∧
      s' 20 = s 20 + i ∧
      s' 21 = s 21 + i ∧
      s' 22 = s 22 + i ∧
      s' 23 = s 23 + i ∧
      s' 24 = s 24 + i ∧
      s' 25 = s 25 + i ∧
      s' 26 = s 26 + i ∧
      s' 27 = s 27 + i ∧
      s' 28 = s 28 + i ∧
      s' 29 = s 29 + i ∧
      s' 30 = s 30 + i ∧
      s' 31 = s 31 + i ∧
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
      s 15 + N < 2 ^ 256 ∧
      s 16 + N < 2 ^ 256 ∧
      s 17 + N < 2 ^ 256 ∧
      s 18 + N < 2 ^ 256 ∧
      s 19 + N < 2 ^ 256 ∧
      s 20 + N < 2 ^ 256 ∧
      s 21 + N < 2 ^ 256 ∧
      s 22 + N < 2 ^ 256 ∧
      s 23 + N < 2 ^ 256 ∧
      s 24 + N < 2 ^ 256 ∧
      s 25 + N < 2 ^ 256 ∧
      s 26 + N < 2 ^ 256 ∧
      s 27 + N < 2 ^ 256 ∧
      s 28 + N < 2 ^ 256 ∧
      s 29 + N < 2 ^ 256 ∧
      s 30 + N < 2 ^ 256 ∧
      s 31 + N < 2 ^ 256

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

end Verify.Eval.D.Scale.LoopBody64

#print axioms Verify.Eval.D.Scale.LoopBody64.vcgen_new
#proof_stats Verify.Eval.D.Scale.LoopBody64.vcgen_new
#kernel_recheck Verify.Eval.D.Scale.LoopBody64.vcgen_new

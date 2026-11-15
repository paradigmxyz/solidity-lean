import Verify.Eval.D.Bridge
import Verify.Eval.Common.Measure
import Verify.CounterBump

/-!
# Lane D: robustness to a small source change

`bump(n)` with its `require` changed from `count + n <= limit` to `count + n < limit`
(`model'`, statement `BumpStmt'`), each engine's proof text otherwise unchanged:

* the repository's hand proof (`bump_old` in `Loop.lean`) with only `model` renamed: it fails
  (kept below inside `fail_if_success`, so this file checks that it still fails);
* `vcgen` with the same annotated invariant: unchanged, it passes.
-/

namespace SolidCore.Verify.Eval.D.Robust

open SolidCore.Verify SolidCore.Refinement SolidCore.Verify.CounterBump
open scoped Std.WP

set_option experimental.vcgen true
set_option grind.warning false
set_option Elab.async false

/-- `bump` with `require(count + n < limit, "over")`. -/
def model' (n : Nat) : SolM (List Nat) := do
  let c ← sload 0
  let lim ← sload 1
  if c + n < 2 ^ 256 then pure () else revert (panic 0x11)
  if c + n < lim then pure () else revert (errorString "over")
  let _ ← whileM (fun i => decide (i < n)) body (n + 1) 0
  pure []

abbrev BumpStmt' : Prop :=
  ∀ (n : Nat) (s : Storage) (herr : Revert → Prop),
    (s 0 + n < 2 ^ 256 → ¬ s 0 + n < s 1 → herr (errorString "over")) →
    (¬ s 0 + n < 2 ^ 256 → herr (panic 0x11)) →
    wp (model' n)
      (fun _ _ s' => s' 0 = s 0 + n ∧ ∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k)
      herr s

/-- The old proof text, with `model` renamed to `model'` and nothing else changed, fails. -/
example : True := by
  fail_if_success
    have : BumpStmt' := by
      intro n s herr hover hpanic
      simp only [model', wp_bind, wp_sload, wp_ite, wp_pure, wp_revert]
      by_cases hb : s 0 + n < 2 ^ 256
      · simp only [hb, ite_true]
        by_cases hl : s 0 + n ≤ s 1
        · simp only [hl, ite_true]
          have hloop := triple_whileM (fun i => decide (i < n)) body (inv n s) (variant n)
            (body_step n s) (n + 1) 0 (by simp [variant])
          have h0 : inv n s 0 herr s := ⟨Nat.zero_le _, by simp, fun _ _ => rfl, hb⟩
          have := wp_cons _ _ (fun (_ : Nat) => fun (_ : Revert → Prop) s' =>
              s' 0 = s 0 + n ∧ ∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k) ?_ herr s (hloop herr s h0)
          · simpa [wp_pure] using this
          · intro i herr' s' ⟨⟨hle, hc, hframe, _⟩, hdone⟩
            have hni : n ≤ i := by
              by_contra hne
              have : decide (i < n) = true := by simp; omega
              simp [LE.pure, this] at hdone
            exact ⟨by rw [hc]; congr 1; omega, hframe⟩
        · simp only [hl, ite_false]; exact hover hb hl
      · simp only [hb, ite_false]; exact hpanic hb
  trivial

abbrev annotInv (n : Nat) (s : Storage) (i : Nat) (s' : Storage) : Prop :=
  i ≤ n ∧ s' 0 = s 0 + i ∧ (∀ k, k % 2 ^ 256 ≠ 0 → s' k = s k) ∧ s 0 + n < 2 ^ 256

-- The `vcgen` proof text of `Loop.bump_new_annot`, with `model` renamed: it passes.
#timed theorem bump'_new : BumpStmt' := by
  intro n s herr hover hpanic
  refine loom_wp_of_triple_pt ?_
  vcgen [model', body, whileM_spec (inv := annotInv n s) (measure := fun i => n - i), annotInv]
    with finish

#print axioms bump'_new

end SolidCore.Verify.Eval.D.Robust

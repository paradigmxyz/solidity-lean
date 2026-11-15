import Verify.Eval.H.Mutation
import Verify.Eval.H.Expected

/-!
# Sibling isolation and the harness's own negative test (lane H)

* The harness reports a survivor: an equivalent mutant (`x < 10 → x ≤ 10` for `x < 10 → x < 11`)
  makes `#mutation_check` fail, which `#expect_reject` turns into a pass.
* Sibling isolation: two branches with contradictory assumptions (`h : x = 0` in one,
  `h : x ≠ 0` in the other) and a conditional rewrite whose side condition holds in one sibling
  only (`f_zero : x = 0 → f x = 5`). Each mutant is provable only if a fact of one sibling leaks into
  the other, so a script that keeps the branches apart must fail on it. Run with `grind` per
  branch, with one `grind` over the whole conjunction (it splits internally, sharing one E-graph
  across the split), and with `simp_all` per branch.
-/

namespace Verify.Eval.H.Sibling

#expect_reject in
#mutation_check "harness_detects_survivor" : ∀ x : Nat, x < 10 → x < 11
  rejects [ "equivalent" => ∀ x : Nat, x < 10 → x ≤ 10 ]
  using (intro x h; omega)

def f (x : Nat) : Nat := if x = 0 then 5 else 7
theorem f_zero (x : Nat) (h : x = 0) : f x = 5 := by simp [f, h]
theorem f_succ (x : Nat) (h : x ≠ 0) : f x = 7 := by simp [f, h]

#mutation_check "sibling_grind_per_branch" :
    ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7)
  rejects [
    "leak_eq_into_ne" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → x = 0),
    "leak_side_condition" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → f x = 5),
    "leak_ne_into_eq" => ∀ x : Nat, (x = 0 → 1 ≤ x) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7) ]
  using (intro x; constructor <;> intro h <;> grind [f_zero, f_succ])

#mutation_check "sibling_grind_one_session" :
    ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7)
  rejects [
    "leak_eq_into_ne" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → x = 0),
    "leak_side_condition" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → f x = 5),
    "leak_ne_into_eq" => ∀ x : Nat, (x = 0 → 1 ≤ x) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7) ]
  using (intro x; grind [f_zero, f_succ])

#mutation_check "sibling_simp_all_per_branch" :
    ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7)
  rejects [
    "leak_eq_into_ne" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → x = 0),
    "leak_side_condition" => ∀ x : Nat, (x = 0 → x + 1 = 1 ∧ f x = 5) ∧ (x ≠ 0 → f x = 5),
    "leak_ne_into_eq" => ∀ x : Nat, (x = 0 → 1 ≤ x) ∧ (x ≠ 0 → 1 ≤ x ∧ f x = 7) ]
  using (intro x; constructor <;> intro h <;> simp_all [f_zero, f_succ] <;> omega)

end Verify.Eval.H.Sibling

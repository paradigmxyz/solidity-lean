import Verify.Eval.H.Expected

/-! Tests for `Verify.Eval.H.Expected`: the positive checks pass, and every weakened statement is
rejected (`#expect_reject` fails the file if a check lets one through). -/

namespace Verify.Eval.H.ExpectedTest

def word (x : Nat) : Prop := x < 2 ^ 256

/-- The baseline. -/
theorem inc_old : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256 :=
  fun x h => ⟨h, by omega⟩

/-- The same statement, proved by another route. -/
theorem inc_new : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256 := by
  intro x h; exact ⟨h, by omega⟩

#same_statement inc_new inc_old
#same_imports inc_new inc_old
#expect_statement inc_new : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256
#statement_hash inc_new

/-- An abbreviation of the statement passes in `(defeq)` mode only. -/
abbrev IncStmt : Prop := ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256
theorem inc_abbrev : IncStmt := inc_old
#same_statement inc_abbrev inc_old (defeq)
#expect_reject in
#same_statement inc_abbrev inc_old

/-! Weakenings: each is a true theorem, so a tactic could close it, but none states the baseline. -/

-- a stronger hypothesis (the boundary moved: `x + 2` instead of `x + 1`)
theorem w_boundary : ∀ x : Nat, x + 2 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256 :=
  fun x h => ⟨by unfold word; omega, by omega⟩
-- `<` turned into `≤` in the conclusion
theorem w_le : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x ≤ 2 ^ 256 :=
  fun x h => ⟨h, by omega⟩
-- a dropped conjunct
theorem w_conj : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) := fun _ h => h
-- an extra hypothesis
theorem w_hyp : ∀ x : Nat, x < 10 → x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256 :=
  fun x _ h => ⟨h, by omega⟩
-- a narrowed quantifier (Fin instead of Nat)
theorem w_fin : ∀ x : Fin 10, x.val + 1 < 2 ^ 256 → word (x.val + 1) ∧ x.val < 2 ^ 256 :=
  fun x h => ⟨h, by omega⟩
-- a weaker statement hidden behind a `def` (not reducible), so `(defeq)` does not unfold it
def WeakStmt : Prop := ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1)
theorem w_hidden : WeakStmt := fun _ h => h

#expect_reject in #same_statement w_boundary inc_old
#expect_reject in #same_statement w_le inc_old
#expect_reject in #same_statement w_conj inc_old
#expect_reject in #same_statement w_hyp inc_old
#expect_reject in #same_statement w_fin inc_old
#expect_reject in #same_statement w_hidden inc_old
#expect_reject in #same_statement w_hidden inc_old (defeq)
#expect_reject in #same_statement w_boundary inc_old (defeq)
#expect_reject in
#expect_statement w_le : ∀ x : Nat, x + 1 < 2 ^ 256 → word (x + 1) ∧ x < 2 ^ 256

-- universe-polymorphic statements compare up to universe names
theorem id_old.{u} {α : Sort u} (a : α) : a = a := rfl
theorem id_new.{v} {α : Sort v} (a : α) : a = a := rfl
#same_statement id_new id_old
theorem id_weak {α : Type} (a : α) : a = a := rfl
#expect_reject in #same_statement id_weak id_old

-- the negative-test command itself fails when its command passes
#expect_reject in
#expect_reject in #same_statement inc_new inc_old

end Verify.Eval.H.ExpectedTest

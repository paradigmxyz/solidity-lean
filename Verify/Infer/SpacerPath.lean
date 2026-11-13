import Flex.Tactic.Tactics.Spacer
/-! Flex's spacer path: export CHC to z3 Spacer, import its model, instantiate the invariant,
    certify predicate heads (init/step) with grind; the remaining query VC (use) is closed by grind.
    No invariant is written by hand. -/
namespace FlexEval.SpacerPath

theorem counter_int :
    ∃ inv : Int → Int → Int → Int → Int → Prop,
      (∀ c0 n lim, 0 ≤ c0 → 0 ≤ n → 0 ≤ lim → c0 ≤ lim → c0 + n ≤ lim → inv c0 n lim 0 c0) ∧
      (∀ c0 n lim i c, inv c0 n lim i c → i < n → inv c0 n lim (i + 1) (c + 1)) ∧
      (∀ c0 n lim i c, inv c0 n lim i c → ¬ (i < n) → c = c0 + n ∧ c ≤ lim) := by
  spacer
  grind

theorem counter_u256 :
    ∃ inv : Int → Int → Int → Int → Int → Prop,
      (∀ c0 n lim, 0 ≤ c0 → c0 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → 0 ≤ n → n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → 0 ≤ lim → lim < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → c0 ≤ lim →
        0 ≤ c0 + n → c0 + n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → c0 + n ≤ lim → inv c0 n lim 0 c0) ∧
      (∀ c0 n lim i c, inv c0 n lim i c → i < n →
        0 ≤ c + 1 → c + 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → 0 ≤ i + 1 → i + 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → inv c0 n lim (i + 1) (c + 1)) ∧
      (∀ c0 n lim i c, inv c0 n lim i c → ¬ (i < n) → c = c0 + n ∧ c ≤ lim) := by
  spacer
  grind

theorem okwhile_int :
    ∃ inv : Int → Int → Prop,
      (∀ n, 0 ≤ n → inv n 0) ∧
      (∀ n i, inv n i → i < n → inv n (i + 1)) ∧
      (∀ n i, inv n i → ¬ (i < n) → i = n) := by
  spacer
  grind

theorem okwhile_u256 :
    ∃ inv : Int → Int → Prop,
      (∀ n, 0 ≤ n → n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → inv n 0) ∧
      (∀ n i, inv n i → i < n → 0 ≤ i + 1 → i + 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → inv n (i + 1)) ∧
      (∀ n i, inv n i → ¬ (i < n) → i = n) := by
  spacer
  grind

theorem drain_int :
    ∃ inv : Int → Int → Int → Prop,
      (∀ n, 0 ≤ n → inv n n 0) ∧
      (∀ n a b, inv n a b → a > 0 → inv n (a - 1) (b + 1)) ∧
      (∀ n a b, inv n a b → ¬ (a > 0) → b = n) := by
  spacer
  grind

theorem drain_u256 :
    ∃ inv : Int → Int → Int → Prop,
      (∀ n, 0 ≤ n → n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → inv n n 0) ∧
      (∀ n a b, inv n a b → a > 0 → 0 ≤ a - 1 → a - 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 → 0 ≤ b + 1 → b + 1 < 115792089237316195423570985008687907853269984665640564039457584007913129639936 →
        inv n (a - 1) (b + 1)) ∧
      (∀ n a b, inv n a b → ¬ (a > 0) → b = n) := by
  spacer
  grind

end FlexEval.SpacerPath
#print axioms FlexEval.SpacerPath.counter_int
#print axioms FlexEval.SpacerPath.counter_u256
#print axioms FlexEval.SpacerPath.okwhile_int
#print axioms FlexEval.SpacerPath.okwhile_u256
#print axioms FlexEval.SpacerPath.drain_int
#print axioms FlexEval.SpacerPath.drain_u256

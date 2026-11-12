import SolidCore.Refinement.Generic.Tree

/-!
# Packed storage fields on words

A field of `w` bits at bit offset `o` of its slot (`o + w ≤ 256`) reads as
`slot / 2 ^ o % 2 ^ w`, and SolidCore writes it by arithmetic (`wordReplaceBitRange`):
`slot - (slot / 2 ^ o % 2 ^ w) * 2 ^ o + (v % 2 ^ w) * 2 ^ o`. solar writes it with masks:
`or (and slot (clearMask o w)) (shl o v)`. `replace_eq` shows the two agree: the clearing mask
keeps the bits below `o` and from `o + w` on (`and_clearMask`), and the parts of the word,
on disjoint bits, add as they `or`.
-/

namespace SolidCore.Refinement.Generic

/-- The mask that clears bits `o` to `o + w - 1` of a word. -/
def clearMask (o w : Nat) : Nat := ((2 ^ (256 - (o + w)) - 1) <<< (o + w)) ||| (2 ^ o - 1)

theorem testBit_word {x : Nat} (hx : x < 2 ^ 256) {i : Nat} (hi : 256 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem testBit_clearMask (o w i : Nat) (h : o + w ≤ 256) :
    (clearMask o w).testBit i = (decide (i < o) || (decide (o + w ≤ i) && decide (i < 256))) := by
  simp only [clearMask, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < o
  · simp [h1]
  · by_cases h2 : o + w ≤ i
    · by_cases h3 : i < 256
      · simp [h1, h2, h3] <;> omega
      · simp [h1, h2, h3] <;> omega
    · simp [h1, h2] <;> omega

theorem clearMask_lt (o w : Nat) (h : o + w ≤ 256) : clearMask o w < 2 ^ 256 := by
  have : clearMask o w = clearMask o w % 2 ^ 256 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, testBit_clearMask o w i h]
    by_cases hi : i < 256
    · simp [hi]
    · simp [hi]; omega
  rw [this]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem and_clearMask {x : Nat} (hx : x < 2 ^ 256) (o w : Nat) (h : o + w ≤ 256) :
    x &&& clearMask o w = ((x >>> (o + w)) <<< (o + w)) ||| (x % 2 ^ o) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, testBit_clearMask o w i h, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases h1 : i < o
  · have : ¬ i ≥ o + w := by omega
    simp [h1, this]
  · by_cases h2 : o + w ≤ i
    · by_cases h3 : i < 256
      · have e : o + w + (i - (o + w)) = i := by omega
        simp [h1, h2, h3, e]
      · have e : o + w + (i - (o + w)) = i := by omega
        simp [h1, h2, h3, e, testBit_word hx (Nat.le_of_not_lt h3)]
    · have : ¬ i ≥ o + w := by omega
      simp [h1, h2, this]

/-- SolidCore's arithmetic write of a packed field is the masked write. -/
theorem replace_eq {cur : Nat} (hcur : cur < 2 ^ 256) (v o w : Nat) (h : o + w ≤ 256) :
    cur - cur / 2 ^ o % 2 ^ w * 2 ^ o + v % 2 ^ w * 2 ^ o =
      (cur &&& clearMask o w) ||| ((v % 2 ^ w) <<< o) := by
  rw [and_clearMask hcur o w h, Nat.or_assoc, Nat.or_comm (cur % 2 ^ o),
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos o))]
  have hV : v % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hlow : (v % 2 ^ w) <<< o + cur % 2 ^ o < 2 ^ (o + w) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    have h1 : cur % 2 ^ o < 2 ^ o := Nat.mod_lt _ (Nat.two_pow_pos o)
    have h2 : (v % 2 ^ w + 1) * 2 ^ o ≤ 2 ^ w * 2 ^ o := Nat.mul_le_mul_right _ hV
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ w)] at h2
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlow]
  have hdec : cur = 2 ^ (o + w) * (cur / 2 ^ (o + w)) + 2 ^ o * (cur / 2 ^ o % 2 ^ w) + cur % 2 ^ o := by
    have e1 := Nat.div_add_mod cur (2 ^ o)
    have e2 := Nat.div_add_mod (cur / 2 ^ o) (2 ^ w)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add] at e2
    have e4 : 2 ^ (o + w) * (cur / 2 ^ (o + w)) = 2 ^ o * (2 ^ w * (cur / 2 ^ (o + w))) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    generalize cur / 2 ^ (o + w) = H at e2 e4 ⊢
    generalize cur / 2 ^ o = q at e1 e2 ⊢
    rw [e4]
    rw [← e2, Nat.mul_add] at e1
    omega
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  generalize cur / 2 ^ (o + w) = H at hdec ⊢
  generalize cur / 2 ^ o % 2 ^ w = M at hdec ⊢
  rw [Nat.mul_comm M, Nat.mul_comm H]
  omega

theorem replace_lt {cur : Nat} (hcur : cur < 2 ^ 256) (v o w : Nat) (h : o + w ≤ 256) :
    (cur &&& clearMask o w) ||| ((v % 2 ^ w) <<< o) < 2 ^ 256 := by
  have h1 : cur &&& clearMask o w < 2 ^ 256 := Nat.lt_of_le_of_lt Nat.and_le_left hcur
  have h2 : (v % 2 ^ w) <<< o < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have hV : v % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have h3 : (v % 2 ^ w + 1) * 2 ^ o ≤ 2 ^ w * 2 ^ o := Nat.mul_le_mul_right _ hV
    have h4 : 2 ^ w * 2 ^ o ≤ 2 ^ 256 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h3
    have := Nat.two_pow_pos o
    omega
  exact Nat.or_lt_two_pow h1 h2

end SolidCore.Refinement.Generic

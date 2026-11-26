/-!
# Big-endian bytes of a word

SolidCore writes a word as `n` big-endian bytes by peeling its low byte off and recursing on
the rest. `bytesBE_eq_range` gives the bytes in closed form, the `i`th of them
`v / 256 ^ (n - 1 - i) % 256`, for any function with those recursion equations, so each of the
encoders' copies of the recursion needs only its two equations.
-/

namespace SolidCore.Refinement

theorem bytesBE_eq_range (f : Nat → Nat → List Nat) (h0 : ∀ v, f 0 v = [])
    (hs : ∀ n v, f (n + 1) v = f n (v / 256) ++ [v % 256]) (n v : Nat) :
    f n v = (List.range n).map fun i => v / 256 ^ (n - 1 - i) % 256 := by
  induction n generalizing v with
  | zero => exact h0 v
  | succ n ih =>
    rw [hs, ih, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show (n - 1 - i).succ = n + 1 - 1 - i by omega]
    · simp

end SolidCore.Refinement

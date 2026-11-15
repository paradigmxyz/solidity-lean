import Std.Tactic.BVDecide
-- needs the SAT certificate (checked with Lean.ofReduceBool), not just bv_decide's preprocessing
theorem bad_bv (x y : BitVec 8) : (x &&& 0x0F) + (x &&& 0xF0) = x ∧ x * y = y * x := by bv_decide

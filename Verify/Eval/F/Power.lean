import SolarTV.Word

/-!
# Lane F: `SolarTV.Word.power` is `Nat.powMod` on the bit vector's value

`SolarTV.Word.power` (tv/SolarTV/Word.lean:10) is EVM `EXP` by squaring on `BitVec w`, defined by
well-founded recursion. `SolarTV.Word.power_eq_pow` (tv/SolarTV/WordSafety.lean:19) already
says it is `base ^ n`, but core's `BitVec.pow` is repeated multiplication (Init/Data/BitVec/
Basic.lean:260), so a concrete large exponent is still out of reach. The bridge here goes to
Lean core's `Nat.powMod` (Init/Data/Nat/PowMod.lean, square-and-multiply, with the
`Nat.reducePowMod` simproc and `powMod_def : powMod b e m = b ^ e % m`).
No Mathlib: core and the module under test only. EXP wraps; there is no overflow check on
this path (the checked `**` of Solidity is SolidCore's `checkedExp`, see CheckedExp.lean).
-/

namespace Verify.Eval.F

open SolarTV.Word

/-- `SolarTV.Word.power_eq_pow` (tv/SolarTV/WordSafety.lean:19), re-proved here with the same
script because SolarTV.WordSafety has no .olean in the shared build yet. Once it does, import it
and drop this copy. -/
private theorem square_power' (base : BitVec width) (n : Nat) :
    (base * base) ^ n = base ^ (n + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [BitVec.pow_succ, ih]
    have h : n + 1 + (n + 1) = (n + n + 1) + 1 := by omega
    rw [h, BitVec.pow_succ, BitVec.pow_succ]
    simp [BitVec.mul_assoc]

theorem power_eq_pow' (base : BitVec width) (n : Nat) : power base n = base ^ n := by
  induction n using Nat.strongRecOn generalizing base with
  | ind n ih =>
    rw [power]
    split
    · rename_i h
      simp [h]
    · rename_i h
      rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)), square_power']
      split
      · rename_i even
        change base ^ (n / 2 + n / 2) = base ^ n
        exact congrArg (fun exponent => base ^ exponent) (by omega)
      · rename_i odd
        change base * base ^ (n / 2 + n / 2) = base ^ n
        rw [BitVec.mul_comm, ← BitVec.pow_succ]
        exact congrArg (fun exponent => base ^ exponent) (by omega)

/-- The value of a bit-vector power (core has no `BitVec.toNat_pow` in v4.35). -/
theorem bv_toNat_pow {w : Nat} (x : BitVec w) (n : Nat) :
    (x ^ n).toNat = x.toNat ^ n % 2 ^ w := by
  induction n with
  | zero => simp [BitVec.pow_zero]
  | succ n ih => rw [BitVec.pow_succ, BitVec.toNat_mul, ih, Nat.pow_succ, Nat.mod_mul_mod]

/-- **The Nat bridge.** -/
theorem power_toNat {w : Nat} (b : BitVec w) (e : Nat) :
    (power b e).toNat = Nat.powMod b.toNat e (2 ^ w) := by
  rw [power_eq_pow', bv_toNat_pow, Nat.powMod_def]

/-- **The BitVec bridge.** -/
theorem power_eq_ofNat_powMod {w : Nat} (b : BitVec w) (e : Nat) :
    power b e = BitVec.ofNat w (Nat.powMod b.toNat e (2 ^ w)) := by
  apply BitVec.eq_of_toNat_eq
  rw [power_toNat, BitVec.toNat_ofNat, Nat.powMod_def, Nat.mod_mod]

/-- MIR's `exp` (tv/SolarTV/Word.lean:32) through the bridge. -/
theorem binary_exp {w : Nat} (a b : BitVec w) :
    binary .exp a b = BitVec.ofNat w (Nat.powMod a.toNat b.toNat (2 ^ w)) :=
  power_eq_ofNat_powMod a b.toNat

/-- The symbolic form: `power` is `b ^ e % 2 ^ w` on values. -/
theorem power_toNat_pow {w : Nat} (b : BitVec w) (e : Nat) :
    (power b e).toNat = b.toNat ^ e % 2 ^ w := by
  rw [power_toNat, Nat.powMod_def]

/-! ## Fixture: a concrete 256-bit exponent (new). The old proof is in PowerOld.lean. -/

/-- `3 ^ (2^255 + 12345) mod 2^256`. Through the bridge, `Nat.reducePowMod` evaluates it with
GMP in O(log e) and the kernel checks the literal. -/
theorem fixture_power_big :
    power (3#256) (2 ^ 255 + 12345) =
      42433521838168360224194192642435598547821817833025597527132038330417986287139#256 := by
  rw [power_eq_ofNat_powMod]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reducePowMod]

/- Note: after the rewrite, `decide` still fails (maximum recursion depth): the kernel does not
run `Nat.powMod`'s well-founded recursion. The `Nat.reducePowMod` simproc is the evaluation path. -/

end Verify.Eval.F

/-- info: 'Verify.Eval.F.power_eq_ofNat_powMod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.power_eq_ofNat_powMod
/-- info: 'Verify.Eval.F.binary_exp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.binary_exp
/-- info: 'Verify.Eval.F.fixture_power_big' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.fixture_power_big

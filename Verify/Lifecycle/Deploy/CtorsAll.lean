import Verify.Lifecycle.Symbolic
import Verify.Lifecycle.Deploy.Ctors

/-!
# solar's constructor fixtures, for every argument word

`Deploy.Ctors` proves each fixture's creation for one list of argument words. Here each is proved
for every list of argument words, by one kernel evaluation of the symbolic frame
(`Creation.Sym.deploys_all`): the init code decodes each static argument word, writes the storage
the constructor body names, and installs solar's runtime code with the immutable patched from the
argument. The hypotheses are the argument conditions under which solar's init code does not
revert (a clean address word, no overflow of a checked addition); the reverting creations are
outside these theorems.

The storage and the runtime code are written here from each fixture's constructor body
(`tools/certify/examples/lifecycle`); they are not derived from SolidCore's evaluation of the
source, whose link to these creations stays the per-argument `Route.Statement`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolidCore.Refinement SolidCore.Refinement.Evm
open Verify.Lifecycle.Creation Verify.Lifecycle.Creation.Sym

namespace Verify.Lifecycle.Deploy.CtorsAll

open Verify.Lifecycle.Deploy.Ctors

/-- The runtime code `rt` as a symbolic code with no argument bytes. -/
def plain (rt : ByteArray) : List B := patched rt []

theorem codeOf_plain (as : List U256) (rt : ByteArray) : codeOf as (plain rt) = rt :=
  codeOf_patched as rt []

/-! ## The argument conditions -/

theorem shr160_eq_zero {b : U256} (h : b.toNat < 2 ^ 160) : bitwiseShr 0xa0#256 b = 0 := by
  unfold bitwiseShr
  rw [if_pos (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero]
  exact Nat.div_eq_of_lt (by simpa using h)

theorem gtMask_eq_zero {b : U256} (h : b.toNat < 2 ^ 160) :
    greaterThan b 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff#256 = 0 := by
  unfold greaterThan
  rw [if_neg]
  simp only [BitVec.toNat_ofNat]
  omega

theorem and_mask {b : U256} (h : b.toNat < 2 ^ 160) :
    bitwiseAnd b 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff#256 = b := by
  unfold bitwiseAnd
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hm : (0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff#256 : U256).toNat =
      2 ^ 160 - 1 := by decide
  rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem add_toNat {a b : U256} (h : a.toNat + b.toNat < 2 ^ 256) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-! ## NoArgCtor -/

/-- The path conditions of `NoArgCtor`'s init code: none. -/
def noArgPre : List E := []

set_option maxRecDepth 100000 in
theorem noArg_check :
    symCheck fuel NoArgCtor.init 0 noArgPre (plain NoArgCtor.runtime) [(0, .c 7)] = true := by
  decide +kernel

/-- **`NoArgCtor`, created with no argument, installs solar's runtime code and leaves slot 0
holding 7.** -/
theorem noArgCtor_deploys : Deploys (initArgs NoArgCtor.init []) NoArgCtor.runtime [(0, 7)] := by
  have h := deploys_all noArg_check [] rfl (by simp [noArgPre])
  rw [codeOf_plain] at h
  simpa [storeOf, E.eval] using h

/-! ## ArgCtor: `constructor(uint256 a, address b)`, slot 0 := a, slot 1 := b -/

/-- The path conditions of `ArgCtor`'s init code: solar's check that the address word is clean. -/
def argPre : List E :=
  [.bin .shr (.c 0xa0#256) (.arg 1),
   .bin .gt (.arg 1) (.c 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff#256),
   .bin .sub (.bin .and (.arg 1) (.c 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff#256))
     (.arg 1)]

set_option maxRecDepth 100000 in
theorem arg_check :
    symCheck fuel ArgCtor.init 2 argPre (plain ArgCtor.runtime) [(0, .arg 0), (1, .arg 1)] = true := by
  decide +kernel

/-- **`ArgCtor`, created with any word `a` and any address `b`, installs solar's runtime code and
leaves slot 0 holding `a` and slot 1 holding `b`.** -/
theorem argCtor_deploys (a b : U256) (hb : b.toNat < 2 ^ 160) :
    Deploys (initArgs ArgCtor.init [a.toNat, b.toNat]) ArgCtor.runtime [(0, a.toNat), (1, b.toNat)] := by
  have h := deploys_all arg_check [a, b] rfl (by
    intro e he
    simp only [argPre, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [E.eval, binOf, List.getD_cons_succ, List.getD_cons_zero, sub]
    · exact shr160_eq_zero hb
    · exact gtMask_eq_zero hb
    · rw [and_mask hb]; exact BitVec.sub_self b)
  rw [codeOf_plain] at h
  simpa [storeOf, E.eval] using h

/-! ## PairCtor: `constructor(uint256 a, uint256 b)`, slot 0 := a, slot 1 := a + b -/

/-- The path conditions of `PairCtor`'s init code: solar's overflow check of `a + b`. -/
def pairPre : List E := [.bin .lt (.bin .add (.arg 0) (.arg 1)) (.arg 0)]

set_option maxRecDepth 100000 in
theorem pair_check :
    symCheck fuel PairCtor.init 2 pairPre (plain PairCtor.runtime)
      [(0, .arg 0), (1, .bin .add (.arg 0) (.arg 1))] = true := by
  decide +kernel

/-- **`PairCtor`, created with any words `a` and `b` whose sum does not overflow, installs solar's
runtime code and leaves slot 0 holding `a` and slot 1 holding `a + b`.** -/
theorem pairCtor_deploys (a b : U256) (hab : a.toNat + b.toNat < 2 ^ 256) :
    Deploys (initArgs PairCtor.init [a.toNat, b.toNat]) PairCtor.runtime
      [(0, a.toNat), (1, a.toNat + b.toNat)] := by
  have h := deploys_all pair_check [a, b] rfl (by
    intro e he
    simp only [pairPre, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp only [E.eval, binOf, List.getD_cons_succ, List.getD_cons_zero, lessThan, add]
    rw [if_neg (by rw [add_toNat hab]; omega)])
  rw [codeOf_plain] at h
  simpa [storeOf, E.eval, binOf, add, add_toNat hab] using h

/-! ## ImmutableCtor: `constructor(uint256 x)`, immutable limit := x, slot 0 := x + 1 -/

/-- The path conditions of `ImmutableCtor`'s init code: solar's overflow check of `x + 1`. -/
def immPre : List E := [.un .iszero (.bin .add (.c 1#256) (.arg 0))]

/-- solar's runtime code with the immutable word at offset 45 taken from the argument. -/
def immCode : List B := patched ImmutableCtor.runtime [(45, .arg 0)]

set_option maxRecDepth 100000 in
theorem imm_check :
    symCheck fuel ImmutableCtor.init 1 immPre immCode [(0, .bin .add (.c 1#256) (.arg 0))] = true := by
  decide +kernel

/-- **`ImmutableCtor`, created with any word `x` below `2^256 - 1`, installs solar's runtime code
with the immutable at offset 45 patched to `x` and leaves slot 0 holding `x + 1`.** -/
theorem immutableCtor_deploys (x : U256) (hx : x.toNat + 1 < 2 ^ 256) :
    Deploys (initArgs ImmutableCtor.init [x.toNat]) (patchWord ImmutableCtor.runtime 45 x)
      [(0, x.toNat + 1)] := by
  have h1 : (1#256 + x).toNat = x.toNat + 1 := by
    rw [add_toNat (by simp; omega)]; simp; omega
  have h := deploys_all imm_check [x] rfl (by
    intro e he
    simp only [immPre, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    simp only [E.eval, binOf, unOf, List.getD_cons_zero, isZero, add]
    rw [if_neg (fun h0 => by have := congrArg BitVec.toNat h0; rw [h1] at this; simp at this)])
  rw [immCode, codeOf_patched] at h
  simpa [storeOf, E.eval, binOf, add, h1] using h

/-! ## The specification read off the run, as the certification driver states it

`allArgsCheck` needs no specification written by hand: it reads the path conditions, the runtime
code and the storage off the symbolic run, and `deploys_at` recovers each concrete creation
of `Deploy.Ctors` from it. -/

set_option maxRecDepth 100000 in
theorem imm_allArgs : allArgsCheck fuel ImmutableCtor.init 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `ImmutableCtor.deploys`, as an instance of every creation of `ImmutableCtor`. -/
theorem immutableCtor_deploys_at : Deploys (initArgs ImmutableCtor.init [1000]) ImmutableCtor.code [(0, 1001)] :=
  deploys_at imm_allArgs (as := [1000#256]) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem arg_allArgs : allArgsCheck fuel ArgCtor.init 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `ArgCtor.deploys`, as an instance of every creation of `ArgCtor`. -/
theorem argCtor_deploys_at : Deploys (initArgs ArgCtor.init [42, 48879]) ArgCtor.code [(0, 42), (1, 48879)] :=
  deploys_at arg_allArgs (as := [42#256, 48879#256]) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The derived specification is not vacuous the wrong way: at 41 it does not give slot 0 = 42. -/
theorem argCtor_at_wrong : atArgsCheck fuel ArgCtor.init 2 [41#256, 48879#256] [41, 48879] ArgCtor.code
    [(0, 42), (1, 48879)] = false := by decide +kernel

/-- info: 'Verify.Lifecycle.Deploy.CtorsAll.immutableCtor_deploys_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms immutableCtor_deploys_at

/-- info: 'Verify.Lifecycle.Deploy.CtorsAll.argCtor_deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms argCtor_deploys

/-- info: 'Verify.Lifecycle.Deploy.CtorsAll.pairCtor_deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairCtor_deploys

/-- info: 'Verify.Lifecycle.Deploy.CtorsAll.immutableCtor_deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms immutableCtor_deploys

/-- info: 'Verify.Lifecycle.Deploy.CtorsAll.noArgCtor_deploys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noArgCtor_deploys

end Verify.Lifecycle.Deploy.CtorsAll

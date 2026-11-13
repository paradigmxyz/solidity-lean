import Verify.Spec.Tree
import Verify.Spec.Hash
import Contracts.Token.VC.Transfer
import Contracts.Token.Spec.Export
import Contracts.Token.EndToEnd

/-!
# Token: solar-verify's exported spec of `transfer` from its erased tree, generically

`Spec/Export.lean` is solar-verify's `--emit-lean-spec` export of `scripts/verify/Token.sol`
(its first line reads the spec library from `Verify.Spec.Contract`). `transfer_meets` proves
`transfer`'s exported spec of the generic source stage's tree (`transferTree`, `transferShape_eq`):
the two balance clauses, the frame clause over every other address, the supply clause and the
invariant `totalSupply == sumBalances` (`TreeMeetsFixed`: `transfer` writes no ghost). The
mapping slots are SolidCore's `solHash`, which is the spec semantics' slot by `solHash_eq`; their
distinctness on distinct addresses, and from the scalar slots, is the one hypothesis,
`SlotsSeparated 0`. `transfer_spec_bytecode` carries it to solar's bytecode through the certified
stages (`EndToEnd.certified`). No solver verdict is used.
-/

namespace SolidCore.Spec.TreeDemo.Token

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Token

abbrev spec : Bundle := SolidCore.Spec.Export.Token.Token
def transferSpec : FnSpec := spec.spec.specs[1]'(by decide)
def ctx : Ctx := { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 }

/-- The call context of every call: `ctx` with the call's value. -/
def ctxOf (call : SolarTV.Call) : Ctx := { ctx with value := call.callvalue }

theorem toNat_mod_wordMod {a : Nat} (h : a < wordMod) : ((a : Int) % (wordMod : Int)).toNat = a := by
  rw [← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt h]

theorem toNat_mod_lit {a : Nat} (h : a < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    ((a : Int) % ((115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) : Int)).toNat = a := by
  rw [← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt h]

theorem ite_mod {P : Prop} [Decidable P] (a b n : Nat) :
    (if P then a else b) % n = if P then a % n else b % n := by split <;> rfl

theorem ite10_eq_zero {P : Prop} [Decidable P] : ((if P then 1 else 0) : Nat) = 0 ↔ ¬ P := by
  split <;> simp_all

attribute [local irreducible] SolidCore.Refinement.Generic.solHash in
theorem transfer_meets (hsep : SlotsSeparated 0) :
    TreeMeetsFixed spec transferSpec ctx 2 transferTree := by
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv
  have hsm : ∀ k, s k % 2 ^ 256 = s k := fun k => Nat.mod_eq_of_lt (hs k)
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨_, _⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hl <;> (try omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargs
  obtain ⟨h0, h1⟩ := hargs
  simp only [transferSpec, spec, SolidCore.Spec.Export.Token.Token, List.getElem_cons_succ, List.getElem_cons_zero,
    decodeWords, Ty.ofWord, bind, pure, Option.bind, Option.some.injEq] at hdec
  split_ifs at hdec with ha
  all_goals simp_all only [ite_true, Option.some.injEq, reduceCtorEq]
  subst hdec
  simp only [Nat.reducePow] at h0 h1 ha hs hsm
  have ha0 : a0 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = a0 :=
    Nat.mod_eq_of_lt h0
  have ha1 : a1 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = a1 :=
    Nat.mod_eq_of_lt h1
  have hc1 : ¬ 1461501637330902918203684832716283019655932542975 < a0 := by omega
  have hL : ((115792089237316195423570985008687907853269984665640564039457584007913129639936 : Nat) : Int) = (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) := rfl
  have hk : ((115792089237316195423570985008687907853269984665640564039457584007913129639936 - a1 : Nat) : Int) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 - (a1 : Int) := Int.ofNat_sub (by omega)
  have hw : (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simp only [Nat.reducePow]
  have hw' : wordMod = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hw
  have t8 : ((8192 : Int) % (wordMod : Int)).toNat = 8192 :=
    toNat_mod_wordMod (a := 8192) (by rw [hw']; decide)
  have tA := toNat_mod_wordMod (a := a0) (by rw [hw']; exact h0)
  have p80 : (2 : Nat) ^ (8 * 0) = 1 := rfl
  have p832 : (2 : Nat) ^ (8 * 32) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simp only [Nat.reduceMul, Nat.reducePow]
  have t0 : ((0 : Int) % (wordMod : Int)).toNat = 0 := by rw [Int.zero_emod]; rfl
  have hinj := fun a b ha hb => slot_inj hsep (a := a) (b := b) ha hb
  have hge := fun a ha => slot_ge hsep (a := a) ha
  have hlt := solHash_lt
  have hspec : ∀ k s, keccakWord (wordBytes k ++ wordBytes s) = solHash k s := fun k s => (solHash_eq k s).symm
  generalize solHash = H at *
  refine ⟨fun hsucc => ?_, fun hne => by simp [transferSpec, spec, SolidCore.Spec.Export.Token.Token] at hne⟩
  simp only [transferTree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, hsm, ha0, ha1,
    Nat.reducePow, Nat.reduceMod, Nat.zero_mod, List.getD_cons_zero, List.getD_cons_succ, Res.obs,
    Writes.store] at hsucc ⊢
  have h8 := hge 8192 (by decide)
  have hA := hge a0 ha
  have hl8 := hlt 8192 0
  have hlA := hlt a0 0
  have hi := hinj a0 8192 ha (by decide)
  have hsS := hs (H 8192 0)
  have hsA := hs (H a0 0)
  have hs1 := hs 1
  simp only [Generic.wordSize, Nat.reducePow] at hl8 hlA hlt h8 hA
  have hl8' := Nat.mod_eq_of_lt hl8
  have hlA' := Nat.mod_eq_of_lt hlA
  simp only [hc1, ite_false, Nat.zero_mod, ite_true, hl8', hlA', hsm, ha0, ha1, ite_mod, Nat.reduceMod,
    ite10_eq_zero, Decidable.not_not, Nat.one_ne_zero, Nat.zero_ne_one] at hsucc ⊢
  split_ifs at hsucc ⊢
  all_goals simp only [Bool.false_eq_true, Bool.true_eq_false] at hsucc
  all_goals refine ⟨[1], by simp [OByte.eval, WExpr.eval, words, bytesWord, decodeWords, Ty.ofWord,
    transferSpec, spec, SolidCore.Spec.Export.Token.Token], ?_, ?_⟩
  all_goals simp only [Bundle.satAll, Bundle.sat, transferSpec, spec, SolidCore.Spec.Export.Token.Token,
    List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv, Env.cur, Env.bind, BinOp.apply, Ty.ofBits,
    toWord, ctx, List.getD_cons_zero, List.getD_cons_succ, List.lookup, hspec, ofProp_ne_zero, ite_true,
    ite_false, Bool.false_eq_true, Nat.zero_mod] at hinv ⊢
  all_goals simp only [hst, beq_self_eq_true, Ty.InRange, Option.getD_some, t8, tA, t0] at hinv ⊢
  all_goals simp only [p80, Nat.div_one] at hinv ⊢
  all_goals simp only [p832] at hinv ⊢

  all_goals simp -failIfUnchanged only [Nat.reduceMod] at hinv ⊢
  all_goals first
    | refine ⟨fun hne => ?_, fun hne => ?_, fun v hv hne => ?_, ?_⟩
    | skip
  all_goals first
    | (obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hv.1
       have hn : n < 2 ^ 160 := by omega
       rw [toNat_mod_lit (by omega)]
       have := hinj n a0 hn ha
       have := hinj n 8192 hn (by decide)
       have := hge n hn
       have := hlt n 0
       have := hs (H n 0)
       split_ifs <;> (simp -failIfUnchanged only [hw', Int.natCast_add, Int.natCast_emod, hk, hL] at *) <;> omega)
    | (split_ifs <;> (simp -failIfUnchanged only [hw', Int.natCast_add, Int.natCast_emod, hk, hL] at *) <;> omega)



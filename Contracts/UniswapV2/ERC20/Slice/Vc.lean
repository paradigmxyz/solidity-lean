import Contracts.UniswapV2.ERC20.Slice.Run
import Verify.ShapeBundle

/-!
# UniswapV2ERC20.transfer: solar-verify's exported spec, discharged over SolidCore's runs

`Gen.spec` is solar-verify's `--emit-lean-spec` export of solar's
crates/verify/uniswap-v2/transfer-slice.spec (the annotations of the slice on the pinned port):

* `old(balanceOf[msg.sender]) >= value` on success, and the recipient-overflow condition only when
  `msg.sender != to`;
* `msg.sender != to`: `balanceOf[msg.sender] == old(...) - value` and
  `balanceOf[to] == old(balanceOf[to]) + value`;
* `msg.sender == to`: `balanceOf[msg.sender] == old(balanceOf[msg.sender])`;
* `returns true`; and `succeeds-if` the balance covers `value` and (`msg.sender == to` or the
  credit does not overflow): with the ensures, success iff that condition.

Its verification condition over SolidCore:

* `transfer_meets`: the spec of the erased tree on every argument list whose footprint premise
  holds (`SepArgs`: `ScopedSep` on the caller's and `to`'s `balanceOf` preimages, nothing else);
  `tree_meets_sep` is Verify/Spec/HashScope.lean's `tree_meets_scoped` with that premise in place of
  `MapScope` (no frame family: the spec has no clause over other addresses);
* `transfer_holds`: the spec of SolidCore's checked contract on the stage's calls of `transfer`
  whose premise holds (`HoldsFnUnder`, by `holdsFnUnder_of_tree_fixed`);
* `meets_bundle`: as `Shapes.Meets` of `Shapes.bundlePost` on `ValidIn`, the form `Equiv` carries to
  the bytes (Bytes.lean);
* `sepArgs_iff`: the premise on a call's words is `Post.Scope`'s, `ScopedSep (transferFootprint 1
  caller to)`.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

/-- **The call's footprint premise on its argument words**: keccak256 separated on the
`balanceOf` preimages of the caller and of `to` (argument 0). -/
def SepArgs (args : List Nat) : Prop := ScopedSep (mapScope (callKeys 8192 [0] args) [1])

theorem sepArgs_iff {dst v : Nat} (hto : dst < 2 ^ 160) :
    SepArgs [dst, v] ↔ ScopedSep (transferFootprint balanceSlot caller dst) := by
  have : dst % 2 ^ 160 = dst := Nat.mod_eq_of_lt hto
  simp only [SepArgs, callKeys, mapScope, transferFootprint, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, this, caller,
    Generic.callerWord, balanceSlot]

/-- Two slots of the footprint are equal only for the same key and mapping. -/
theorem sep_inj {K ms : List Nat} (h : ScopedSep (mapScope K ms)) (m n : Nat) (hm : m ∈ ms) (hn : n ∈ ms)
    (hmw : m < 2 ^ 256) (hnw : n < 2 ^ 256) (a b : Nat) (hK : a ∈ K ∧ b ∈ K) :
    a < 2 ^ 160 → b < 2 ^ 160 → solHash a m = solHash b n → a = b ∧ m = n := fun ha hb he =>
  scoped_inj h (by omega) (by omega) hmw hnw (mem_mapScope hK.1 hm) (mem_mapScope hK.2 hn) he

/-- A slot of the footprint is at least `2 ^ 128`. -/
theorem sep_ge {K ms : List Nat} (h : ScopedSep (mapScope K ms)) (m : Nat) (hm : m ∈ ms) (a : Nat)
    (hK : a ∈ K) : 2 ^ 128 ≤ solHash a m :=
  scoped_ge h (mem_mapScope hK hm)

set_option maxHeartbeats 4000000 in
/-- **The exported spec holds of the erased tree** on every argument list whose footprint premise holds. -/
theorem transfer_meets :
    TreeMeetsFixedOn (fun ρ => SepArgs ρ.args) spec transfer_spec ctx 2 transfer_tree := by
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
  simp only [Nat.reducePow] at hs
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs <;>
    simp only [transfer_tree, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, ctx, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      bind, pure, Option.bind, Nat.reducePow] at hdec <;>
    split_ifs at hdec <;> simp only [Option.some.injEq, reduceCtorEq] at hdec <;>
    subst hdec <;>
    simp only [SepArgs, callKeys, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hP <;>
    simp (disch := omega) only [Nat.mod_eq_of_lt] at hP <;>
    have hinj := sep_inj hP <;> have hge := sep_ge hP <;> have hlt := solHash_lt' <;>
    have hkec := keccak_solHash <;>
    generalize solHash = H at hinj hge hlt hkec ⊢ <;>
    refine ⟨fun hsucc => have hsi : True := trivial; ?_, fun hne hsi => have hsucc : True := trivial; ?_⟩
  all_goals try (simp [transfer_tree, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, ctx] at hne; done)
  all_goals simp only [transfer_tree, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, ctx, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow] at hsucc ⊢
  all_goals simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢
  all_goals split_ifs at hsucc ⊢
  all_goals try simp only [Bool.false_eq_true, Bool.true_eq_false, imp_false, not_true_eq_false,
    IsEmpty.forall_iff] at hsucc
  all_goals try simp only [transfer_tree, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, ctx, OByte.eval, WExpr.eval, Generic.wordSize, words, bytesWord, decodeWords, Ty.ofWord,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.drop_zero, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq,
    exists_eq_left', bind, pure, Option.bind, Ty.InRange, Nat.cast_ofNat, Nat.zero_add,
    Nat.reduceLeDiff] at hsucc ⊢
  all_goals try clear hsucc
  all_goals try refine ⟨?_, ?_⟩
  all_goals simp only [Bundle.satAll, Bundle.sat, transfer_tree, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, ctx, List.getElem_cons_succ, List.getElem_cons_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval, evalList, slotOf, mkEnv,
    Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero, List.getD_cons_succ,
    List.lookup, hkec, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true, Nat.zero_mod, hst,
    beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat] at hinv hsi ⊢
  all_goals try simp only [wordMod, Nat.reducePow] at hinv hsi ⊢
  all_goals try simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.mod_eq_of_lt,
    toNat_natCast_emod] at hinv hsi ⊢
  all_goals try simp (disch := first | exact hlt _ _ | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hinv hsi ⊢
  all_goals (repeat' (first | (apply And.intro) | intro))
  -- The footprint premise, the one way it is used: the caller's and `to`'s slots differ when the
  -- addresses do (Verify/Spec/HashScope.lean's `hash_facts_scoped` instances close with the main goal
  -- still open, so its `done` fails and it adds none).
  all_goals have hk : a0 = 8192 ∨ H a0 1 ≠ H 8192 1 :=
    (Decidable.em (a0 = 8192)).elim Or.inl fun h => Or.inr fun (he : H a0 1 = H 8192 1) =>
      absurd (hinj 1 1 (by simp) (by simp) (by decide) (by decide) a0 8192 (by simp) (by omega) (by decide) he).1 h
  all_goals have hk' : a0 ≠ 8192 ∨ H a0 1 = H 8192 1 :=
    (Decidable.em (a0 = 8192)).elim (fun h => Or.inr (congrArg (H · 1) h)) Or.inl
  all_goals (hash_facts_scoped H s hinj hge hlt hs; (try split_ifs) <;> omega)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.transfer_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transfer_meets

end SolidCore.Spec.UniswapV2.ERC20.Slice

import Contracts.UniswapV2.ERC20.Slice.Statement
import Contracts.UniswapV2.ERC20.Slice.Gen.TreeFrom
import Verify.Spec.TreeFrom

/-!
# UniswapV2ERC20.transfer from every caller: solar-verify's exported spec over SolidCore's runs

`Statement.lean`'s `transfer_holds` is the spec of calls sent by `callerAddress`. Here the caller is
every account `a < 2 ^ 160` other than the contract, by Verify/Spec/TreeFrom.lean's
`holdsFnUnder_of_tree_from_footprint_zero` on the symbolic-caller tree `GenFrom.transfer_tree_from`
(`eraseFnSym`, checked against SolidCore's contract of the pinned port by `GenFrom.transfer_erase_from_eq`):

* `transfer_meets_from`: the spec of the tree, for every caller `a`, on every argument list whose
  footprint premise `FootprintSep a [0] [1]` holds;
* `transfer_holds_from`: the spec of SolidCore's checked contract, run as `solidCoreFrom a` in
  `ctxOfCallFrom a`, on every call of `transfer` with no value whose footprint premise holds;
* `meets_bundle_from`: the same as `Shapes.Meets` of `bundlePost` on `ValidInAt a` (`Valid deployed` and
  `ScopeFromAt a`, `ScopedSep (transferFootprint balanceSlot a to)` at the call).

**The finite keccak256 qualification.** The premise of each call is `ScopedSep` of exactly two
preimages, `a . 1` and `to . 1` (the caller's and the recipient's `balanceOf` slots):
keccak256 injective on them with both images at least `2 ^ 128`. It is assumed call by call, not
proved, and nothing is assumed of keccak256 elsewhere.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen SolidCore.Verify.AnyCaller

theorem fn_from_eq : GenFrom.fn_transfer = fn_transfer := rfl

theorem spec_from_eq : GenFrom.transfer_spec = transfer_spec := rfl

set_option maxHeartbeats 8000000 in
/-- **The exported spec holds of the symbolic-caller tree from every caller** on every argument list
whose footprint premise holds: keccak256 separated on the caller's and `to`'s `balanceOf` preimages. -/
theorem transfer_meets_from :
    TreeMeetsFootprintFrom [0] [1] spec transfer_spec 2 GenFrom.transfer_tree_from := by
  intro a ha hne args s iargs pre hl hargs hs hdec hst ht hreq hinv hP
  have hca : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have ha' : a % 2 ^ 160 = a := Nat.mod_eq_of_lt ha
  simp only [Nat.reducePow] at hs hca ha'
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> (try omega) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs <;>
    simp only [GenFrom.transfer_tree_from, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, SolidCore.Spec.ctxAt, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords, Ty.ofWord,
      bind, pure, Option.bind, Nat.reducePow] at hdec <;>
    split_ifs at hdec <;> simp only [Option.some.injEq, reduceCtorEq] at hdec <;>
    subst hdec <;>
    simp only [FootprintSep, footprintFrom, callKeys, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, Nat.reducePow] at hP <;>
    simp (disch := omega) only [Nat.mod_eq_of_lt] at hP <;>
    have hinj := sep_inj hP <;> have hge := sep_ge hP <;> have hlt := solHash_lt' <;>
    have hkec := keccak_solHash <;>
    generalize solHash = H at hinj hge hlt hkec ⊢ <;>
    refine ⟨fun hsucc => have hsi : True := trivial; ?_, fun hne hsi => have hsucc : True := trivial; ?_⟩
  all_goals try (simp [GenFrom.transfer_tree_from, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, SolidCore.Spec.ctxAt] at hne; done)
  all_goals simp only [GenFrom.transfer_tree_from, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, SolidCore.Spec.ctxAt, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize, Res.obs,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow, hca] at hsucc ⊢
  all_goals simp (disch := simp only [hargs, hs, hlt, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not] at hsucc ⊢
  all_goals split_ifs at hsucc ⊢
  all_goals try simp only [Bool.false_eq_true, Bool.true_eq_false, imp_false, not_true_eq_false,
    IsEmpty.forall_iff] at hsucc
  all_goals try simp only [GenFrom.transfer_tree_from, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, SolidCore.Spec.ctxAt, OByte.eval, WExpr.eval, Generic.wordSize, words, bytesWord, decodeWords, Ty.ofWord,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.drop_zero, List.take_succ_cons, List.take_zero, List.foldl_cons,
    List.foldl_nil, Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceLT, ite_true, ite_false, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq,
    exists_eq_left', bind, pure, Option.bind, Ty.InRange, Nat.cast_ofNat, Nat.zero_add,
    Nat.reduceLeDiff] at hsucc ⊢
  all_goals try clear hsucc
  all_goals try refine ⟨?_, ?_⟩
  all_goals simp only [Bundle.satAll, Bundle.sat, GenFrom.transfer_tree_from, transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, SolidCore.Spec.ctxAt, List.getElem_cons_succ, List.getElem_cons_zero,
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
  -- addresses do.
  all_goals have hk : a0 = a ∨ H a0 1 ≠ H a 1 :=
    (Decidable.em (a0 = a)).elim Or.inl fun h => Or.inr fun (he : H a0 1 = H a 1) =>
      absurd (hinj 1 1 (by simp) (by simp) (by decide) (by decide) a0 a (by simp) (by omega) (by omega) he).1 h
  all_goals have hk' : a0 ≠ a ∨ H a0 1 = H a 1 :=
    (Decidable.em (a0 = a)).elim (fun h => Or.inr (congrArg (H · 1) h)) Or.inl
  all_goals (hash_facts_scoped H s hinj hge hlt hs; (try split_ifs) <;> omega)

/-- **The scoped premise of a call sent by `a`**: keccak256 separated on the preimages of `a`'s and
the recipient's `balanceOf` slots, and nothing else (the body of `CertifiedFrom.ScopeAt`, so the two
are the same proposition). -/
def ScopeFromAt (a : Nat) (call : Call) : Prop :=
  ∀ σ dst v, call = transferCall σ dst v → dst < 2 ^ 160 → v < 2 ^ 256 →
    ScopedSep (transferFootprint balanceSlot a dst)

/-- The calls of `transfer` from the constructor's storage are the stage's calls with no value. -/
theorem zeroScope_of_valid {call : Call} (h : Valid deployed call) : zeroScope fn_transfer deployed call := by
  obtain ⟨σ, dst, v, hcov, hto, hv, rfl⟩ := h
  exact ⟨σ, hcov, by decide, fn_transfer, by simp, [dst, v], rfl, by simp; omega, rfl⟩

/-- **The footprint premise of a valid call sent by `a`**, in the form the call's words give it. -/
theorem footprintSep_of_scopeAt {a : Nat} {call : Call} (h : Valid deployed call) (hs : ScopeFromAt a call) :
    FootprintSep a [0] [1] (callArgs call) := by
  obtain ⟨σ, dst, v, hcov, hto, hv, rfl⟩ := h
  rw [callArgs_transferCall σ (by omega) hv, footprintSep_transfer hto]
  exact hs σ dst v rfl hto hv

/-- **The exported spec of `transfer` holds of SolidCore's checked contract from every caller**: for
every account `a < 2 ^ 160` other than the contract, on every call of `transfer` sent by `a` with no
value, from any storage covering the deployed one, whose two `balanceOf` preimages `a . 1` and
`to . 1` keccak256 separates (`FootprintSep a [0] [1]`). -/
theorem transfer_holds_from {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress →
      HoldsFnUnder (fun call => FootprintSep a [0] [1] (callArgs call)) (solidCoreFrom a fuel) c
        (zeroScope fn_transfer deployed) spec (ctxOfCallFrom a) idStep transfer_spec := by
  obtain ⟨⟨d, hd⟩, -⟩ := facts hc
  have hmap := GenFrom.transfer_erase_from_eq
  simp only [GenFrom.transfer_erase_from?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT, -, -⟩ := hmap
  exact holdsFnUnder_of_tree_from_footprint_zero (fn := fn_transfer) hd (by decide) hf
    (by simpa [fn_transfer] using hlen) hT (fun _ _ _ => rfl)
    (by simpa [fn_transfer] using transfer_meets_from)

/-- The valid calls sent by `a` with their premise. -/
def ValidInAt (a : Nat) (call : Call) : Prop := Valid deployed call ∧ ScopeFromAt a call

/-- **The exported spec as `Shapes.Meets`, from every caller**, of `bundlePost` in `ctxOfCallFrom a` on
the valid calls sent by `a` whose footprint premise holds. -/
theorem meets_bundle_from {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) (a : Nat) (ha : a < 2 ^ 160)
    (hne : a ≠ selfAddress) :
    Meets (solidCoreFrom a fuel) c (ValidInAt a) (bundlePost spec (ctxOfCallFrom a) idStep) := by
  intro call h obs hrun fs hfs args pre hpre
  rw [specs_eq, List.mem_singleton] at hfs
  subst hfs
  obtain ⟨obs', h1, h2⟩ := transfer_holds_from hc a ha hne call (zeroScope_of_valid h.1)
    (footprintSep_of_scopeAt h.1 h.2) args pre hpre
  rw [hrun, Option.some.injEq] at h1
  subst h1
  exact h2

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.transfer_holds_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transfer_holds_from

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.meets_bundle_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_bundle_from

end SolidCore.Spec.UniswapV2.ERC20.Slice

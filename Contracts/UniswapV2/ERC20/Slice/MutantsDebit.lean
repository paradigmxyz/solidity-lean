import Contracts.UniswapV2.ERC20.Slice.Bytes
import Contracts.UniswapV2.ERC20.Slice.Gen.MutDebit.Tree

/-!
# UniswapV2ERC20.transfer: the missing-debit mutant, refused by execution

See Mutants.lean. The mutant undoes the debit (`balanceOf[from] = balanceOf[from].sub(value).add(value)`):
`transfer(1, 2)` from a caller balance of 5 succeeds and leaves it at 5, where `TargetPost` asks 3. Its
own module, so that each module checks within 6 GB.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice

/-! ## Debit -/

section Debit
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen.MutDebit in
/-- SolidCore's run of a valid call on the debit mutant is its erased tree's result. -/
theorem runDebit {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutDebit.contract? = .ok c) {σ : List (Nat × Nat)} {dst v : Nat}
    (hcov : Generic.Covers deployed σ) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256) :
    (solidCore fuel).run c (transferCall σ dst v) =
      some (transfer_tree.eval ⟨[dst, v], slotValue σ, solHash⟩).obs := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep
  have hmap := transfer_erase_eq
  simp only [transfer_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact source_run hd hcov (by decide) hf hT [dst, v] (by simp [hlen]) (by simp; omega)
end Debit

/-! ## The debit mutant's tree, by parts -/

section DebitParts
set_option simprocs false

/-- The debited balance credited back: the mutant's caller slot. -/
abbrev eAddBack : WExpr := .bin .add eSub (.arg 1)
/-- The recipient's balance in the mutant's state after its caller write. -/
abbrev eSelD : WExpr := .sel (.bin .eq hT hC) eAddBack (.sinit hT)
/-- The mutant's credited balance. -/
abbrev eAddD : WExpr := .bin .add eSelD (.arg 1)
/-- SafeMath's `add` test of the credit-back. -/
abbrev c3d : WExpr := .un .iszero (.bin .lt eAddBack eSub)
/-- SafeMath's `add` test of the credit. -/
abbrev c4d : WExpr := .un .iszero (.bin .lt eAddD eSelD)

/-- The mutant's success leaf. -/
def okD : Tree :=
  .halt true (wordOBytes (.lit 1)) [(hT, eAddD), (hC, eAddBack)]
    [{ topics := [.lit transferTopic, .lit 8192, .arg 0], data := wordOBytes (.arg 1) }]

-- The mutant's erased tree, by parts: the kernel's conversion check.
kernel_rfl dtree_eq Gen.MutDebit.transfer_tree
  (.ite c1 (.halt false [] [] [])
    (.ite c2 (.ite c3d (.ite c4d okD (.halt false (errBytes addMsg) [] [])) (.halt false (errBytes addMsg) [] []))
      (.halt false (errBytes subMsg) [] [])))

variable {s : Nat → Nat} {dst v : Nat} (hs : ∀ k, s k < 2 ^ 256) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256)
include hs hto hv

theorem ev_addBack (hle : v ≤ s (balKey caller)) : eAddBack.eval (val s dst v) = s (balKey caller) := by
  simp only [eAddBack, eval_bin, ev_sub hs hto hv, ev_arg1 hv, BinOp.eval, wsub_of_le (hs _) hle,
    Generic.wordSize, Nat.mod_mod, Nat.sub_add_cancel hle]
  exact Nat.mod_eq_of_lt (hs _)

theorem ev_c3d (hle : v ≤ s (balKey caller)) : c3d.eval (val s dst v) = 1 := by
  simp only [c3d, WExpr.eval.eq_4, eval_bin, ev_addBack hs hto hv hle, ev_sub hs hto hv,
    wsub_of_le (hs _) hle, BinOp.eval, UnOp.eval, ite01_modW, Generic.wordSize]
  split_ifs <;> omega

theorem ev_selD (hne : balKey dst ≠ balKey caller) : eSelD.eval (val s dst v) = s (balKey dst) := by
  simp only [eSelD, WExpr.eval.eq_7, eval_bin, ev_hT hto, ev_hC, BinOp.eval, ite01_modW, Generic.wordSize,
    if_neg hne, ev_b hs hto hv, eq_self_iff_true, if_true]

theorem ev_c4d (hne : balKey dst ≠ balKey caller) (hov : s (balKey dst) + v < 2 ^ 256) :
    c4d.eval (val s dst v) = 1 := by
  simp only [c4d, eAddD, WExpr.eval.eq_4, eval_bin, ev_selD hs hto hv hne, ev_arg1 hv, BinOp.eval, UnOp.eval,
    ite01_modW, Generic.wordSize, Nat.mod_mod, Nat.mod_eq_of_lt hov]
  split_ifs <;> omega

/-- **The debit mutant on a call that the source accepts, with distinct slots**: success, and the
caller's slot keeps its balance. -/
theorem debit_eval (hle : v ≤ s (balKey caller)) (hne : balKey dst ≠ balKey caller)
    (hov : s (balKey dst) + v < 2 ^ 256) :
    (Gen.MutDebit.transfer_tree.eval (val s dst v)).success = true ∧
      (Gen.MutDebit.transfer_tree.eval (val s dst v)).store (balKey caller) = s (balKey caller) := by
  have e2 : c2.eval (val s dst v) = 1 := by rw [ev_c2 hs hto hv, if_pos hle]
  rw [dtree_eq]
  simp only [Tree.eval, ev_c1 hs hto hv, e2, ev_c3d hs hto hv hle, ev_c4d hs hto hv hne hov, if_pos,
    one_ne_zero, if_false, okD, if_true, eq_self_iff_true, true_and]
  simp only [Writes.store, Generic.wordSize, ev_hT hto, ev_hC, balKey_mod, if_neg hne, if_true,
    eq_self_iff_true, ev_addBack hs hto hv hle]

end DebitParts

/-- The caller holds 5, every other slot 0. -/
def σd : List (Nat × Nat) := [(3, 0), (balKey caller, 5)]

theorem coversDebit : Generic.Covers Gen.MutDebit.deployed σd := by
  intro kv hkv
  simp only [Gen.MutDebit.deployed, List.mem_singleton] at hkv
  subst hkv
  exact ⟨(3, 0), by simp [σd], rfl⟩

/-- The caller's and address 1's `balanceOf` slots differ (the real keccak256, by the kernel). -/
theorem slots_ne : solHash 1 1 ≠ solHash 8192 1 := fun h =>
  (transfer_slots scopedSep_transfer_example (by decide) (by decide) (by decide)).1 (by decide) h.symm

theorem obs_success (R : Res) (h : R.success = true) : R.obs.success = true := h

theorem obs_storage (R : Res) (k : Nat) {n : Nat} (h : R.store k = n) : R.obs.storage k = n := h

set_option simprocs false in
/-- The debit mutant's result on `transfer(1, 2)` from `σd`: success, with the caller's balance
still 5. -/
theorem debit_result :
    (Gen.MutDebit.transfer_tree.eval ⟨[1, 2], slotValue σd, solHash⟩).obs.success = true ∧
      (Gen.MutDebit.transfer_tree.eval ⟨[1, 2], slotValue σd, solHash⟩).obs.storage (balKey caller) = 5 := by
  have hs : ∀ k, slotValue σd k < 2 ^ 256 := fun k => Generic.slotValue_lt σd k
  have hne : balKey 1 ≠ balKey caller := by
    rw [show balKey caller = solHash 8192 1 by simp only [balKey, caller, Generic.callerWord]]
    exact slots_ne
  have ha : slotValue σd (balKey caller) = 5 := by rw [σd, slotValue_last]; decide
  have hb : slotValue σd (balKey 1) = 0 := by
    have h : ¬ (balKey caller % 2 ^ 256 = balKey 1 % 2 ^ 256) := by
      rw [balKey_mod, balKey_mod]; exact Ne.symm hne
    simp only [slotValue, σd, List.foldl_cons, List.foldl_nil, if_neg h, Nat.zero_mod, ite_self]
  have h := debit_eval (s := slotValue σd) (dst := 1) (v := 2) hs (by norm_num) (by norm_num)
    (by rw [ha]; norm_num) hne (by rw [hb]; norm_num)
  have e1 : (⟨[1, 2], slotValue σd, solHash⟩ : Val) = val (slotValue σd) 1 2 := rfl
  rw [← e1] at h
  exact ⟨obs_success _ h.1, obs_storage _ _ (h.2.trans ha)⟩

theorem validDebit : Valid Gen.MutDebit.deployed (transferCall σd 1 2) :=
  ⟨σd, 1, 2, coversDebit, by decide, by decide, rfl⟩

theorem scopeDebit : Scope (transferCall σd 1 2) := by
  intro σ dst v h hto hv
  obtain ⟨-, rfl, -⟩ := transferCall_inj (by decide) (by decide) (by omega) hv h
  exact scopedSep_transfer_example

/-- **The debit mutant fails `TargetPost`**: `transfer(1, 2)` from a balance of 5 succeeds and
leaves the caller's balance at 5, not 3. -/
theorem debit_refuted_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutDebit.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (fun call => Valid Gen.MutDebit.deployed call ∧ Scope call) TargetPost := by
  intro h
  have hp := h _ ⟨validDebit, scopeDebit⟩ _ (runDebit hc coversDebit (by decide) (by decide))
    σd 1 2 rfl (by decide) (by decide)
  have hb : slotValue σd (balKey caller) = 5 := by rw [σd, slotValue_last]; decide
  have := ((hp.1 (by decide)).2 debit_result.1).1
  rw [debit_result.2, hb] at this
  omega

/-- **The debit mutant fails `SeqPost`** (through `targetPost_of_seq`). -/
theorem debit_refuted_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutDebit.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (Valid Gen.MutDebit.deployed) SeqPost := fun h =>
  debit_refuted_target hc fun call hv obs hrun => targetPost_of_seq (h call hv.1 obs hrun) hv.2

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.debit_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms debit_refuted_target

end SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants

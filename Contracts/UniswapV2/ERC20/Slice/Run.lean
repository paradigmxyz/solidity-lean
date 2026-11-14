import Contracts.UniswapV2.ERC20.Slice.Post
import Contracts.UniswapV2.ERC20.Slice.Gen.Tree

/-!
# UniswapV2ERC20.transfer: what SolidCore's checked contract does, from its erased tree

The generic source stage erases SolidCore's checked `transfer` to the tree
`Gen.transfer_tree` (`Gen.transfer_erase_eq`, a kernel check against the contract the frontend
built from the pinned port; `Gen.deploy_eq` for the constructor's storage), and SolidCore runs
every call of the stage's scope as that tree (`Generic.source_run`). So:

* `tree_eq`: the tree, by named parts (its three tests and its three leaves);
* `tree_seq`: the tree's result on `transfer(to, v)` from any storage of words is
  `SeqPost`'s, by evaluating it: no hash premise, the slots are the ones the source computes;
* `run_tree`: SolidCore's run of a valid call is the tree's result;
* `meets_seq`: `Shapes.Meets` of `SeqPost` over SolidCore's runs, with no premise;
* `meets_target`: `Shapes.Meets` of `TargetPost` on the valid calls whose footprint premise
  holds (`ValidIn`: `Valid` and `Scope`).

The proofs read the tree only through `tree_eq`, a definitional check: they hold of the tree the
kernel checked `transfer` erases to, and fail to build for another.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

set_option simprocs false

/-! ## The tree by parts -/

/-- The caller's `balanceOf` slot word. -/
abbrev hC : WExpr := .hash (.lit 8192) (.lit 1)
/-- The recipient's `balanceOf` slot word. -/
abbrev hT : WExpr := .hash (.arg 0) (.lit 1)
/-- The debited balance (wrapping subtraction). -/
abbrev eSub : WExpr := .bin .sub (.sinit hC) (.arg 1)
/-- The recipient's balance in the debited state. -/
abbrev eSel : WExpr := .sel (.bin .eq hT hC) eSub (.sinit hT)
/-- The credited balance (wrapping addition). -/
abbrev eAdd : WExpr := .bin .add eSel (.arg 1)
/-- The address test of `to`. -/
abbrev c1 : WExpr := .bin .gt (.arg 0) (.lit 1461501637330902918203684832716283019655932542975)
/-- SafeMath's `sub` test. -/
abbrev c2 : WExpr := .un .iszero (.bin .lt (.sinit hC) eSub)
/-- SafeMath's `add` test. -/
abbrev c3 : WExpr := .un .iszero (.bin .lt eAdd eSel)

/-- The bytes of `Error(msg)` as constant output bytes. -/
def errBytes (msg : List Nat) : List OByte := (errorData msg).map OByte.lit

/-- The success leaf: return `true`, the credit then the debit, `Transfer(caller, to, v)`. -/
def okLeaf : Tree :=
  .halt true (wordOBytes (.lit 1)) [(hT, eAdd), (hC, eSub)]
    [{ topics := [.lit transferTopic, .lit 8192, .arg 0], data := wordOBytes (.arg 1) }]

-- The erased tree, by parts: the kernel's conversion check.
kernel_rfl tree_eq transfer_tree
  (.ite c1 (.halt false [] [] [])
    (.ite c2 (.ite c3 okLeaf (.halt false (errBytes addMsg) [] [])) (.halt false (errBytes subMsg) [] [])))

/-! ## Evaluating the parts -/

/-- The words `transfer(to, v)` reads from the storage `s`. -/
abbrev val (s : Nat → Nat) (dst v : Nat) : Val := ⟨[dst, v], s, solHash⟩

/-- The tree's result on `transfer(to, v)` from the storage `s`. -/
abbrev res (s : Nat → Nat) (dst v : Nat) : Res := transfer_tree.eval (val s dst v)

theorem modW {n : Nat} (h : n < 2 ^ 256) : n % 2 ^ 256 = n := Nat.mod_eq_of_lt h

theorem ite01_modW (p : Prop) [Decidable p] : (if p then 1 else 0) % 2 ^ 256 = if p then 1 else 0 := by
  split
  · exact modW (by norm_num)
  · exact Nat.zero_mod _

/-- Wrapping subtraction of words. -/
def wsub (a v : Nat) : Nat := (a + (2 ^ 256 - v)) % 2 ^ 256

theorem wsub_of_le {a v : Nat} (ha : a < 2 ^ 256) (h : v ≤ a) : wsub a v = a - v := by
  unfold wsub
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem lt_wsub_iff {a v : Nat} (ha : a < 2 ^ 256) (hv : v < 2 ^ 256) : a < wsub a v ↔ a < v := by
  unfold wsub
  rcases Nat.lt_or_ge (a + (2 ^ 256 - v)) (2 ^ 256) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

theorem add_mod_lt_iff {d v : Nat} (hd : d < 2 ^ 256) (hv : v < 2 ^ 256) :
    (d + v) % 2 ^ 256 < d ↔ 2 ^ 256 ≤ d + v := by
  rcases Nat.lt_or_ge (d + v) (2 ^ 256) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

section
variable {s : Nat → Nat} {dst v : Nat}

/-- The hash of two constant words (stated for variables: the kernel never evaluates Keccak-256 here). -/
theorem ev_hash_lit {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (WExpr.hash (.lit a) (.lit b)).eval (val s dst v) = solHash a b := by
  simp only [WExpr.eval, Generic.wordSize, modW ha, modW hb]
  exact modW (solHash_lt _ _)

theorem ev_hC : hC.eval (val s dst v) = balKey caller :=
  ev_hash_lit (by decide) (by decide)

theorem ev_arg0 (hto : dst < 2 ^ 160) : (WExpr.arg 0).eval (val s dst v) = dst := by
  simp only [WExpr.eval, Generic.wordSize, List.getD_cons_zero]; exact modW (by omega)

theorem ev_arg1 (hv : v < 2 ^ 256) : (WExpr.arg 1).eval (val s dst v) = v := by
  simp only [WExpr.eval, Generic.wordSize, List.getD_cons_succ, List.getD_cons_zero]; exact modW hv

theorem ev_hT (hto : dst < 2 ^ 160) : hT.eval (val s dst v) = balKey dst := by
  simp only [hT, WExpr.eval.eq_8, Generic.wordSize, ev_arg0 hto]
  simp only [WExpr.eval, Generic.wordSize, modW (show 1 < 2 ^ 256 by decide)]
  exact modW (solHash_lt _ _)

variable (hs : ∀ k, s k < 2 ^ 256) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256)
include hs hto hv

theorem ev_a : (WExpr.sinit hC).eval (val s dst v) = s (balKey caller) := by
  simp only [WExpr.eval.eq_6, Generic.wordSize, ev_hC]; exact modW (hs _)

theorem ev_b : (WExpr.sinit hT).eval (val s dst v) = s (balKey dst) := by
  simp only [WExpr.eval.eq_6, Generic.wordSize, ev_hT hto]; exact modW (hs _)

theorem ev_sub : eSub.eval (val s dst v) = wsub (s (balKey caller)) v := by
  simp only [eSub, eval_bin, ev_a hs hto hv, ev_arg1 hv, BinOp.eval, wsub, Generic.wordSize, Nat.mod_mod]

theorem ev_sel : eSel.eval (val s dst v) =
    if balKey dst = balKey caller then wsub (s (balKey caller)) v else s (balKey dst) := by
  simp only [eSel, WExpr.eval.eq_7, eval_bin, Generic.wordSize, ev_hT hto, ev_hC, BinOp.eval, ite01_modW,
    ev_sub hs hto hv, ev_b hs hto hv]
  by_cases h : balKey dst = balKey caller <;> simp [h]

theorem ev_c1 : c1.eval (val s dst v) = 0 := by
  simp only [c1, eval_bin, ev_arg0 hto, eval_lit, Generic.wordSize, modW (show 1461501637330902918203684832716283019655932542975 < 2 ^ 256 by decide),
    BinOp.eval, ite01_modW, Generic.wordSize]
  split_ifs <;> omega

theorem ev_c2 : c2.eval (val s dst v) = if v ≤ s (balKey caller) then 1 else 0 := by
  simp only [c2, WExpr.eval.eq_4, eval_bin, ev_a hs hto hv, ev_sub hs hto hv, BinOp.eval, UnOp.eval,
    ite01_modW, lt_wsub_iff (hs _) hv, Generic.wordSize]
  split_ifs <;> omega

/-- The recipient's balance after the debit, as the tree reads it. -/
theorem ev_sel_debit (hle : v ≤ s (balKey caller)) :
    eSel.eval (val s dst v) = debit s v (balKey dst) := by
  rw [ev_sel hs hto hv, wsub_of_le (hs _) hle]
  simp only [debit, upd, balKey_mod]

theorem ev_c3 (hle : v ≤ s (balKey caller)) :
    c3.eval (val s dst v) = if debit s v (balKey dst) + v < 2 ^ 256 then 1 else 0 := by
  have hd : debit s v (balKey dst) < 2 ^ 256 := by
    rw [← ev_sel_debit hs hto hv hle]; exact WExpr.eval_lt _ _
  simp only [c3, eAdd, WExpr.eval.eq_4, eval_bin, ev_sel_debit hs hto hv hle, ev_arg1 hv, BinOp.eval,
    UnOp.eval, ite01_modW, Generic.wordSize, Nat.mod_mod, add_mod_lt_iff hd hv]
  split_ifs <;> omega

end

/-! ## The tree's result -/

theorem bytes_err (ρ : Val) (msg : List Nat) (h : ∀ b ∈ errorData msg, b < 256) :
    (errBytes msg).map (OByte.eval ρ) = errorData msg := by
  simp only [errBytes, List.map_map]
  conv_rhs => rw [← List.map_id (errorData msg)]
  apply List.map_congr_left
  intro b hb
  exact Nat.mod_eq_of_lt (h b hb)

theorem errorData_add_lt : ∀ b ∈ errorData addMsg, b < 256 := by decide +kernel
theorem errorData_sub_lt : ∀ b ∈ errorData subMsg, b < 256 := by decide +kernel

theorem bytes_word (ρ : Val) (e : WExpr) :
    (wordOBytes e).map (OByte.eval ρ) = be32 (e.eval ρ) := by
  simp only [wordOBytes, be32, List.map_map]
  rfl

/-- The result of a failure with the revert data `Error(msg)`. -/
def failRes (s : Nat → Nat) (msg : List Nat) : Res :=
  { success := false, output := errorData msg, logs := [], store := s }

/-- The result of a success. -/
def okRes (s : Nat → Nat) (dst v : Nat) : Res :=
  { success := true, output := be32 1, logs := [transferLog caller dst v], store := seqStore s dst v }

section
variable {s : Nat → Nat} {dst v : Nat} (hs : ∀ k, s k < 2 ^ 256) (hto : dst < 2 ^ 160) (hv : v < 2 ^ 256)
include hs hto hv

/-- The caller's balance does not cover `v`: SafeMath's `sub` reverts. -/
theorem res_sub (hle : ¬ v ≤ s (balKey caller)) : res s dst v = failRes s subMsg := by
  simp only [res, tree_eq, Tree.eval, ev_c1 hs hto hv, ev_c2 hs hto hv, if_neg hle, if_true,
    eq_self_iff_true, Bool.false_eq_true, if_false, failRes]
  rw [bytes_err _ _ errorData_sub_lt]

/-- The credit overflows: SafeMath's `add` reverts. -/
theorem res_add (hle : v ≤ s (balKey caller)) (hov : ¬ debit s v (balKey dst) + v < 2 ^ 256) :
    res s dst v = failRes s addMsg := by
  simp only [res, tree_eq, Tree.eval, ev_c1 hs hto hv, ev_c2 hs hto hv, ev_c3 hs hto hv hle, if_pos hle,
    if_neg hov, one_ne_zero, if_true, eq_self_iff_true, Bool.false_eq_true, if_false, failRes]
  rw [bytes_err _ _ errorData_add_lt]

/-- Otherwise the call succeeds: the debit, then the credit, the log and `true`. -/
theorem res_ok (hle : v ≤ s (balKey caller)) (hov : debit s v (balKey dst) + v < 2 ^ 256) :
    res s dst v = okRes s dst v := by
  simp only [res, tree_eq, Tree.eval, ev_c1 hs hto hv, ev_c2 hs hto hv, ev_c3 hs hto hv hle, if_pos hle,
    if_pos hov, one_ne_zero, if_true, eq_self_iff_true, if_false, okLeaf, okRes]
  congr 1
  case e_logs =>
    simp only [Log.eval, List.map_cons, List.map_nil, bytes_word, ev_arg1 hv, ev_arg0 hto, eval_lit,
      transferLog, transferTopic, caller, Generic.callerWord, Generic.wordSize,
      modW (show 100389287136786176327247604509743168900146139575972864366142685224231313322991 < 2 ^ 256 by decide),
      modW (show 8192 < 2 ^ 256 by decide)]
  case e_store =>
    funext n
    simp only [Writes.store, ev_hT hto, ev_hC, seqStore, upd, Generic.wordSize]
    rw [show eAdd.eval (val s dst v) = debit s v (balKey dst) + v by
      simp only [eAdd, eval_bin, ev_sel_debit hs hto hv hle, ev_arg1 hv, BinOp.eval, Generic.wordSize,
        Nat.mod_mod]
      exact Nat.mod_eq_of_lt hov]
    rw [ev_sub hs hto hv, wsub_of_le (hs _) hle]
    by_cases h1 : n % 2 ^ 256 = balKey dst
    · rw [if_pos h1.symm, if_pos h1]
    · rw [if_neg (Ne.symm h1), if_neg h1]
      simp only [debit, upd]
      by_cases h2 : n % 2 ^ 256 = balKey caller
      · rw [if_pos h2.symm, if_pos h2]
      · rw [if_neg (Ne.symm h2), if_neg h2]

  all_goals rw [bytes_word, eval_lit, Generic.wordSize, modW (show 1 < 2 ^ 256 by decide)]
end

/-- **The erased tree is `SeqPost`'s source**, from any storage of words. -/
theorem tree_seq (s : Nat → Nat) (hs : ∀ k, s k < 2 ^ 256) (dst v : Nat) (hto : dst < 2 ^ 160)
    (hv : v < 2 ^ 256) :
    ((res s dst v).success = true ↔
      (v ≤ s (balKey caller) ∧ debit s v (balKey dst) + v < 2 ^ 256)) ∧
    ((res s dst v).success = true → (res s dst v).store = seqStore s dst v ∧
      (res s dst v).logs = [transferLog caller dst v] ∧ (res s dst v).output = be32 1) ∧
    ((res s dst v).success = false → (res s dst v).store = s ∧ (res s dst v).logs = [] ∧
      (res s dst v).output = errorData (if v ≤ s (balKey caller) then addMsg else subMsg)) := by
  by_cases hle : v ≤ s (balKey caller)
  · by_cases hov : debit s v (balKey dst) + v < 2 ^ 256
    · rw [res_ok hs hto hv hle hov]; simp [okRes, hle, hov]
    · rw [res_add hs hto hv hle hov]; simp [failRes, hle, hov]
  · rw [res_sub hs hto hv hle]; simp [failRes, hle]

end SolidCore.Spec.UniswapV2.ERC20.Slice

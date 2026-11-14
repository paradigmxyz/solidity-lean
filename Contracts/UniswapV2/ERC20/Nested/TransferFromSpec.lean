import Contracts.UniswapV2.ERC20.Nested.Approve

/-!
# UniswapV2ERC20.transferFrom: its exact result, as sequential storage updates in source order

`transferFromResult st frm dst value` is the source's effect step by step, each read seeing the writes
before it (so any aliasing of the slots is the source's, not assumed away):

1. a dirty address (`frm` or `to` at least `2 ^ 160`) reverts with no data;
2. `a := allowance[frm][caller]`; unless `a` is `type(uint256).max`, `a < value` reverts with SafeMath's
   `ds-math-sub-underflow`, else `allowance[frm][caller] = a - value`;
3. `b := balanceOf[frm]` (reading step 2's storage); `b < value` reverts (`ds-math-sub-underflow`), else
   `balanceOf[frm] = b - value`;
4. `d := balanceOf[to]` (reading step 3's storage); `d + value >= 2 ^ 256` reverts
   (`ds-math-add-overflow`), else `balanceOf[to] = d + value`;
5. `Transfer(frm, to, value)`, returns `true`.

A revert changes no storage and logs nothing. `transferFrom_tree_eval` proves the generic stage's tree
gives exactly this on every argument word and every storage of words, with no hash premise;
`transferFrom_meets` carries it to SolidCore's checked contract on every valid call.
`transferFrom_keys` reads it key by key under `HashScopeNested.Scoped (transferFromFootprint caller frm dst)`:
the three slots are apart, so for `frm ≠ dst` success is `value ≤ a` (or `a` infinite), `value ≤ b` and
`d + value < 2 ^ 256` on the storage before the call, and for `frm = to` the balance is unchanged with
no overflow condition.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes

/-- `keccak256("Transfer(address,address,uint256)")`. -/
abbrev transferTopic : Nat := 100389287136786176327247604509743168900146139575972864366142685224231313322991

/-- `type(uint256).max`. -/
abbrev umax : Nat := 2 ^ 256 - 1

/-- The revert data of `Error(string)` for a message of at most 32 bytes. -/
def errorData (msg : List Nat) : List Nat :=
  [8, 195, 121, 160] ++ word32 32 ++ word32 msg.length ++ msg ++ List.replicate (32 - msg.length) 0

/-- SafeMath's `ds-math-sub-underflow` revert data. -/
def subUnderflow : List Nat := errorData ("ds-math-sub-underflow".toUTF8.toList.map (·.toNat))

/-- SafeMath's `ds-math-add-overflow` revert data. -/
def addOverflow : List Nat := errorData ("ds-math-add-overflow".toUTF8.toList.map (·.toNat))

/-- A revert with data `d`: no change, no log. -/
def revertWith (st : Nat → Nat) (d : List Nat) : Observable :=
  { success := false, output := d, logs := [], storage := st }

/-- Steps 3 to 5 of transferFrom on the storage `s1` after the allowance step. -/
def transferSteps (st s1 : Nat → Nat) (frm dst value : Nat) : Observable :=
  if value ≤ s1 (balanceSlot frm) then
    let s2 := upd s1 (balanceSlot frm) (s1 (balanceSlot frm) - value)
    if s2 (balanceSlot dst) + value < 2 ^ 256 then
      { success := true, output := word32 1, logs := [([transferTopic, frm, dst], word32 value)],
        storage := upd s2 (balanceSlot dst) (s2 (balanceSlot dst) + value) }
    else revertWith st addOverflow
  else revertWith st subUnderflow

/-- **transferFrom(frm, to, value) from the caller on storage `st`**: see the module comment. -/
def transferFromResult (st : Nat → Nat) (frm dst value : Nat) : Observable :=
  if frm < 2 ^ 160 ∧ dst < 2 ^ 160 then
    if st (allowanceSlot frm caller) = umax then transferSteps st st frm dst value
    else if value ≤ st (allowanceSlot frm caller) then
      transferSteps st (upd st (allowanceSlot frm caller) (st (allowanceSlot frm caller) - value)) frm dst value
    else revertWith st subUnderflow
  else revertWith st []

end SolidCore.Spec.UniswapV2.ERC20.Nested

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic

/-! ## The tree, compactly

`tfTree` is `transferFrom_tree` with its words named (`transferFrom_tree_eq`, by `rfl`): the slots `wA`
(`allowance[frm][caller]`), `wF` (`balanceOf[frm]`), `wT` (`balanceOf[dst]`), and each read as the source
makes it after the writes before it (`wbF`: `balanceOf[frm]` after the allowance write, `wdT`:
`balanceOf[dst]` after both). -/

def wV : WExpr := .arg 2
def wA : WExpr := .hash (.lit 8192) (.hash (.arg 0) (.lit 2))
def wF : WExpr := .hash (.arg 0) (.lit 1)
def wT : WExpr := .hash (.arg 1) (.lit 1)
def wA1 : WExpr := .bin .sub (.sinit wA) wV
def wbF : WExpr := .sel (.bin .eq wF wA) wA1 (.sinit wF)
def wbT1 : WExpr := .sel (.bin .eq wT wA) wA1 (.sinit wT)
def wF2 : WExpr := .bin .sub wbF wV
def wdT : WExpr := .sel (.bin .eq wT wF) wF2 wbT1
def wF2n : WExpr := .bin .sub (.sinit wF) wV
def wdTn : WExpr := .sel (.bin .eq wT wF) wF2n (.sinit wT)

/-- A revert with the bytes `b`. -/
def errT (b : List Nat) : Tree := .halt false (b.map OByte.lit) [] []

/-- Success with the writes `ws`: returns `true`, logs `Transfer(frm, dst, value)`. -/
def okT (ws : Writes) : Tree :=
  .halt true (wordOBytes (.lit 1)) ws [⟨[.lit transferTopic, .arg 0, .arg 1], wordOBytes wV⟩]

/-- SafeMath's check `require(x - y <= x)`, as the tree's condition (nonzero: no underflow). -/
def noUnder (x x1 : WExpr) : WExpr := .un .iszero (.bin .lt x x1)

def tfTree : Tree :=
  .ite (.bin .gt (.arg 0) (.lit 1461501637330902918203684832716283019655932542975)) (errT [])
  (.ite (.bin .gt (.arg 1) (.lit 1461501637330902918203684832716283019655932542975)) (errT [])
  (.ite (.un .iszero (.bin .eq (.sinit wA) (.lit (2 ^ 256 - 1))))
    (.ite (noUnder (.sinit wA) wA1)
      (.ite (noUnder wbF wF2)
        (.ite (noUnder (.bin .add wdT wV) wdT)
          (okT [(wT, .bin .add wdT wV), (wF, .bin .sub wbF wV), (wA, wA1)])
          (errT addOverflow))
        (errT subUnderflow))
      (errT subUnderflow))
    (.ite (noUnder (.sinit wF) wF2n)
      (.ite (noUnder (.bin .add wdTn wV) wdTn) (okT [(wT, .bin .add wdTn wV), (wF, wF2n)])
        (errT addOverflow))
      (errT subUnderflow))))

theorem transferFrom_tree_eq : transferFrom_tree = tfTree := by
  decide +kernel

theorem errT_eval (ρ : Val) (b : List Nat) (hb : b.map (· % 256) = b) :
    ((errT b).eval ρ).obs = { success := false, output := b, logs := [], storage := ρ.store } := by
  simp only [errT, Tree.eval, Res.obs, List.map_map, Function.comp_def, OByte.eval]
  simp only [Bool.false_eq_true, if_false, Observable.mk.injEq, and_true, true_and]
  exact hb

theorem wordOBytes_eval (ρ : Val) (e : WExpr) :
    (wordOBytes e).map (OByte.eval ρ) = word32 (e.eval ρ) := by
  simp [wordOBytes, word32, List.map_map, Function.comp_def, OByte.eval]

theorem okT_eval (ρ : Val) (ws : Writes) :
    ((okT ws).eval ρ).obs = (⟨true, word32 1,
      [([transferTopic, ρ.args.getD 0 0 % 2 ^ 256, ρ.args.getD 1 0 % 2 ^ 256],
        word32 (ρ.args.getD 2 0 % 2 ^ 256))], Writes.store ρ ws⟩ : Observable) := by
  simp only [okT, Tree.eval, Res.obs, if_true, List.map_cons, List.map_nil, Log.eval, wordOBytes_eval,
    WExpr.eval, wV, Generic.wordSize]
  simp [word32]
  all_goals decide

theorem eval_ite_obs (ρ : Val) (c : WExpr) (t e : Tree) :
    ((Tree.ite c t e).eval ρ).obs = if c.eval ρ = 0 then (e.eval ρ).obs else (t.eval ρ).obs := by
  simp only [Tree.eval]
  split <;> rfl

theorem subUnderflow_mod : subUnderflow.map (· % 256) = subUnderflow := by decide +kernel
theorem addOverflow_mod : addOverflow.map (· % 256) = addOverflow := by decide +kernel

theorem ite01 (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2 ^ 256 = 0) = ¬p := by
  by_cases h : p <;> simp [h]

set_option maxHeartbeats 4000000 in
/-- **The generic source stage's tree of transferFrom gives exactly `transferFromResult`**, on every
argument word and every storage of words, with no hash premise: the tree's selects on slot equality
are the source's own aliasing, which `upd` reproduces. -/
theorem transferFrom_tree_eval (frm dst value : Nat) (st : Nat → Nat) (hf : frm < 2 ^ 256)
    (ht : dst < 2 ^ 256) (hv : value < 2 ^ 256) (hst : ∀ k, st k < 2 ^ 256) :
    (transferFrom_tree.eval ⟨[frm, dst, value], st, solHash⟩).obs = transferFromResult st frm dst value := by
  have hl := solHash_lt
  simp only [Generic.wordSize] at hl
  have hH : ∀ a b, solHash a b % 2 ^ 256 = solHash a b := fun a b => Nat.mod_eq_of_lt (hl a b)
  have hS : ∀ k, st k % 2 ^ 256 = st k := fun k => Nat.mod_eq_of_lt (hst k)
  have hfN : frm % 2 ^ 256 = frm := Nat.mod_eq_of_lt hf
  have htN : dst % 2 ^ 256 = dst := Nat.mod_eq_of_lt ht
  have hvN : value % 2 ^ 256 = value := Nat.mod_eq_of_lt hv
  rw [transferFrom_tree_eq]
  simp only [tfTree, noUnder, eval_ite_obs, okT_eval, errT_eval _ _ subUnderflow_mod,
    errT_eval _ _ addOverflow_mod, errT_eval _ [] rfl]
  simp only [wA, wF, wT, wV, wA1, wbF, wbT1, wF2, wdT, wF2n, wdTn, WExpr.eval, BinOp.eval, UnOp.eval,
    Writes.store, List.getD_cons_zero, List.getD_cons_succ, Generic.wordSize, hH, hS, hfN, htN, hvN]
  unfold transferFromResult transferSteps revertWith
  simp only [allowanceSlot, balanceSlot, caller, umax]
  have hA := hl 8192 (solHash frm 2)
  have hF := hl frm 1
  have hT := hl dst 1
  have hsA := hst (solHash 8192 (solHash frm 2))
  have hsF := hst (solHash frm 1)
  have hsT := hst (solHash dst 1)
  generalize solHash 8192 (solHash frm 2) = A at *
  generalize solHash frm 1 = F at *
  generalize solHash dst 1 = T at *
  have hAm : A % 2 ^ 256 = A := Nat.mod_eq_of_lt hA
  have hFm : F % 2 ^ 256 = F := Nat.mod_eq_of_lt hF
  have hTm : T % 2 ^ 256 = T := Nat.mod_eq_of_lt hT
  simp only [upd, ite01, not_not, Nat.mod_mod, hAm, hFm, hTm]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMod]
  clear hl hH hS
  split_ifs <;> first
    | (exfalso; omega)
    | (simp only [Observable.mk.injEq, true_and, and_true]
       all_goals first
         | rfl
         | (funext n; (try simp only [upd]); (try dsimp only); split_ifs <;> omega))

end SolidCore.Spec.UniswapV2.ERC20.Nested


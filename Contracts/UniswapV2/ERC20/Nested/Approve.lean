import Contracts.UniswapV2.ERC20.Nested.Trees
import Verify.Spec.HashScopeNested
import Verify.Spec.Tree
import Verify.Shapes

/-!
# UniswapV2ERC20.approve: its exact result, sequentially, and the source's runs meet it

The slot-level statement needs no hash premise: `approveResult st spender value` is the source's
effect in source order (one write `allowance[caller][spender] = value` at the slot SolidCore computes,
`solHash spender (solHash caller 2)`, then the `Approval` log and `true`), and `approve_tree_eval` proves
the generic source stage's tree gives exactly it on every argument word and every storage. The frame
is over that one slot (`approve_frame`): every slot other than the written one keeps its value, said
of slots, never of "all other keys" (which would ask keccak256 to be injective everywhere).

`approve_meets` carries it to SolidCore's checked contract on every valid call of approve (the
generic stage's calls: any argument words, no value, any storage covering the deployed one), by
`source_run`.

`approve_keys` is the key-level reading, under `HashScopeNested.Scoped (approveFootprint caller spender)`
(keccak256 separated on the two preimages this call hashes): the written slot is no small constant
slot, so `totalSupply` (slot 0) and `DOMAIN_SEPARATOR` (slot 3) are unchanged.

Scope: the caller is the stage's (`0x2000`, SolidCore's `msg.sender` on these runs); `SolarTV.Call` has
no caller field, so any-caller is a gap of the shared statement, named in RESULT.md.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes

/-- The stage's caller: `msg.sender` of SolidCore's runs of the generic stage. -/
abbrev caller : Nat := 0x2000

/-- `st` with slot `k` set to `v`; slots are words, so slot `n` is slot `n % 2 ^ 256`. -/
def upd (st : Nat → Nat) (k v : Nat) : Nat → Nat := fun n => if k = n % 2 ^ 256 then v else st n

/-- A word as its 32 big-endian bytes. -/
def word32 (v : Nat) : List Nat := (List.range 32).map fun i => v / 256 ^ (31 - i) % 256

/-- The slot of `allowance[o][s]` (allowance at slot 2), as SolidCore computes it. -/
abbrev allowanceSlot (o s : Nat) : Nat := solHash s (solHash o 2)

/-- The slot of `balanceOf[a]` (balanceOf at slot 1). -/
abbrev balanceSlot (a : Nat) : Nat := solHash a 1

/-- `keccak256("Approval(address,address,uint256)")`. -/
abbrev approvalTopic : Nat := 63486140976153616755203102783360879283472101686154884697241723088393386309925

/-- The argument words of a call: its calldata's words after the selector. -/
def callArgs (call : Call) : List Nat := words ((call.calldata.data.toList.map (·.toNat)).drop 4)

/-- **approve(spender, value) from the caller on storage `st`**: a dirty address reverts with no data
and no change; otherwise `allowance[caller][spender] = value`, `Approval(caller, spender, value)`,
returns `true`. -/
def approveResult (st : Nat → Nat) (spender value : Nat) : Observable :=
  if spender < 2 ^ 160 then
    { success := true, output := word32 1,
      logs := [([approvalTopic, caller, spender], word32 value)],
      storage := upd st (allowanceSlot caller spender) value }
  else { success := false, output := [], logs := [], storage := st }

/-- **The generic source stage's tree of approve gives exactly `approveResult`**, on every argument
word and every storage. -/
theorem approve_tree_eval (spender value : Nat) (st : Nat → Nat) (hs : spender < 2 ^ 256)
    (hv : value < 2 ^ 256) :
    (approve_tree.eval ⟨[spender, value], st, solHash⟩).obs = approveResult st spender value := by
  have hl := solHash_lt
  simp only [Generic.wordSize] at hl
  have hsN : spender % 2 ^ 256 = spender := Nat.mod_eq_of_lt hs
  have hvN : value % 2 ^ 256 = value := Nat.mod_eq_of_lt hv
  have hH : ∀ a b, solHash a b % 2 ^ 256 = solHash a b := fun a b => Nat.mod_eq_of_lt (hl a b)
  simp only [approve_tree, approveResult, Tree.eval, WExpr.eval, BinOp.eval, Res.obs, Generic.wordSize,
    List.getD_cons_zero, List.getD_cons_succ, Writes.store, Log.eval, List.map_cons, List.map_nil,
    OByte.eval, hsN, hvN, hH]
  by_cases h : spender < 2 ^ 160
  · have hn : ¬ (1461501637330902918203684832716283019655932542975 % 2 ^ 256 < spender) := by omega
    simp only [hn, h, if_false, if_true, Nat.zero_mod]
    simp only [Observable.mk.injEq, true_and]
    refine ⟨by simp [word32, List.range_succ], by simp [word32, List.range_succ, caller, approvalTopic], ?_⟩
    funext n
    simp [upd, caller, allowanceSlot]
  · have hn : 1461501637330902918203684832716283019655932542975 < spender := by omega
    have h' : ¬ spender < 1461501637330902918203684832716283019655932542976 := h
    simp [hn, h']

/-- **approve's frame is its one slot**: on success, every slot but `allowance[caller][spender]`'s
keeps its value. Said of slots: no premise on keccak256. -/
theorem approve_frame (st : Nat → Nat) (spender value n : Nat)
    (hn : n % 2 ^ 256 ≠ allowanceSlot caller spender) :
    (approveResult st spender value).storage n = st n := by
  simp only [Nat.reducePow] at hn
  unfold approveResult
  split <;> simp [upd, Ne.symm hn]

/-- The postcondition of every source result on a valid call of approve: exactly `approveResult` of
the call's storage and argument words. -/
def ApprovePost (call : Call) (obs : Observable) : Prop :=
  obs = approveResult (slotValue call.storage) ((callArgs call).getD 0 0) ((callArgs call).getD 1 0)

/-- The valid calls of approve: the generic stage's (any argument words, no value, any storage
covering the deployed one). -/
abbrev ApproveValid (call : Call) : Prop :=
  ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_approve] σ call

/-- **approve's exact result holds of every SolidCore run of the checked UniswapV2ERC20** on its
valid calls. No hash premise. -/
theorem approve_meets {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Meets (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c ApproveValid ApprovePost := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  have hmap := approve_erase_eq
  simp only [approve_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  rintro _ ⟨σ, hcov, fn, hfn, args, hl, hargs, rfl⟩ obs hrun
  simp only [List.mem_singleton] at hfn
  subst hfn
  change Source.run SolidCore.Verify.VC.UniswapV2ERC20.fuel c
    { calldata := SolidCore.Refinement.Abi.calldata 157198259 args, callvalue := 0, storage := σ } = some obs at hrun
  have hrun' := source_run hdd hcov (by decide) hf hT args (by simpa [fn_approve] using hl.trans hlen.symm) hargs
  rw [hrun'] at hrun
  cases hrun
  match args, hl, hargs with
  | [spender, value], _, hargs =>
    have h0 := hargs spender (by simp)
    have h1 := hargs value (by simp)
    unfold ApprovePost callArgs
    rw [words_calldata _ hargs]
    exact approve_tree_eval spender value _ h0 h1

/-- **approve, key by key, on its footprint**: under keccak256's separation on the two preimages of
`allowance[caller][spender]`'s slot, a clean call succeeds, `allowance[caller][spender]` is `value`,
and every small constant slot (`totalSupply` at 0, `DOMAIN_SEPARATOR` at 3) is unchanged. -/
theorem approve_keys (st : Nat → Nat) (spender value : Nat) (hsp : spender < 2 ^ 160)
    (h : HashScopeNested.Scoped (HashScopeNested.approveFootprint caller spender)) :
    (approveResult st spender value).success = true ∧
      (approveResult st spender value).storage (allowanceSlot caller spender) = value ∧
      ∀ k < 2 ^ 128, (approveResult st spender value).storage k = st k := by
  have hge := HashScopeNested.approve_slot h
  have hlt := solHash_lt spender (solHash caller 2)
  unfold Generic.wordSize at hlt
  have hsp' : spender < 1461501637330902918203684832716283019655932542976 := hsp
  have hlt' : allowanceSlot caller spender < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hlt
  refine ⟨by simp [approveResult, hsp'], by simp [approveResult, hsp', upd, Nat.mod_eq_of_lt hlt'], ?_⟩
  intro k hk
  have hk' : k % 2 ^ 256 = k := Nat.mod_eq_of_lt (by omega)
  exact approve_frame st spender value k (by rw [hk']; intro e; simp only [allowanceSlot] at e; omega)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms approve_meets

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms approve_keys

end SolidCore.Spec.UniswapV2.ERC20.Nested

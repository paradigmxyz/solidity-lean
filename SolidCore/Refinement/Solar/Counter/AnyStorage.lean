import SolidCore.Refinement.Solar.Counter.Assembly
import SolidCore.Refinement.Spec

/-!
NOTE: ckpt3's SpecAt.lean, LoweringAt.lean and AssemblyAt.lean prove the same theorems under
the same names, which Counter.Milestone imports, so this module imports only what the
deployed-storage milestone needs and is not imported beside them.

# The counter milestone from any storage

`certified` (Milestone.lean) proves Counter's `inc` on calls from the deployed, empty storage,
where `x = 0`. A sequence of calls starts each call from the storage the previous one left, so
this module proves every stage of solar's pipeline, and the specification, from any storage `σ`:
`scopeAt` is every call of `inc` on any argument word below `2 ^ 256`, with no value, from any
storage. There the overflow branch is reached, and `expectedAt σ d` is what a call shows: when
`x + d` fits, with `x` slot 0 of `σ`, success with slot 0 holding `x + d` and every other slot
of `σ` kept; otherwise a revert with `Panic(0x11)` and `σ` kept.

* Specification: `vcsAt` is `vcs` for each `σ` (Loom's weakest preconditions of `model` against
  the existing `post`, which is stated from any storage), and `run_inc_at` runs SolidCore from
  `σ` written over the deployed storage (`run_eq_at`, `getD_storage`), giving `implementsAt`,
  `specAt` and `satisfiesAt`.
* Source stage: `loweringAt`, from `source_run_at` and `mir_run_at` (symbolic execution of
  `stage0` with slot 0 read from `σ` and both branches of the overflow check).
* Backend: `SolarTV.Milestone.Counter.counter_mir_to_evmir`, already on every call.
* Assembly stage: `stageAt`, from `evmir_run_at` and `target_run_at`: EthLib's run of the
  bytecode from `σ` (`run_of_postS_at`), SLOAD reading `σ`'s slot 0
  (`getStorage_preState_word`), and the final storage read through the write
  (`getStorage_writeOf_any`) on the success path, and REVERT with `Panic(0x11)` on the overflow
  path (`target_run_ok`, `target_run_overflow`).
* `certifiedAt`: the bytecode meets `post` on every call of `scopeAt`, through every stage.

Nothing here uses `native_decide` or `bv_decide`.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Verify

/-- Every call of `inc` on any argument word, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope fns σ call

/-- What a call of `inc(d)` from the storage `σ` shows: with `x` slot 0 of `σ`, success with
slot 0 holding `x + d` and every other slot kept when `x + d` fits in 256 bits, and otherwise a
revert with `Panic(0x11)` and `σ` kept. -/
def expectedAt (σ : List (Nat × Nat)) (d : U256) : Observable :=
  if slotValue σ 0 + d.toNat < 2 ^ 256 then
    { success := true, output := [], logs := [],
      storage := fun slot => if slot % 2 ^ 256 = 0 then slotValue σ 0 + d.toNat else slotValue σ slot }
  else { success := false, output := panic 0x11, logs := [], storage := slotValue σ }

theorem scopeAt_callOf {call : Call} (h : scopeAt call) :
    ∃ d : U256, ∃ σ, call = { callOf incSelector [d] with storage := σ } := by
  obtain ⟨σ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, σ, ?_⟩
    have ha' : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callOf, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha']

/-- `model` from the storage `σ` shows `expectedAt σ d`. -/
theorem observe_model_at (d : U256) (σ : List (Nat × Nat)) :
    observe (slotValue σ) (model [d.toNat] (slotValue σ)) = expectedAt σ d := by
  unfold model expectedAt
  by_cases h : slotValue σ 0 + d.toNat < 2 ^ 256
  · simp only [sload, sstore, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
      List.getD_cons_zero, h, ↓reduceIte, observe, Nat.zero_mod, Nat.mod_eq_of_lt h]
  · simp only [sload, bind, StateT.bind, Except.bind, List.getD_cons_zero, h, ↓reduceIte,
      observe, revert]

/-- The verification conditions of `inc` from any storage, by Loom's weakest preconditions. -/
theorem vcsAt : ∀ call, scopeAt call → pre call → vc model (argWords 1) post call := by
  rintro call ⟨σ, hs⟩ hp
  refine vcs_of_fullScope (s := σ) (by simp [fns]) ?_ call hs hp
  intro fn hfn call args hcall hw hlen hargs hinit hpre
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst fn hcall
  rcases args with _ | ⟨a, _ | _⟩ <;> simp at hlen
  have ha : a < 2 ^ 256 := hargs a (by simp)
  simp only [model, post, hw, wp_bind, wp_pure, wp_sload, wp_sstore, wp_revert, wp_ite,
    List.getD_cons_zero]
  by_cases h : slotValue σ 0 + a < 2 ^ 256
  · simp only [h, ↓reduceIte, Nat.zero_mod, Nat.mod_eq_of_lt h]
    simp
  · simp only [h, ↓reduceIte]
    simp

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs `inc` on any argument word from any storage `σ` as `model` does. -/
theorem run_inc_at {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) (w : U256) (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt incSelector [w] σ) =
      some (Verify.observe (slotValue σ) (model [w.toNat] (slotValue σ))) := by
  rw [run_eq_at hd]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  simp only [hcore, List.map_cons, List.map_nil]
  have hx0 : m[0]?.getD 0 = slotValue σ 0 := by simpa using hget 0
  have hN : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  have hlt := slotValue_lt σ 0
  have hw := w.isLt
  rw [hN] at hlt hw
  wide_symex [coreLit, fuel, ctxOf, hcore, incSelector, get?_insert]
  case pos =>
    rename_i hp
    have hnot : ¬ slotValue σ 0 + w.toNat < 2 ^ 256 := by
      split at hp
      · rename_i v heq
        have hv : v = slotValue σ 0 := by simpa [heq] using hx0
        rw [hv] at hp
        omega
      · rename_i heq
        have hv : slotValue σ 0 = 0 := by simpa [heq] using hx0.symm
        rw [hv]
        omega
    simp only [model, sload, bind, StateT.bind, Except.bind, List.getD_cons_zero, hnot, ↓reduceIte,
      revert]
    simp [Source.observe, Verify.observe, callAt]
    rfl
  case h_1 =>
    rename_i hp _ v heq
    have hv : v = slotValue σ 0 := by simpa [heq] using hx0
    subst hv
    simp only [heq] at hp
    have hyes : slotValue σ 0 + w.toNat < 2 ^ 256 := by omega
    have hyes' : slotValue σ 0 + w.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by omega
    simp only [model, sload, sstore, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, List.getD_cons_zero, hyes, ↓reduceIte, Verify.observe, Nat.mod_eq_of_lt hyes]
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?]
    funext slot
    have hs := hget slot
    rw [hN] at hs
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, beq_iff_eq,
      EvmYul.UInt256.size]
    by_cases h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp [h, Nat.mod_eq_of_lt hyes']
    · have h' : ¬ 0 = slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := fun e => h e.symm
      simp only [h, h', ↓reduceIte]
      rw [← hs]
      cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl
  case h_2 =>
    rename_i hp _ heq
    have hv : slotValue σ 0 = 0 := by simpa [heq] using hx0.symm
    have hyes : slotValue σ 0 + w.toNat < 2 ^ 256 := by rw [hv, hN]; omega
    simp only [model, sload, sstore, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, List.getD_cons_zero, hyes, ↓reduceIte, Verify.observe, Nat.mod_eq_of_lt hyes]
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?]
    funext slot
    have hs := hget slot
    rw [hN] at hs
    simp only [Std.HashMap.getElem?_insert, Shared.norm, Shared.wordModulus, beq_iff_eq,
      EvmYul.UInt256.size]
    by_cases h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp [h, hv]
    · have h' : ¬ 0 = slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := fun e => h e.symm
      simp only [h, h', ↓reduceIte]
      rw [← hs]
      cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl

section Lowering

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

/-- SolarTV's lowered MIR runs Counter's first lowered MIR module, on every call whose call data
reads as `inc(d)` with no value, to `expectedAt` of the call's storage. -/
theorem mir_run_of_at (o : Oracle) (call : Call) (d : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455)
    (h4 : calldataWord call 4 = d) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (expectedAt call.storage d) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  have hx : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    simp only [State.initial, BitVec.toNat_ofNat]
    exact slotValue_mod_mod call.storage 0
  by_cases hof : slotValue call.storage 0 + d.toNat < 2 ^ 256
  all_goals
    simp only [add_lt_self_iff_comm, hx, hof, not_true_eq_false,
      not_false_eq_true, ↓reduceIte]
    repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  · simp only [Machine.observe, expectedAt, hof, ↓reduceIte, Option.some.injEq,
      Observable.mk.injEq, true_and]
    refine ⟨rfl, ?_⟩
    funext slot
    simp only [storageOf, update]
    split
    · rename_i e
      have h : slot % 2 ^ 256 = 0 := by simpa using congrArg BitVec.toNat e
      simp only [h, ↓reduceIte, EvmRules.Evm.add, BitVec.toNat_add, hx]
      rw [Nat.add_comm (BitVec.toNat d)]
      exact Nat.mod_eq_of_lt hof
    · rename_i e
      have h : ¬ slot % 2 ^ 256 = 0 :=
        fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [h, ↓reduceIte, State.initial, BitVec.toNat_ofNat]
      exact slotValue_mod_mod call.storage slot
  · simp only [Machine.observe, expectedAt, hof, ↓reduceIte, Option.some.injEq,
      Observable.mk.injEq]
    refine ⟨trivial, ?_, trivial, trivial⟩
    try simp only [State.initial]
    decide

end Lowering

section Target

open EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts EthLib.Execution.State
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm

/-- `run_of_postS` from any storage `σ`: when the frame of every message of the call stops as
`PostS X` says from the call's state before it, `Target.run` of the call is `X`, when `X`
shows no logs and keeps `σ` when it fails. -/
theorem run_of_postS_at (code : ByteArray) (s : Nat) (ws : List U256) (σ : List (Nat × Nat))
    (X : Observable) (hlogs : X.logs = [])
    (hfail : X.success = false → ∀ slot, X.storage slot = slotValue σ slot)
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      msg.isStatic = false → msg.currentTarget = Target.address selfAddress →
      Spec .fusaka (At code msg 0 [] .empty 10000000
        (Target.preState code { callOf s ws with storage := σ }) Substate.empty .empty)
        (PostS X Substate.empty)) :
    Target.run code { callOf s ws with storage := σ } = some X := by
  have hd : Abi.calldata s (ws.map BitVec.toNat) = cdOf (selectorOf s) ws := by
    rw [calldata_eq_cdOf s _ (by simpa using fun a _ => a.isLt)]
    simp [List.map_map, Function.comp_def]
  let c : Call := { callOf s ws with storage := σ }
  obtain ⟨evm, hr, herr, hout, hst⟩ := processMessage_postS (Target.message code c) rfl rfl
    (precompileAddress_message code c) X (Target.preState code c) Substate.empty
    (h _ rfl (by simp [Target.message, c, callOf, hd]) rfl rfl)
  show Target.run code c = some X
  simp only [Target.run, hr]
  have hsucc : evm.1.error.isNone = X.success := by
    rw [herr]; cases hX : X.success <;> simp [errorOf, hX]
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout hlogs hfail hst ⊢
    subst hlogs
    rw [Observable.mk.injEq]
    refine ⟨hsucc, hout, ?_, ?_⟩
    · rw [hsucc]
      cases hs : success
      · rfl
      · simp [(hst hs).1, Substate.empty]
    · funext slot
      rw [hsucc]
      cases hs : success
      · simp [c, hfail hs slot]
      · simp only [ite_true]
        exact (hst hs).2 slot

/-- A read of the callee's storage before the call, at the key of a word, is the call's slot. -/
theorem getStorage_preState_word (code : ByteArray) (c : Call) (key : U256) :
    (Target.preState code c).getStorage (Target.address selfAddress) (U256.toBeBytes key) =
      BitVec.ofNat 256 (slotValue c.storage key.toNat) := by
  have hk : U256.toBeBytes key = Target.storageKey key.toNat :=
    ((storageKey_eq_toBeBytes key.toNat key).2 (Nat.mod_eq_of_lt key.isLt)).symm
  rw [hk]
  apply BitVec.eq_of_toNat_eq
  rw [getStorage_preState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt _ _)]

/-- After a write of `v` at `k` of `a`, the written slot holds `v` and every other slot is
as before. -/
theorem getStorage_writeOf_any (tx : TransactionState) (a : Address) (k : Bytes32) (v : U256)
    (a' : Address) (k' : Bytes32) :
    (writeOf tx a k v).getStorage a' k' = if a' = a ∧ k' = k then v else tx.getStorage a' k' := by
  simp only [writeOf, TransactionState.getStorage, TransactionState.recordAccountRead, StorageMap.slot]
  by_cases ha : a' = a
  · subst ha
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, Std.ExtTreeMap.getElem?_insert]
      simp only [show ¬ (k = k') from fun e => hk e.symm, ↓reduceIte]
      have : (Std.ExtTreeMap.getD tx.storageWrites a' ∅)[k']? =
          tx.storageWrites[a']?.bind fun slots => slots[k']? := by
        rw [Std.ExtTreeMap.getD_eq_getD_getElem?]
        cases tx.storageWrites[a']? <;> simp
      rw [this]
      rfl
  · simp [ha, Std.ExtTreeMap.getElem?_insert]
    simp only [show ¬ (a = a') from fun e => ha e.symm, ↓reduceIte]
    rfl

open Lean.Parser.Tactic in
/-- Steps one opcode of a path of `inc` from any storage: SLOAD of slot 0 (a cold key, read as
`σ`'s slot 0), SSTORE after it, and every other opcode as `wide_one_s`. -/
syntax "counter_at_one" " [" simpLemma,* "]" " [" simpLemma,* "]" ident ident ident : tactic

macro_rules
  | `(tactic| counter_at_one [$ls,*] [$ns,*] $hf $hstat $htgt) => `(tactic| ((try unfold Spec) <;> first
      | (refine' Triple.seq (sload (cold := true) (by decide) ?lt ?op ?cold ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case cold => simp [Substate.empty]
         case gas => simp only [ite_true]; omega) <;>
        (try simp only [$htgt:ident, getStorage_preState_word, Bool.true_eq, ↓reduceIte,
          Nat.reduceSub]) <;> evm_tidy
      | (refine' Triple.seq (sstore (by decide) (by decide) ?lt ?op $hstat rfl ?stip ?gas
          (setStorage_ok _ _ ?acc)) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case stip => simp only [CALL_STIPEND]; omega
         case gas => exact Nat.le_trans (sstoreCost_le _ _ _ _) (by omega)
         case acc => simp only [getAccountOptional_recordStorageRead, $htgt:ident]
                     exact account_preState _ _) <;> evm_tidy
      | wide_one_s [$ls,*] [$ns,*] $hf $hstat $htgt))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- When `x + d` fits, EthLib runs solar's bytecode on `inc(d)` from `σ` to `expectedAt σ d`:
every opcode stepped from pc 0 with 10M gas, SLOAD's read of `σ` and SSTORE's write and price
included. -/
theorem target_run_ok (d : U256) (σ : List (Nat × Nat)) (hof : slotValue σ 0 + d.toNat < 2 ^ 256) :
    Target.run code { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) := by
  have he : expectedAt σ d = ⟨true, [], [], fun slot =>
      if slot % 2 ^ 256 = 0 then slotValue σ 0 + d.toNat else slotValue σ slot⟩ := by
    simp only [expectedAt, hof, ↓reduceIte]
  rw [he]
  refine run_of_postS_at code incSelector [d] σ _ rfl (fun h => by cases h) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [incSelector] at hd
  repeat counter_at_one [code, runtimeNat, runtimeSize, incSelector] [hd, hv] hfork hstat htgt
  refine stop_postS ?lt ?op rfl rfl rfl ?store
  case lt => evm_code [code, runtimeNat, runtimeSize, incSelector]
  case op => evm_code [code, runtimeNat, runtimeSize, incSelector]
  case store =>
    intro slot
    have hrd : ∀ (tx : TransactionState) a k a' k',
        (tx.recordStorageRead a k).getStorage a' k' = tx.getStorage a' k' :=
      fun _ _ _ _ _ => rfl
    rw [htgt, getStorage_writeOf_any, hrd, hrd]
    have hk : Target.storageKey slot = U256.toBeBytes 0#256 ↔ slot % 2 ^ 256 = 0 :=
      storageKey_eq_toBeBytes slot 0#256
    by_cases h : slot % 2 ^ 256 = 0
    · have h' : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := h
      simp only [hk.2 h, and_self, ↓reduceIte, h']
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt σ 0),
        Nat.mod_eq_of_lt hof]
    · have h' : ¬ slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := h
      simp only [show ¬ Target.storageKey slot = U256.toBeBytes 0#256 from fun e => h (hk.1 e),
        and_false, ↓reduceIte, h']
      exact getStorage_preState code _ slot

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- When `x + d` overflows, EthLib's run of the bytecode reverts with `Panic(0x11)`. -/
theorem target_run_overflow (d : U256) (σ : List (Nat × Nat))
    (hof : ¬ slotValue σ 0 + d.toNat < 2 ^ 256) :
    Target.run code { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) := by
  have he : expectedAt σ d = ⟨false, panic 0x11, [], slotValue σ⟩ := by
    simp only [expectedAt, hof, ↓reduceIte]
  rw [he]
  refine run_of_postS_at code incSelector [d] σ _ rfl (fun _ _ => rfl) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [incSelector] at hd
  have hc : BitVec.ofNat 256 (slotValue σ 0) + d < BitVec.ofNat 256 (slotValue σ 0) := by
    have hN : (2 : Nat) ^ 256 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num
    have hlt := slotValue_lt σ 0
    have hw := d.isLt
    rw [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hN] at hlt hw hof ⊢
    omega
  repeat counter_at_one [code, runtimeNat, runtimeSize, incSelector] [hd, hv, hc] hfork hstat htgt
  refine revert_postS (by decide) ?_ ?_ ?_ rfl ?_ rfl
  · evm_code [code, runtimeNat, runtimeSize, incSelector]
  · evm_code [code, runtimeNat, runtimeSize, incSelector]
  · wide_mem
  · simp only [Verify.panic, Verify.word]
    decide +kernel

/-- EthLib runs solar's bytecode on every call of `inc(d)` from any storage `σ` to
`expectedAt σ d`. -/
theorem target_run_at (d : U256) (σ : List (Nat × Nat)) :
    Target.run code { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) := by
  by_cases hof : slotValue σ 0 + d.toNat < 2 ^ 256
  · exact target_run_ok d σ hof
  · exact target_run_overflow d σ hof

end Target

section Stages

open SolarTV SolarTV.Machine

/-- SolarTV's lowered MIR runs `stage0` on `inc(d)` from any storage `σ` to `expectedAt σ d`. -/
theorem mir_run_at (o : Oracle) (d : U256) (σ : List (Nat × Nat)) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Counter.stage0
        { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) :=
  SolidCore.Refinement.Solar.W1.mir_sem_of_run 9
    (mir_run_of_at o _ d rfl (size_callOf d)
      (by have h := word0 d; rw [show BitVec.ofNat 256 incSelector = 2166751455 from rfl] at h; exact h)
      (word4 d))

/-- SolarTV's EVM IR runs `evm5` on `inc(d)` from any storage `σ` to `expectedAt σ d`. -/
theorem evmir_run_at (o : Oracle) (d : U256) (σ : List (Nat × Nat)) :
    (SolarTV.evmirSem o).run SolarTV.Export.Counter.evm5
        { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) :=
  SolarTV.Milestone.Counter.counter_mir_to_evmir o _ trivial _ (mir_run_at o d σ)

end Stages

/-- `model` implements SolidCore's `Counter` on every call of `scopeAt`. -/
theorem implementsAt {c : TypeCheck.CheckedContract} (hcore : c.core = coreLit) {d : Source.State}
    (hd : DeployedAt fuel c d []) : Implements fuel c scopeAt (argWords 1) model := by
  rintro call ⟨σ, hs⟩
  refine implements_of_run' (s := σ) (by simp [fns]) (fun fn hfn ws hl => ?_) call hs
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  subst hfn
  rcases ws with _ | ⟨w, _ | _⟩ <;> simp at hl
  exact run_inc_at hcore hd w σ

/-- **The specification of Counter's `inc` from any storage**, as a triple against SolidCore. -/
theorem specAt : ∃ c, contract? = .ok c ∧ Triple fuel c scopeAt pre post := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨c, hc, triple_of_wp (implementsAt hk (deployedAt_of_deployed hd)) vcsAt⟩

/-- The specification from any storage as `Satisfies` on SolidCore. -/
theorem satisfiesAt : ∃ c, contract? = .ok c ∧ Satisfies (solidCore fuel) c scopeAt pre post := by
  obtain ⟨c, hc, h⟩ := specAt
  exact ⟨c, hc, satisfies_of_triple h⟩

/-- SolidCore runs `inc` on any argument word from any storage `σ` to `expectedAt σ d`. -/
theorem source_run_at {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (w : U256)
    (σ : List (Nat × Nat)) :
    Source.run fuel c { callOf incSelector [w] with storage := σ } = some (expectedAt σ w) := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  have := run_inc_at hk (deployedAt_of_deployed hd) w σ
  rw [observe_model_at] at this
  exact this

/-- **The source stage of Counter from any storage**: SolidCore to solar's first lowered MIR on
every call of `inc` with no value from any storage, under every oracle. -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      scopeAt := by
  intro call hscope obs hrun
  obtain ⟨d, σ, rfl⟩ := scopeAt_callOf hscope
  change Source.run fuel c { callOf incSelector [d] with storage := σ } = some obs at hrun
  rw [source_run_at hc d σ] at hrun
  cases hrun
  exact mir_run_at o d σ

/-- **The assembly stage of Counter from any storage**: EVM IR to bytecode on EthLib on every
call of `inc` with no value from any storage, under every oracle. -/
theorem stageAt (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scopeAt := by
  intro call hc obs hrun
  obtain ⟨d, σ, rfl⟩ := scopeAt_callOf hc
  rw [evmir_run_at o d σ] at hrun
  cases hrun
  exact target_run_at d σ

/-- **The counter milestone from any storage.** solar's runtime bytecode for Counter meets the
specification of `inc` (`post`: slot 0 holds `x + d` and every other slot is kept when `x + d`
fits, otherwise a revert with `Panic(0x11)` keeping the storage, never a log) on every call of
`inc` with no value from any storage, under EthLib, through every stage of solar's pipeline, each
proved from any storage. -/
theorem certifiedAt : Satisfies ethLib code scopeAt pre post := by
  obtain ⟨c, hc, hspec⟩ := satisfiesAt
  exact bytecode_of_stages hspec (loweringAt W1.oracle hc)
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir W1.oracle).mono fun _ _ => trivial)
    (stageAt W1.oracle)

/-- info: 'SolidCore.Refinement.Solar.Counter.stageAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAt

/-- info: 'SolidCore.Refinement.Solar.Counter.certifiedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedAt

end SolidCore.Refinement.Solar.Counter























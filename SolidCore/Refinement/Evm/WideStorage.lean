import SolidCore.Refinement.Evm.Wide
import SolidCore.Refinement.Check

/-!
# Symbolic execution of a function that writes storage

`Evm.Wide`'s `Post` asks a frame to keep the state it started from, so it covers
functions that only compute. A function that writes storage changes the state: SSTORE
records the write in the transaction state and the access and refund in the substate.
This module states what such a call shows and steps SSTORE and STOP.

* `PostS X ss`: the frame stops with `X`'s error and output, its logs are those of `ss`,
  and, when `X` succeeds, every slot of the callee's storage holds `X.storage`'s word.
* `run_of_postS` turns a frame specification from `Target.preState` into
  `Target.run code call = some X`, as `run_of_post` does for a frame that keeps its state.
* `sstoreCost_le` bounds the price of SSTORE at Fusaka, and `setStorage_ok` gives the
  state a write to an account that exists leaves, `writeOf`.
* `getStorage_writeOf` reads the storage after one write from the empty storage of the
  call, which `stop_postS` compares with SolidCore's storage slot by slot.
* `getStorage_preState` reads the callee's storage before the call as the call's, and
  `run_of_post_at` is `run_of_post` from any storage, for a frame that keeps its state.
* `wide_tgt_s [rules]` is `wide_tgt` with SSTORE and STOP: it proves the frame hypothesis
  of `run_of_postS` for a function that writes one slot and stops.

A contract whose constructor leaves storage is called from it, `callAt sel ws σ`:

* `run_of_postS_at` is `run_of_postS` for such a call, whose failure keeps the words of `σ`;
* `getStorage_preState_ofNat` reads a slot of the callee's storage before the call as the
  word `slotValue σ`, and `getStorage_writeOf_of` the storage after a write to any state;
* `sload_then` and `sstore_then` step SLOAD and SSTORE, each at a price bounded by its most
  expensive case, so that the rest of a path may spend the gas left;
* `wide_tgt_at [rules]` is `wide_tgt_s` with SLOAD, for such a call. Where evaluation and
  `bv_omega` leave a word to compare that depends on bit operations of an argument word whose
  path condition bounds it below `2 ^ 8`, `word_decide` evaluates it on every such word in the
  kernel.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace SolidCore.Refinement.Evm.Wide

variable {fork : Fork}

/-- The frame stopped as `X` shows, with the logs of `ss`, and on success with `X`'s storage at
the callee. -/
def PostS (X : Observable) (ss : Substate) (evm : Evm fork Nat) : Prop :=
  evm.error = errorOf X ∧ evm.output.toList.map (·.toNat) = X.output ∧
    evm.substate.logs = ss.logs ∧
    (X.success = true → ∀ slot, (evm.state.getStorage (Target.address selfAddress)
      (Target.storageKey slot)).toNat = X.storage slot)

/-- `processMessage` at Fusaka of a message with no value, to code that is no precompile, whose
frame from `st` and `ss` stops as `PostS X ss` says. -/
theorem processMessage_postS {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (hv : message.value = 0)
    (hpre : precompileAddress .fusaka message = none) (X : Observable)
    (st : State.TransactionState) (ss : Substate)
    (h : Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) (PostS X ss)) :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = errorOf X ∧ evm.1.output.toList.map (·.toNat) = X.output ∧
      (X.success = true → evm.1.substate.logs = ss.logs ∧ ∀ slot,
        (evm.1.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
          X.storage slot) := by
  rw [processMessage]
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre]
  split
  · rename_i htr; exact absurd htr.2 (by simp [hv])
  simp only [pure, Except.pure, bind, Except.bind]
  split
  · rename_i e hr
    simp only [hv, ne_eq, not_true_eq_false, and_false, ite_false] at hr
    obtain ⟨after, h', -⟩ := runFrame_of_spec hcode h hr
    cases h'
  · rename_i after hr
    simp only [hv, ne_eq, not_true_eq_false, and_false, ite_false] at hr
    obtain ⟨after', h', -, herr, hout, hlogs, hst⟩ := runFrame_of_spec hcode h hr
    cases h'
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> exact hout
    · intro hX
      have hE : errorOf X = none := by simp [errorOf, hX]
      simp only [rollbackOnError, herr, hE, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlogs, hst hX⟩

/-- The frame of every message of the call, from the call's state before it, stops as `PostS X`
says: `Target.run` of the call is `X`, when `X` shows no logs and keeps the empty storage when it
fails. -/
theorem run_of_postS (code : ByteArray) (s : Nat) (ws : List U256) (X : Observable)
    (hlogs : X.logs = []) (hfail : X.success = false → ∀ slot, X.storage slot = 0)
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      msg.isStatic = false → msg.currentTarget = Target.address selfAddress →
      Spec .fusaka (At code msg 0 [] .empty 10000000 (Target.preState code (callOf s ws))
        Substate.empty .empty) (PostS X Substate.empty)) :
    Target.run code (callOf s ws) = some X := by
  have hd : Abi.calldata s (ws.map BitVec.toNat) = cdOf (selectorOf s) ws := by
    rw [calldata_eq_cdOf s _ (by simpa using fun a _ => a.isLt)]
    simp [List.map_map, Function.comp_def]
  let c := callOf s ws
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
      · simp [slotValue, c, callOf, hfail hs slot]
      · simp only [ite_true]
        exact (hst hs).2 slot

/-- SSTORE at Fusaka costs at most a cold access and a new slot. -/
theorem sstoreCost_le (o c n : U256) (cold : Bool) : sstoreCost .fusaka o c n cold ≤ 22100 := by
  unfold sstoreCost sstoreResetCost sstoreReadCost
  simp only [show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, show Fork.fusaka ≥ Fork.istanbul by decide,
    show Fork.fusaka ≥ Fork.berlin by decide, ite_true, ite_false]
  simp only [COLD_STORAGE_ACCESS, STORAGE_SET, COLD_STORAGE_WRITE, WARM_ACCESS]
  split <;> split <;> (try split) <;> omega

/-- The state a write of `v` at key `k` of an account that exists leaves. -/
def writeOf (tx : TransactionState) (a : Address) (k : Bytes32) (v : U256) : TransactionState :=
  let tx := tx.recordAccountRead a
  { tx with storageWrites := tx.storageWrites.insert a ((tx.storageWrites.getD a ∅).insert k v) }

theorem setStorage_ok {tx : TransactionState} {a : Address} (k : Bytes32) (v : U256)
    (h : tx.getAccountOptional a ≠ none) : tx.setStorage a k v = .ok (writeOf tx a k v) := by
  unfold TransactionState.setStorage
  simp [h, writeOf]

theorem account_preState (code : ByteArray) (c : Call) :
    (Target.preState code c).getAccountOptional (Target.address selfAddress) ≠ none := by
  simp only [Target.preState, TransactionState.getAccountOptional, TransactionState.ofBlock,
    State.getAccountOptional]
  rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right (by decide +kernel), Std.ExtTreeMap.getElem?_insert,
    ite_eq_left (by decide +kernel)]
  simp

/-- The storage after one write to the account of the call, from the empty storage of a call
with no initial storage: the written word at its key, zero elsewhere. -/
theorem getStorage_writeOf (code : ByteArray) (c : Call) (hst : c.storage = []) (a : Address)
    (k : Bytes32) (v : U256) (a' : Address) (k' : Bytes32) :
    (writeOf ((Target.preState code c).recordStorageRead a k) a k v).getStorage a' k' =
      if a' = a ∧ k' = k then v else 0 := by
  simp only [writeOf, TransactionState.getStorage, TransactionState.recordAccountRead,
    TransactionState.recordStorageRead, Target.preState, hst, List.foldl_nil,
    TransactionState.ofBlock, StorageMap.slot]
  by_cases ha : a' = a
  · subst ha
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, Std.ExtTreeMap.getElem?_insert, State.getStorage, StorageMap.slot]
      simp only [show (k = k') = False from eq_false (fun h => hk h.symm), ite_false]
      by_cases h : Target.address selfAddress = a' <;> simp [h]
  · simp [ha, Std.ExtTreeMap.getElem?_insert, State.getStorage, StorageMap.slot]
    simp only [show (a = a') = False from eq_false (fun h => ha h.symm), ite_false,
      Option.bind_none]
    by_cases h : Target.address selfAddress = a' <;> simp [h]

/-- The storage key of a slot is the key of a word when the slot is the word modulo 2^256. -/
theorem storageKey_eq_toBeBytes (slot : Nat) (key : U256) :
    Target.storageKey slot = U256.toBeBytes key ↔ slot % 2 ^ 256 = key.toNat := by
  rw [SolidCore.Refinement.storageKey_mod]
  constructor
  · intro h
    have := congrArg (fun v : Bytes32 => bytesToNat v.toList) h
    simp only [SolidCore.Refinement.toList_storageKey, EthLib.Base.U256.toList_toBeBytes,
      bytesToNat_natToBytes] at this
    have hk := key.isLt
    simp [SolidCore.Refinement.wordSize] at this
    omega
  · intro h
    apply Vector.toList_inj.mp
    rw [SolidCore.Refinement.toList_storageKey, EthLib.Base.U256.toList_toBeBytes]
    exact congrArg _ h

/-- STOP shows `X` when `X` succeeds with no output, the frame's logs are those of `ss`, and
its storage is `X`'s. -/
theorem stop_postS {X : Observable} {ss : Substate} {code : ByteArray} {message : Message fork}
    {pc : Nat} {stack : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x00) (hs : X.success = true) (hout : X.output = [])
    (hlogs : substate.logs = ss.logs)
    (hstore : ∀ slot, (state.getStorage (Target.address selfAddress)
      (Target.storageKey slot)).toNat = X.storage slot) :
    Spec fork (At code message pc stack memory gas state substate returnData) (PostS X ss) :=
  Spec.consequence (stop hlt hbyte) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, hst, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout', hout]; decide +kernel, by rw [hss, hlogs],
        fun _ slot => by rw [hst]; exact hstore slot⟩)

/-- RETURN shows §X§ when §X§ succeeds with the bytes it reads, the logs are §ss§'s and the
storage is §X§'s. -/
theorem return_postS {X : Observable} {ss : Substate} {code : ByteArray} {message : Message fork}
    {pc : Nat} {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = true)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output)
    (hlogs : substate.logs = ss.logs)
    (hstore : ∀ slot, (state.getStorage (Target.address selfAddress)
      (Target.storageKey slot)).toNat = X.storage slot) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (PostS X ss) :=
  Spec.consequence (Logic.«return» hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, hst, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, by rw [hss, hlogs],
        fun _ slot => by rw [hst]; exact hstore slot⟩)

/-- REVERT shows §X§ when §X§ fails with the bytes it reads and the logs are §ss§'s. -/
theorem revert_postS {X : Observable} {ss : Substate} {code : ByteArray} {message : Message fork}
    {pc : Nat} {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hfork : .byzantium ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = false)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output)
    (hlogs : substate.logs = ss.logs) :
    Spec fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (PostS X ss) :=
  Spec.consequence (revert hfork hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, _, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, by rw [hss, hlogs],
        fun h => by rw [hs] at h; cases h⟩)

theorem hashMap_getElem?_of_isEmpty {m : Std.HashMap Nat Nat} (h : m.isEmpty = true) (k : Nat) :
    m[k]? = none :=
  Std.HashMap.getElem?_eq_none (Std.HashMap.isEmpty_iff_forall_not_mem.mp h _)

/-! ## Storage before the call

The callee's storage before a call is the call's (`getStorage_preState`), and
`run_of_post_at` is `run_of_post` from it. -/


/-- Two slots have the same storage key exactly when they agree modulo 2^256. -/
theorem storageKey_eq_iff (a b : Nat) :
    Target.storageKey a = Target.storageKey b ↔ a % 2 ^ 256 = b % 2 ^ 256 := by
  constructor
  · intro h
    have := congrArg (fun v : Bytes32 => bytesToNat v.toList) h
    simpa [SolidCore.Refinement.toList_storageKey, bytesToNat_natToBytes] using this
  · intro h
    rw [SolidCore.Refinement.storageKey_mod a, SolidCore.Refinement.storageKey_mod b]
    simp only [SolidCore.Refinement.wordSize, h]

/-- A key of a storage tree after the entries `σ` are written over it reads as `slotValue`'s
fold of `σ` from the tree's own word. -/
theorem getD_foldl_insert (σ : List (Nat × Nat)) (m : Std.ExtTreeMap Bytes32 EthLib.Base.U256)
    (k b : Nat) (h : BitVec.toNat (m[Target.storageKey k]?.getD (0 : EthLib.Base.U256)) = b) :
    ((σ.foldl (fun m kv => m.insert (Target.storageKey kv.1) (BitVec.ofNat 256 kv.2)) m)[
        Target.storageKey k]?.getD (0 : EthLib.Base.U256)).toNat =
      σ.foldl (fun acc kv => if kv.1 % 2 ^ 256 = k % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) b := by
  induction σ generalizing m b with
  | nil => simpa using h
  | cons kv σ ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Std.ExtTreeMap.getElem?_insert]
    by_cases hk : kv.1 % 2 ^ 256 = k % 2 ^ 256
    · have : compare (Target.storageKey kv.1) (Target.storageKey k) = .eq := by
        rw [Std.compare_eq_iff_eq (α := Bytes32)]; exact (storageKey_eq_iff _ _).2 hk
      simp only [hk, ↓reduceIte]; simp [this]
    · have : compare (Target.storageKey kv.1) (Target.storageKey k) ≠ .eq := by
        rw [ne_eq, Std.compare_eq_iff_eq (α := Bytes32)]
        exact fun e => hk ((storageKey_eq_iff _ _).1 e)
      simp only [hk, ↓reduceIte]; simpa [this] using h

/-- A slot of a call's storage is a word. -/
theorem slotValue_lt (σ : List (Nat × Nat)) (k : Nat) : slotValue σ k < 2 ^ 256 := by
  unfold slotValue
  suffices h : ∀ b < 2 ^ 256, σ.foldl
      (fun acc kv => if kv.1 % 2 ^ 256 = k % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) b < 2 ^ 256 from
    h 0 (by decide)
  induction σ with
  | nil => exact fun b hb => hb
  | cons kv σ ih =>
    intro b hb
    simp only [List.foldl_cons]
    apply ih
    split
    · exact Nat.mod_lt _ (by decide)
    · exact hb

/-- A slot of a call's storage depends on the slot modulo 2^256 only. -/
theorem slotValue_mod (σ : List (Nat × Nat)) (k : Nat) : slotValue σ (k % 2 ^ 256) = slotValue σ k := by
  simp only [slotValue, Nat.mod_mod]

/-- A slot of a call's storage read at the slot modulo 2^256, as a word, is the slot's. -/
theorem slotValue_mod_mod (σ : List (Nat × Nat)) (k : Nat) :
    slotValue σ (k % 2 ^ 256) % 2 ^ 256 = slotValue σ k := by
  rw [slotValue_mod, Nat.mod_eq_of_lt (slotValue_lt σ k)]

/-- A slot of the callee's storage before the call is the call's: `slotValue` of its storage. -/
theorem getStorage_preState (code : ByteArray) (c : Call) (k : Nat) :
    ((Target.preState code c).getStorage (Target.address selfAddress) (Target.storageKey k)).toNat =
      slotValue c.storage k := by
  simp only [Target.preState, TransactionState.getStorage, TransactionState.ofBlock,
    StorageMap.slot, State.getStorage]
  simp
  exact getD_foldl_insert _ _ _ _ (by simp)

/-- `run_of_post` from any storage `σ`: the frame of every message with no value and call data
`cdOf (selectorOf s) ws` stops as `X` shows from every state, so `Target.run` of the call with
argument words `ws`, no value and storage `σ` is `X`, when `X` shows no logs and keeps `σ`. -/
theorem run_of_post_at (code : ByteArray) (s : Nat) (ws : List U256) (σ : List (Nat × Nat))
    (X : Observable) (hlogs : X.logs = []) (hstore : ∀ slot, X.storage slot = slotValue σ slot)
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      ∀ st ss, Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) (Post X st ss)) :
    Target.run code
      { calldata := Abi.calldata s (ws.map BitVec.toNat), callvalue := 0, storage := σ } =
        some X := by
  have hd : Abi.calldata s (ws.map BitVec.toNat) = cdOf (selectorOf s) ws := by
    rw [calldata_eq_cdOf s _ (by simpa using fun a _ => a.isLt)]
    simp [List.map_map, Function.comp_def]
  let c : Call := { calldata := Abi.calldata s (ws.map BitVec.toNat), callvalue := 0, storage := σ }
  obtain ⟨evm, hr, herr, hout, hsub, hst⟩ := processMessage_post (Target.message code c) rfl rfl
    (precompileAddress_message code c) X
    (fun st ss => h _ rfl (by simp [Target.message, c, hd]) st ss) (Target.preState code c)
    Substate.empty
  show Target.run code c = some X
  simp only [Target.run, hr]
  have hsucc : evm.1.error.isNone = X.success := by
    rw [herr]; cases hX : X.success <;> simp [errorOf, hX]
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc hout hlogs hstore hst ⊢
    subst hlogs
    rw [Observable.mk.injEq]
    refine ⟨hsucc, hout, by simp [hsub, Substate.empty], ?_⟩
    funext slot
    rw [hstore slot, hsucc]
    cases hs : success
    · simp [c]
    · simp only [ite_true]
      rw [hst hs, getStorage_preState code c slot]

/-! ## Calls from a given storage

A contract whose constructor leaves storage is called from it: `callAt sel ws σ` is the call of
selector `sel` on the argument words `ws` from the storage `σ`. Its frame starts from
`Target.preState`, whose storage holds the words of `σ` (`getStorage_preState`), so SLOAD reads
them (`sload_then`), and a failing call keeps them (`run_of_postS_at`). -/

/-- The call of selector `sel` on the argument words `ws` from the storage `σ`, with no value. -/
def callAt (sel : Nat) (ws : List U256) (σ : List (Nat × Nat)) : Call :=
  { calldata := Abi.calldata sel (ws.map BitVec.toNat), callvalue := 0, storage := σ }

theorem storage_callAt (sel : Nat) (ws : List U256) (σ : List (Nat × Nat)) :
    (callAt sel ws σ).storage = σ := rfl

/-- A slot of the callee's storage before the call holds the call's word for it, as a word. -/
theorem getStorage_preState_ofNat (code : ByteArray) (c : Call) (k : Nat) :
    (Target.preState code c).getStorage (Target.address selfAddress) (Target.storageKey k) =
      BitVec.ofNat 256 (slotValue c.storage k) := by
  apply BitVec.eq_of_toNat_eq
  rw [getStorage_preState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt _ _)]

/-- `getStorage_preState` at the key SLOAD reads for a word. -/
theorem getStorage_preState_toBeBytes (code : ByteArray) (c : Call) (key : U256) :
    (Target.preState code c).getStorage (Target.address selfAddress) (U256.toBeBytes key) =
      BitVec.ofNat 256 (slotValue c.storage key.toNat) := by
  rw [← (storageKey_eq_toBeBytes key.toNat key).mpr (Nat.mod_eq_of_lt key.isLt)]
  exact getStorage_preState_ofNat code c key.toNat

/-- Recording a read keeps the storage. -/
theorem getStorage_recordStorageRead (tx : TransactionState) (a : Address) (k : Bytes32)
    (a' : Address) (k' : Bytes32) :
    (tx.recordStorageRead a k).getStorage a' k' = tx.getStorage a' k' := rfl

theorem getD_getElem? (m : StorageMap) (a : Address) (k : Bytes32) :
    (m.getD a ∅)[k]? = m.slot a k := by
  simp only [StorageMap.slot, Std.ExtTreeMap.getD_eq_getD_getElem?]
  cases m[a]? <;> simp

theorem slot_writeOf (tx : TransactionState) (a : Address) (k : Bytes32) (v : U256)
    (a' : Address) (k' : Bytes32) :
    (writeOf tx a k v).storageWrites.slot a' k' =
      if a' = a ∧ k' = k then some v else tx.storageWrites.slot a' k' := by
  by_cases ha : a' = a
  · subst ha
    by_cases hk : k' = k
    · subst hk
      simp [writeOf, TransactionState.recordAccountRead, StorageMap.slot]
    · simp only [writeOf, TransactionState.recordAccountRead, StorageMap.slot,
        Std.ExtTreeMap.getElem?_insert_self, Option.bind_some, Std.ExtTreeMap.getElem?_insert]
      have hc : compare k k' ≠ .eq := fun h => hk (Std.LawfulEqCmp.eq_of_compare h).symm
      simp only [hc, true_and, hk, ↓reduceIte]
      exact getD_getElem? _ _ _
  · simp only [writeOf, TransactionState.recordAccountRead, StorageMap.slot,
      Std.ExtTreeMap.getElem?_insert]
    simp [show (a = a') = False from eq_false (fun h => ha h.symm), ha]

/-- The storage after a write to any state: the written word at its key, the state's elsewhere. -/
theorem getStorage_writeOf_of (tx : TransactionState) (a : Address) (k : Bytes32) (v : U256)
    (a' : Address) (k' : Bytes32) :
    (writeOf tx a k v).getStorage a' k' = if a' = a ∧ k' = k then v else tx.getStorage a' k' := by
  unfold TransactionState.getStorage
  rw [slot_writeOf]
  by_cases h : a' = a ∧ k' = k
  · simp only [h, and_self, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    rfl

/-- The frame of every message of the call from the storage `σ`, from the call's state before
it, stops as `PostS X` says: `Target.run` of the call is `X`, when `X` shows no logs and keeps
the words of `σ` when it fails. -/
theorem run_of_postS_at (code : ByteArray) (s : Nat) (ws : List U256) (σ : List (Nat × Nat))
    (X : Observable) (hlogs : X.logs = [])
    (hfail : X.success = false → ∀ slot, X.storage slot = slotValue σ slot)
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = cdOf (selectorOf s) ws →
      msg.isStatic = false → msg.currentTarget = Target.address selfAddress →
      Spec .fusaka (At code msg 0 [] .empty 10000000 (Target.preState code (callAt s ws σ))
        Substate.empty .empty) (PostS X Substate.empty)) :
    Target.run code (callAt s ws σ) = some X := by
  have hd : Abi.calldata s (ws.map BitVec.toNat) = cdOf (selectorOf s) ws := by
    rw [calldata_eq_cdOf s _ (by simpa using fun a _ => a.isLt)]
    simp [List.map_map, Function.comp_def]
  let c := callAt s ws σ
  obtain ⟨evm, hr, herr, hout, hst⟩ := processMessage_postS (Target.message code c) rfl rfl
    (precompileAddress_message code c) X (Target.preState code c) Substate.empty
    (h _ rfl (by simp [Target.message, c, callAt, hd]) rfl rfl)
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
      · simp [c, callAt, hfail hs slot]
      · simp only [ite_true]
        exact (hst hs).2 slot

/-- SLOAD of a slot of the callee, as a step of a specification: it reads the word of the state,
at a price of at most a cold access. -/
theorem sload_then {Q : Evm fork Nat → Prop} {code : ByteArray} {message : Message fork}
    {pc : Nat} {key : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : TransactionState} {substate : Substate} {returnData : ByteArray}
    (hfork : .berlin ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (htgt : message.currentTarget = Target.address selfAddress) (hgas : 2100 ≤ gas)
    (h : ∀ g, g ≤ 2100 → Spec fork (At code message (pc + 1)
        (state.getStorage (Target.address selfAddress) (U256.toBeBytes key) :: rest) memory
        (gas - g) (state.recordStorageRead message.currentTarget (U256.toBeBytes key))
        { substate with
          accessedStorageKeys := (substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))) } returnData) Q) :
    Spec fork (At code message pc (key :: rest) memory gas state substate returnData) Q :=
  Spec.seq (sload hfork hlt hbyte rfl (by split <;> omega))
    (Spec.reshape (by rw [htgt]) rfl rfl (h _ (by split <;> omega)))

/-- SSTORE at Fusaka, as a step of a specification: it writes the word, at a price of at most a
cold access and a new slot (`sstoreCost_le`), which the rest of the path may spend. -/
theorem sstore_then {Q : Evm .fusaka Nat → Prop} {code : ByteArray} {message : Message .fusaka}
    {pc : Nat} {key new : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state state' : TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hgas : 22100 ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state')
    (h : ∀ g, g ≤ 22100 → Spec .fusaka (At code message (pc + 1) rest memory (gas - g) state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund .fusaka
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) Q) :
    Spec .fusaka (At code message pc (key :: new :: rest) memory gas state substate returnData)
      Q :=
  Spec.seq (sstore (by decide) (by decide) hlt hbyte hstatic rfl
      (by simp only [CALL_STIPEND]; omega) (Nat.le_trans (sstoreCost_le _ _ _ _) hgas) hset)
    (h _ (sstoreCost_le _ _ _ _))

/-- A statement about every word below `N` follows from it on the words of every number below
`N`, which the kernel can evaluate one by one. -/
theorem forall_of_lt_ofNat {N : Nat} {P : U256 → Prop}
    (h : ∀ n, n < N → P (BitVec.ofNat 256 n)) : ∀ w : U256, w.toNat < N → P w := fun w hw => by
  simpa using h w.toNat hw

/-! ## The tactic -/

open Lean.Parser.Tactic

/-- Proves that a slot of the storage after the write is SolidCore's: both are the written
word on the slot of its key and zero elsewhere. -/
syntax "wide_store" : tactic

macro_rules
  | `(tactic| wide_store) => `(tactic| (
      simp [*, Source.observe, SolidCore.Solidity.Source.State.loadSlot,
        SolidCore.Solidity.Source.StorageMap.lookup?, Std.HashMap.getElem?_insert,
        hashMap_getElem?_of_isEmpty, storageKey_eq_toBeBytes, SolidCore.Solidity.Shared.norm,
        SolidCore.Solidity.Shared.wordModulus, EvmYul.UInt256.size]
      try ((repeat' split) <;> simp_all <;> omega)))

/-- Proves that a slot of the callee's storage at a stop is SolidCore's, after one write or
none. -/
syntax "wide_slot" ident : tactic

macro_rules
  | `(tactic| wide_slot $htgt) => `(tactic| first
      | (rw [$htgt:ident, getStorage_writeOf _ _ rfl]; wide_store)
      | (rw [getStorage_preState_nil _ _ rfl]; wide_store))

/-- Steps one opcode of a path of a function that writes storage: SSTORE to the callee's account,
which exists, STOP against the observable of `PostS`, and every other opcode as `wide_one`. -/
syntax "wide_one_s" " [" simpLemma,* "]" " [" simpLemma,* "]" ident ident ident : tactic

macro_rules
  | `(tactic| wide_one_s [$ls,*] [$ns,*] $hf $hstat $htgt) => `(tactic| ((try unfold Spec) <;> first
      | (refine' Triple.seq (sstore (by decide) (by decide) ?lt ?op $hstat rfl ?stip ?gas
          (setStorage_ok _ _ ?acc)) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case stip => simp only [CALL_STIPEND]; omega
         case gas => exact Nat.le_trans (sstoreCost_le _ _ _ _) (by omega)
         case acc => rw [$htgt:ident]; exact account_preState _ _) <;> evm_tidy
      | (refine stop_postS ?lt ?op ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case succ => simp [Source.observe]
         case out => simp [Source.observe]
         case store => intro slot; wide_slot $htgt)
      | (refine return_postS ?lt ?op ?gas ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out
         case store => intro slot; wide_slot $htgt)
      | (refine revert_postS (by decide) ?lt ?op ?gas ?succ ?out rfl
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out)
      | wide_one [$ls,*] [$ns,*] $hf))

/-- Proves the frame hypothesis of `run_of_postS` on one path of the source, for a function
that writes storage. `ls` are the rules of the code, as for `wide_tgt`. -/
syntax "wide_tgt_s" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| wide_tgt_s [$ls,*]) => `(tactic| (
      intro msg hv hd hstat htgt
      have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
      try simp only [$ls,*] at hd
      repeat wide_one_s [$ls,*] [hd, hv] hfork hstat htgt))

open Lean Meta Elab Tactic in
/-- Closes a goal about one word that a hypothesis `w.toNat < N` bounds by `N ≤ 2 ^ 8`, such as
a path condition on a `uint8` argument, by evaluating it on every word below `N` in the kernel
(`forall_of_lt_ofNat` and `decide +kernel`). It fails when the goal mentions another local. -/
elab "word_decide" : tactic => withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let_expr LT.lt _ _ lhs rhs := ty | continue
    let_expr BitVec.toNat _ w := lhs | continue
    unless w.isFVar do continue
    let some n ← (Meta.evalNat rhs).run | continue
    unless n ≤ 256 do continue
    let g ← instantiateMVars (← goal.getType)
    unless g.containsFVar w.fvarId! do continue
    let motive ← mkLambdaFVars #[w] g
    -- The goal `∀ n, n < N → motive (BitVec.ofNat 256 n)`, which the kernel decides.
    let hty ← withLocalDeclD `n (mkConst `Nat) fun k => do
      let lt ← mkAppM `LT.lt #[k, rhs]
      let body := (mkApp motive (← mkAppM `BitVec.ofNat #[mkNatLit 256, k])).headBeta
      mkForallFVars #[k] (← mkArrow lt body)
    let hm ← mkFreshExprSyntheticOpaqueMVar hty
    let [] ← Term.TermElabM.run' <|
        Tactic.run hm.mvarId! (evalTactic (← `(tactic| decide +kernel)))
      | throwError "word_decide: the kernel check left goals"
    goal.assign (← mkAppOptM `SolidCore.Refinement.Evm.Wide.forall_of_lt_ofNat
      #[rhs, motive, hm, w, decl.toExpr])
    replaceMainGoal []
    return
  throwError "word_decide: no word with a small bound that the goal mentions"

/-- Proves that a slot of the callee's storage at a stop is SolidCore's, for a call from a given
storage (`callAt`): the target's word is the last write's at its key and the call's word
elsewhere (`getStorage_writeOf_of`, `getStorage_preState_ofNat`). After a split on the slot, the
words left to compare go to `word_decide`. -/
syntax "wide_slot_at" ident : tactic

macro_rules
  | `(tactic| wide_slot_at $htgt) => `(tactic| (
      simp only [$htgt:ident, getStorage_writeOf_of, getStorage_recordStorageRead,
        getStorage_preState_ofNat, storage_callAt]
      simp [*, Source.observe, SolidCore.Solidity.Source.State.loadSlot,
        SolidCore.Solidity.Source.StorageMap.lookup?, Std.HashMap.getElem?_insert,
        storageKey_eq_toBeBytes, slotValue, SolidCore.Solidity.Shared.norm,
        SolidCore.Solidity.Shared.wordModulus, EvmYul.UInt256.size]
      all_goals (split <;> (try simp_all) <;> (try split) <;> (try simp_all) <;> (try omega) <;>
        word_decide)))

/-- Proves that the output a RETURN or REVERT reads is the observable's: `wide_out`, and else
`word_decide` on the output words. -/
syntax "wide_out_at" : tactic

macro_rules
  | `(tactic| wide_out_at) => `(tactic| first
      | wide_out
      | ((try wide_mem) <;> simp only [toList_wordBytes, Source.observe] <;> word_decide))

/-- Steps one opcode of a path of a call from a given storage: SLOAD reads the call's word
(`sload_then`, `getStorage_preState_toBeBytes`), SSTORE writes (`sstore_then`), STOP, RETURN
and REVERT close the path against the observable of `PostS`, and every other opcode is
`wide_one`'s. -/
syntax "wide_one_at" " [" simpLemma,* "]" " [" simpLemma,* "]" ident ident ident : tactic

macro_rules
  | `(tactic| wide_one_at [$ls,*] [$ns,*] $hf $hstat $htgt) => `(tactic| ((try unfold Spec) <;> first
      | ((refine sload_then (by decide) ?lt ?op $htgt ?gas (fun _ _ => ?next)
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => omega) <;>
          simp only [getStorage_recordStorageRead, getStorage_preState_toBeBytes, storage_callAt,
            slotValue, List.foldl_cons, List.foldl_nil, BitVec.reduceToNat, Nat.reduceMod,
            Nat.reducePow, ↓reduceIte, Nat.reduceEqDiff, BitVec.reduceOfNat] <;> evm_tidy)
      | ((refine sstore_then ?lt ?op $hstat ?gas (setStorage_ok _ _ ?acc) (fun _ _ => ?next)
          case lt => evm_code [$ls,*]
          case op => evm_code [$ls,*]
          case gas => omega
          case acc => rw [$htgt:ident]; exact account_preState _ _) <;> evm_tidy)
      | (refine stop_postS ?lt ?op ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case succ => simp [Source.observe]
         case out => simp [Source.observe]
         case store => intro slot; wide_slot_at $htgt)
      | (refine return_postS ?lt ?op ?gas ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out_at
         case store => intro slot; wide_slot_at $htgt)
      | (refine revert_postS (by decide) ?lt ?op ?gas ?succ ?out rfl
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case gas => (try wide_mem) <;> first | decide | omega | decide +kernel
         case succ => first | rfl | simp [Source.observe]
         case out => wide_out_at)
      | wide_one [$ls,*] [$ns,*] $hf))

/-- Proves the frame hypothesis of `run_of_postS_at` on one path of the source, for a call from
a given storage. `ls` are the rules of the code, as for `wide_tgt`. -/
syntax "wide_tgt_at" " [" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| wide_tgt_at [$ls,*]) => `(tactic| (
      intro msg hv hd hstat htgt
      have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
      try simp only [$ls,*] at hd
      repeat wide_one_at [$ls,*] [hd, hv] hfork hstat htgt))

end SolidCore.Refinement.Evm.Wide

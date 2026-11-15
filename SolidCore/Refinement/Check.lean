import SolidCore.Refinement.Statement
import EthLib.Base.Proofs.BigEndian

/-!
# Checking a refinement on a finite set of calls

`Refines` is a statement about functions: the callee's final storage is a map from
every slot to a word, so it cannot be compared by evaluation. This module turns it
into one that can.

`agree fuel contract code call` runs both semantics on `call` and compares the
success flag, the output, the logs, and the final storage on a finite list of slots:
every slot either side holds a word for, and every slot of the call's initial
storage. `agree_sound` shows that both sides keep every other slot at zero, and that
both read a slot modulo `2 ^ 256`, so agreement on that list is agreement on every
slot. `refines_of_all` lifts it to `Refines` for a list of calls, which a proof
about a contract then checks with `native_decide`.
-/

namespace SolidCore.Refinement

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State
open SolidCore.Solidity

/-! ## Storage functions that agree on finitely many slots -/

/-- The words a slot is read as on both sides. -/
abbrev wordSize : Nat := 2 ^ 256

/-- Two storage functions that read slots modulo `2 ^ 256`, are zero off `keys` and
agree on `keys` are equal. -/
theorem storage_ext {f g : Nat → Nat} (keys : List Nat)
    (fp : ∀ s, f s = f (s % wordSize)) (gp : ∀ s, g s = g (s % wordSize))
    (fz : ∀ s, s % wordSize ∉ keys → f s = 0) (gz : ∀ s, s % wordSize ∉ keys → g s = 0)
    (agree : ∀ k ∈ keys, f k = g k) : f = g := by
  funext s
  by_cases hk : s % wordSize ∈ keys
  · rw [fp, gp]; exact agree _ hk
  · rw [fz s hk, gz s hk]

/-! ## SolidCore's storage -/

/-- The slots SolidCore's storage map holds a word for. -/
def sourceKeys (st : Source.State) : List Nat := st.storage.keys

theorem norm_mod (s : Nat) : Shared.norm (s % wordSize) = Shared.norm s := by
  simp [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, wordSize]

theorem loadSlot_mod (st : Source.State) (s : Nat) :
    st.loadSlot s = st.loadSlot (s % wordSize) := by
  simp only [Source.State.loadSlot, Source.StorageMap.lookup?, norm_mod]

theorem loadSlot_of_not_mem (st : Source.State) (s : Nat) (h : s % wordSize ∉ sourceKeys st) :
    st.loadSlot s = 0 := by
  have hn : Shared.norm s = s % wordSize := by
    simp [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size, wordSize]
  unfold Source.State.loadSlot Source.StorageMap.lookup?
  rw [hn, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_none]
  intro hm
  exact h (Std.HashMap.mem_keys.mpr hm)

/-! ## The initial storage of a call -/

/-- The slots the call's initial storage names. -/
def callKeys (call : Call) : List Nat := call.storage.map (·.1 % wordSize)

theorem slotValue_mod (storage : List (Nat × Nat)) (s : Nat) :
    slotValue storage s = slotValue storage (s % wordSize) := by
  simp [slotValue, wordSize]

theorem slotValue_of_not_mem (call : Call) (s : Nat) (h : s % wordSize ∉ callKeys call) :
    slotValue call.storage s = 0 := by
  unfold slotValue
  unfold callKeys at h
  generalize call.storage = l at h
  suffices ∀ acc, acc = 0 → List.foldl (fun acc kv =>
      if kv.1 % 2 ^ 256 = s % 2 ^ 256 then kv.2 % 2 ^ 256 else acc) acc l = 0 from this 0 rfl
  induction l with
  | nil => intro acc h; simpa using h
  | cons kv l ih =>
    intro acc hacc
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    apply ih h.2
    have hne : ¬ kv.1 % 2 ^ 256 = s % 2 ^ 256 := fun e => h.1 (by simpa [wordSize] using e.symm)
    simp only [hne, ite_false, hacc]

/-! ## EthLib's storage -/

/-- The slots one storage map holds a word for at an address, as numbers. -/
def mapKeys (m : StorageMap) (a : Address) : List Nat :=
  match m[a]? with
  | some slots => slots.keys.map fun k => bytesToNat k.toList
  | none => []

/-- The slots any layer of a transaction's state holds a word for at an address. -/
def targetKeys (tx : TransactionState) (a : Address) : List Nat :=
  mapKeys tx.storageWrites a ++ mapKeys tx.parent.storageWrites a ++
    mapKeys tx.parent.preState.storage a

theorem toList_storageKey (s : Nat) : (Target.storageKey s).toList = natToBytes 32 s := by
  simp [Target.storageKey, Vector.toList]

theorem storageKey_mod (s : Nat) : Target.storageKey s = Target.storageKey (s % wordSize) := by
  apply Vector.toList_inj.mp
  rw [toList_storageKey, toList_storageKey]
  have h := natToBytes_bytesToNat (natToBytes 32 s)
  have h' := natToBytes_bytesToNat (natToBytes 32 (s % wordSize))
  rw [natToBytes_length, bytesToNat_natToBytes] at h h'
  rw [← h, ← h', show (256 : Nat) ^ 32 = wordSize by decide, Nat.mod_mod]

theorem slot_of_not_mem (m : StorageMap) (a : Address) (s : Nat)
    (h : s % wordSize ∉ mapKeys m a) : m.slot a (Target.storageKey s) = none := by
  unfold StorageMap.slot
  unfold mapKeys at h
  cases hm : m[a]? with
  | none => rfl
  | some slots =>
    rw [hm] at h
    simp only [Option.bind_some]
    rw [Std.ExtTreeMap.getElem?_eq_none]
    intro hk
    apply h
    refine List.mem_map.mpr ⟨_, Std.ExtTreeMap.mem_keys.mpr hk, ?_⟩
    rw [toList_storageKey, bytesToNat_natToBytes]
    rfl

theorem getStorage_of_not_mem (tx : TransactionState) (a : Address) (s : Nat)
    (h : s % wordSize ∉ targetKeys tx a) : tx.getStorage a (Target.storageKey s) = 0 := by
  simp only [targetKeys, List.mem_append, not_or] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold TransactionState.getStorage State.getStorage
  rw [slot_of_not_mem _ _ _ h1, slot_of_not_mem _ _ _ h2, slot_of_not_mem _ _ _ h3]
  simp

/-! ## The check -/

/-- The final storage of a successful call, slot by slot, as `Target.run` reads it. -/
def targetSlot (tx : TransactionState) (s : Nat) : Nat :=
  (tx.getStorage (Target.address selfAddress) (Target.storageKey s)).toNat

/-- Whether SolidCore with `fuel` and EthLib both finish `call` and show the same
success flag, output and logs, and the same final storage on every slot either side
or the call names. -/
def agree (fuel : Nat) (contract : TypeCheck.CheckedContract) (code : ByteArray)
    (call : Call) : Bool :=
  match Source.result? fuel contract call,
      processMessage (Meter := Nat) .fusaka (Target.message code call)
        (Target.preState code call) Substate.empty, Target.run code call with
  | some r, .ok ⟨evm, _⟩, some tgt =>
    let src := Source.observe call r
    src.success == tgt.success && src.output == tgt.output && src.logs == tgt.logs &&
      (sourceKeys r.state ++ targetKeys evm.state (Target.address selfAddress) ++
        callKeys call).all fun k => src.storage k == tgt.storage k
  | _, _, _ => false

theorem agree_sound {fuel : Nat} {contract : TypeCheck.CheckedContract} {code : ByteArray}
    {call : Call} (h : agree fuel contract code call = true) :
    ∃ obs, Source.run fuel contract call = some obs ∧ Target.run code call = some obs := by
  unfold agree at h
  split at h
  next r evm sub tgt hr hpm htgt =>
    have hsrc : Source.run fuel contract call = some (Source.observe call r) := by
      simp [Source.run, hr]
    refine ⟨_, hsrc, ?_⟩
    rw [htgt]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨hs, ho⟩, hl⟩, hk⟩ := h
    have htgt' := htgt
    simp only [Target.run, hpm, Option.some.injEq] at htgt'
    subst htgt'
    congr 1
    symm
    simp only [Source.observe] at hs ho hl hk ⊢
    rw [Observable.mk.injEq]
    refine ⟨hs, ho, hl, ?_⟩
    rw [hs] at hk ⊢
    cases hsucc : evm.error.isNone
    · rfl
    · simp only [hsucc, ite_true] at hk ⊢
      apply storage_ext (sourceKeys r.state ++ targetKeys evm.state (Target.address selfAddress) ++
          callKeys call) (fun s => by rw [loadSlot_mod])
        (fun s => by rw [storageKey_mod])
        (fun s hs' => loadSlot_of_not_mem _ _ (fun m => hs' (List.mem_append_left _
          (List.mem_append_left _ m))))
        (fun s hs' => by
          rw [getStorage_of_not_mem _ _ _ (fun m => hs' (List.mem_append_left _
            (List.mem_append_right _ m)))]
          rfl)
      intro k hk'
      exact hk k hk'
  next => exact absurd h (by simp)

/-- `code` refines `contract` on every call of a list that `agree` accepts. -/
theorem refines_of_all {fuel : Nat} {contract : TypeCheck.CheckedContract} {code : ByteArray}
    {calls : List Call} (h : calls.all (agree fuel contract code) = true) :
    Refines fuel contract code (· ∈ calls) := fun _ hc =>
  agree_sound (List.all_eq_true.mp h _ hc)

end SolidCore.Refinement

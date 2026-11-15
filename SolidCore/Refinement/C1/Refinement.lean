import SolidCore.Refinement.Statement
import SolidCore.Refinement.Source.C1
import SolidCore.Refinement.C1.Target

/-!
# c1: solar's bytecode refines SolidCore's `Main`

`refines` proves `Refines fuel contract code scope` for c1
(`scripts/refinement/corpus/c1.sol`), where `contract` is SolidCore's checked
`Main` and `code` is solar's runtime bytecode at the pinned commit. The scope is
every call of `f(uint8)` with any 32-byte argument word, no value and empty
storage: 2^256 calls, including the dirty words a `uint8` decoder must reject.

* The EthLib side, `target_run`, is a kernel-checked symbolic proof
  (`C1.processMessage_spec`).
* The SolidCore side, `source_run`, evaluates the interpreter with
  `native_decide` on the 256 clean words and on the dirty word 256, and shows
  that every dirty word decodes, and so runs, exactly as 256 does. It trusts
  Lean's compiler, as `native_decide` does.
-/

namespace SolidCore.Refinement.C1

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State
open SolidCore.Solidity

/-- The interpreter fuel the refinement uses. -/
def fuel : Nat := 4096

/-- SolidCore's checked `Main` of c1. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract Source.C1.importedSourceUnit "Main"

/-- The call of `f` with argument word `w`, no value and empty storage. -/
def call (w : U256) : Call := { calldata := cd w, callvalue := 0, storage := [] }

/-- The calls the theorem covers. -/
def scope (c : Call) : Prop := ∃ w, c = call w

/-- What both sides show for `f` on the word `w`: `spec w`, no logs, empty storage. -/
def expected (w : U256) : Observable :=
  { success := (spec w).1.isNone, output := (spec w).2.toList.map (·.toNat), logs := [],
    storage := fun _ => 0 }

/-! ## EthLib -/

theorem precompileAddress_message (c : Call) :
    precompileAddress .fusaka (Target.message code c) = none := by
  simp only [precompileAddress, Target.message]
  decide

theorem getStorage_preState (w : U256) (k : Nat) :
    (Target.preState code (call w)).getStorage (Target.address selfAddress)
      (Target.storageKey k) = 0 := by
  simp [Target.preState, call, TransactionState.getStorage, TransactionState.ofBlock,
    StorageMap.slot, State.getStorage]

/-- EthLib runs solar's bytecode on every call in scope as `expected` says. -/
theorem target_run (w : U256) : Target.run code (call w) = some (expected w) := by
  obtain ⟨evm, h, herr, hout, hsub, hst⟩ := processMessage_spec w (Target.message code (call w))
    rfl rfl rfl rfl (precompileAddress_message _) (Target.preState code (call w)) Substate.empty
  simp only [Target.run, h, hsub, herr, hout, expected]
  cases hs : (spec w).1 with
  | none =>
    have hstate := hst hs
    simp [hstate, getStorage_preState, Substate.empty]
  | some e =>
    simp [call, slotValue]

/-! ## SolidCore -/

/-- The call data of `call w`, byte by byte: the selector, then `w` big-endian. -/
theorem bytes_call (w : U256) :
    (call w).calldata.data.toList.map (·.toNat) =
      [0x31, 0x20, 0xd4, 0x34] ++ (natToBytes 32 w.toNat).map (·.toNat) := by
  simp [call, cd, sel, wordBytes]
  rw [← EthLib.Base.U256.toList_toBeBytes]
  rfl

/-- A 256-bit word is already a SolidCore word. -/
theorem norm_toNat (w : U256) : Shared.norm w.toNat = w.toNat := by
  simp only [Shared.norm, Shared.wordModulus]
  exact Nat.mod_eq_of_lt w.isLt

open SolidCore.Solidity.Source in
/-- SolidCore reads the 32 big-endian bytes of `w` back as `w`. -/
theorem bytesToWordBE_natToBytes (w : U256) :
    ABI.bytesToWordBE (ABI.normalizeBytes ((natToBytes 32 w.toNat).map (·.toNat))) = w.toNat := by
  have small : w.toNat < 256 ^ 32 := by
    have := w.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  have hnorm : Shared.norm w.toNat = w.toNat := norm_toNat w
  have hbyte : ∀ b : UInt8, normByte (Shared.External.byte b.toNat) = b.toNat := by
    intro b
    have := b.toNat_lt
    simp [normByte, Shared.Account.byte, Shared.External.byte, Nat.mod_eq_of_lt this]
  unfold ABI.bytesToWordBE ABI.normalizeBytes Shared.External.normalizeBytes
  rw [List.map_map, List.foldl_map]
  simp only [Function.comp_def, hbyte]
  change Shared.norm (bytesToNat (natToBytes 32 w.toNat)) = _
  rw [EthLib.Base.bytesToNat_natToBytes_of_lt small, hnorm]

open SolidCore.Solidity.Source in
/-- A `uint256` parameter cleaned as `uint8` rejects every word from 256 up. -/
theorem decode_dirty (fn : FunctionDef) (hp : fn.params.map BindingDecl.ty = [Source.Ty.uint256])
    (hc : fn.paramAbiCleanups = [AbiCleanup.uint 8]) (w : U256) (hw : 256 ≤ w.toNat) :
    ABI.decodeFunctionArgs? fn ((natToBytes 32 w.toNat).map (·.toNat)) = .error .empty := by
  unfold ABI.decodeFunctionArgs?
  simp only [hp, hc]
  simp [ABI.decodeArgsWith?, ABI.decodeArgsAux?, ABI.decodeValueAt?,
    ABI.decodeValueAtWithFuel?, ABI.readWord?, ABI.readBytes?, ABI.abiArgOpt,
    AbiCleanups.lazyParamValues, AbiCleanup.lazyParamValue, AbiCleanup.accepts, ABI.AbiCleanup.decodeLazy,
    natToBytes_length, ABI.Ty.listAbiHeadWords?, ABI.Ty.abiHeadWords?, ABI.Ty.abiDecodeFuel,
    ABI.Ty.isDynamicAbi, ABI.Ty.staticAbiHeadWords?, ABI.wordBytes, bind, Except.bind, pure,
    Except.pure]
  have hlt := norm_toNat w
  have htake : List.take 32 ((natToBytes 32 w.toNat).map (·.toNat)) =
      (natToBytes 32 w.toNat).map (·.toNat) :=
    List.take_of_length_le (by simp [natToBytes_length])
  simp [htake, bytesToWordBE_natToBytes, hlt, show ¬ w.toNat < 256 by omega]

open SolidCore.Solidity.Source in
/-- The ABI dispatcher sends every dirty word for `f` to the empty revert. -/
theorem dispatch_dirty (k : Contract) (fn : FunctionDef)
    (hsel : k.findFunctionBySelector? 0x3120d434 = some fn)
    (hp : fn.params.map BindingDecl.ty = [Source.Ty.uint256])
    (hc : fn.paramAbiCleanups = [AbiCleanup.uint 8])
    (w : U256) (hw : 256 ≤ w.toNat) {fuel : Nat} {base : Source.Context} {st : Source.State}
    {self sender value : Nat} :
    ABI.Contract.callCalldataAtFromWithContext? fuel k base st self sender value
        ([0x31, 0x20, 0xd4, 0x34] ++ (natToBytes 32 w.toNat).map (·.toNat)) =
      ABI.Contract.revertedCall? k st .empty := by
  have hsel' : ABI.readSelector? ([0x31, 0x20, 0xd4, 0x34] ++ (natToBytes 32 w.toNat).map (·.toNat)) =
      some 0x3120d434 := by
    simp [ABI.readSelector?, ABI.readBytes?, ABI.selectorBytes, natToBytes_length]
    decide
  unfold ABI.Contract.callCalldataAtFromWithContext?
  simp only [hsel', hsel, ABI.selectorBytes, List.drop_left' (show [0x31, 0x20, 0xd4, 0x34].length = 4 from rfl)]
  rw [decode_dirty fn hp hc w hw]

/-- Whether `Main` dispatches selector `0x3120d434` to a function with one `uint256`
ABI parameter cleaned as `uint8`. -/
def shapeOk : Bool :=
  match contract? with
  | .ok c =>
    match c.core.findFunctionBySelector? 0x3120d434 with
    | some fn =>
      match fn.params.map Source.BindingDecl.ty, fn.paramAbiCleanups with
      | [Source.Ty.uint256], [Source.AbiCleanup.uint 8] => true
      | _, _ => false
    | none => false
  | .error _ => false

theorem shapeOk_eq_true : shapeOk = true := by native_decide

/-- `Main` dispatches `f(uint8)` to a function whose one parameter is a `uint256`
cleaned as `uint8`. -/
theorem shape {c : TypeCheck.CheckedContract} (h : contract? = .ok c) :
    ∃ fn, c.core.findFunctionBySelector? 0x3120d434 = some fn ∧
      fn.params.map Source.BindingDecl.ty = [Source.Ty.uint256] ∧
      fn.paramAbiCleanups = [Source.AbiCleanup.uint 8] := by
  have hs := shapeOk_eq_true
  simp only [shapeOk, h] at hs
  split at hs
  next fn hf =>
    split at hs
    next hp hc => exact ⟨fn, hf, hp, hc⟩
    next => exact absurd hs (by simp)
  next => exact absurd hs (by simp)

/-- SolidCore runs every dirty word exactly as it runs 256. -/
theorem result_dirty {c : TypeCheck.CheckedContract} (h : contract? = .ok c) (w : U256)
    (hw : 256 ≤ w.toNat) :
    Source.result? fuel c (call w) = Source.result? fuel c (call (BitVec.ofNat 256 256)) := by
  obtain ⟨fn, hsel, hp, hc⟩ := shape h
  have h256 : 256 ≤ (BitVec.ofNat 256 256 : U256).toNat := by decide
  simp only [Source.result?, TypeCheck.CheckedContract.callCalldataAtFromWithContext?, bytes_call,
    dispatch_dirty c.core fn hsel hp hc w hw, dispatch_dirty c.core fn hsel hp hc _ h256]
  rfl

/-- Whether SolidCore's result for `call w` is `expected w`, read as data: the
success flag, the output, no logs and an empty storage map. -/
def sourceAgrees (w : U256) : Bool :=
  match contract? with
  | .ok contract =>
    match Source.result? fuel contract (call w) with
    | some result =>
      result.success == (spec w).1.isNone &&
        result.output == (spec w).2.toList.map (·.toNat) &&
        (result.state.logEntries selfAddress).isEmpty &&
        result.state.storage.isEmpty
    | none => false
  | .error _ => false

/-- SolidCore agrees on every clean argument word. -/
theorem sourceAgrees_clean : ∀ v : Fin 256, sourceAgrees (BitVec.ofNat 256 v.val) = true := by
  native_decide

/-- SolidCore agrees on the dirty word 256. -/
theorem sourceAgrees_256 : sourceAgrees (BitVec.ofNat 256 256) = true := by
  native_decide

/-- SolidCore agrees on every argument word. -/
theorem sourceAgrees_all (w : U256) : sourceAgrees w = true := by
  by_cases hw : w.toNat < 256
  · have := sourceAgrees_clean ⟨w.toNat, hw⟩
    simpa using this
  · have h256 := sourceAgrees_256
    have hspec : spec w = spec (BitVec.ofNat 256 256) := by
      rw [spec_dirty (by omega), spec_dirty (by decide)]
    unfold sourceAgrees at h256 ⊢
    split
    next c hc =>
      rw [hc] at h256
      simp only at h256
      rw [result_dirty hc w (by omega), hspec]
      exact h256
    next => rw [‹contract? = _›] at h256; exact h256

open SolidCore.Solidity.Source in
/-- An empty storage map reads 0 everywhere. -/
theorem loadSlot_of_isEmpty {st : Source.State} (h : st.storage.isEmpty = true) (slot : Nat) :
    st.loadSlot slot = 0 := by
  unfold State.loadSlot StorageMap.lookup?
  rw [Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_eq_none (Std.HashMap.isEmpty_iff_forall_not_mem.mp h _)]

/-- SolidCore runs every call in scope as `expected` says. -/
theorem source_run {c : TypeCheck.CheckedContract} (h : contract? = .ok c) (w : U256) :
    Source.run fuel c (call w) = some (expected w) := by
  have ha := sourceAgrees_all w
  simp only [sourceAgrees, h] at ha
  split at ha
  next r hr =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ha
    obtain ⟨⟨⟨hs, ho⟩, hl⟩, hst⟩ := ha
    simp only [Source.run, hr, Option.map_some, Source.observe, expected, hs, ho, hl]
    have hstore : (fun slot => if (spec w).1.isNone = true then r.state.loadSlot slot
        else slotValue (call w).storage slot) = fun _ => 0 := by
      funext slot
      split
      · exact loadSlot_of_isEmpty hst slot
      · simp [call, slotValue]
    rw [hstore]
    simp
  next => exact absurd ha (by simp)

/-! ## The refinement -/

/-- solar's runtime bytecode for c1 refines SolidCore's `Main` on every call of
`f(uint8)` with any argument word, no value and empty storage. -/
theorem refines : ∃ contract, contract? = .ok contract ∧ Refines fuel contract code scope := by
  match h : contract? with
  | .ok contract =>
    exact ⟨contract, rfl, fun _ ⟨w, hw⟩ => hw ▸ ⟨expected w, source_run h w, target_run w⟩⟩
  | .error _ =>
    have hs := shapeOk_eq_true
    simp [shapeOk, h] at hs

end SolidCore.Refinement.C1

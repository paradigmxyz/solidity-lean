import SolidCore.Refinement.Evm.WideStorage

/-!
# Symbolic execution of a function that writes storage, from any storage

`Evm.WideStorage` reads the callee's storage before the call (`getStorage_preState_toBeBytes`,
`getStorage_recordStorageRead`) and runs a function that writes storage from any storage
(`run_of_postS_at`). This module adds `getStorage_writeOf_any`: the storage after one write
over any state, the written word at its key and the state's own word elsewhere.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace SolidCore.Refinement.Evm.Wide

/-- The storage after one write over any state: the written word at its key, the state's own
word elsewhere. -/
theorem getStorage_writeOf_any (tx : TransactionState) (a : Address) (k : Bytes32) (v : U256)
    (a' : Address) (k' : Bytes32) :
    (writeOf tx a k v).getStorage a' k' = if a' = a ∧ k' = k then v else tx.getStorage a' k' := by
  simp only [writeOf, TransactionState.getStorage, TransactionState.recordAccountRead,
    StorageMap.slot]
  by_cases ha : a' = a
  · subst ha
    by_cases hk : k' = k
    · subst hk; simp
    · have hk' : (k = k') = False := eq_false (fun h => hk h.symm)
      simp only [Std.ExtTreeMap.getElem?_insert_self, Option.bind_some, hk, and_false,
        ↓reduceIte, Std.ExtTreeMap.getElem?_insert, Std.compare_eq_iff_eq, hk']
      cases h : tx.storageWrites[a']? <;> simp [h, Std.ExtTreeMap.getD_eq_getD_getElem?] <;> rfl
  · have ha' : (a = a') = False := eq_false (fun h => ha h.symm)
    simp [ha, ha', Std.ExtTreeMap.getElem?_insert]
    rfl

/-- info: 'SolidCore.Refinement.Evm.Wide.getStorage_writeOf_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms getStorage_writeOf_any

end SolidCore.Refinement.Evm.Wide

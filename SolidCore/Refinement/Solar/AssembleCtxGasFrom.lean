import SolidCore.Refinement.Solar.AssembleCtxGas

/-!
# The forward assembly theorem with gas, from any caller

`Final.Target.runWith gas` runs one message from the fixed account `callerAddress`. Here
`Final.Target.runWithFrom a gas` runs the same message from the account `a` (its sender and the
transaction's origin, holding exactly the call's value), any account below `2 ^ 160` but the
contract's own, at `gas` gas; at `callerAddress` it is `runWith` (`runWithFrom_callerAddress`).

`forward_of_checkXLFrom` is `AssembleCtxGas.forward_of_checkXL` for it: when SolarTV's run of
`guard F p`, under an oracle whose CALLER is `a` and whose Keccak-256 is EthLib's, ends within
`n` blocks, then at every gas from `gasBoundL cx.base n` on EthLib runs the exact bytecode from
`a` to exactly that result. The bound is the same for every caller: it charges every item of the
lowered program 22100 gas, at least the price of any instruction of the loop checker's fragment
under EIP-2929 (an SSTORE to a cold slot that sets a zero slot: 20000 + 2100; a cold SLOAD: 2100),
whatever slots and accounts the call finds warm or cold; EthLib's interpreter meters the actual
accesses, so the theorem holds of the access sets the run builds, not of a model of them.

The lemmas on `preStateFrom` follow `AssembleSim`'s on `preState`.
-/

namespace SolidCore.Refinement.Target

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State

/-- The transaction of a call from the account `caller`, its origin. -/
def txEnvFrom (caller : Nat) : TransactionEnvironment .fusaka :=
  { origin := address caller, gasPrice := 0, blobVersionedHashes := fun _ => [] }

/-- The state before a call from the account `caller`: `code` at `selfAddress` with the call's
storage, and `caller` holding exactly the call value. -/
def preStateFrom (caller : Nat) (code : ByteArray) (call : Call) : TransactionState :=
  let hash := EthLib.Cryptography.Hash.Keccak.keccak256 code
  let storage : Std.ExtTreeMap Bytes32 U256 :=
    call.storage.foldl (fun m kv => m.insert (storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅
  let pre : State :=
    { accounts := ((∅ : Std.ExtTreeMap Address Account).insert (address selfAddress)
          { nonce := 1, balance := 0, codeHash := hash }).insert (address caller)
          { nonce := 0, balance := BitVec.ofNat 256 call.callvalue,
            codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 .empty },
      storage := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert
        (address selfAddress) storage,
      code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert hash code }
  TransactionState.ofBlock
    { preState := pre, accountWrites := ∅, storageWrites := ∅, codeWrites := ∅,
      storageClears := ∅ }

/-- The message of a call from the account `caller` with `gas` gas to `selfAddress`. -/
def messageFromWith (caller gas : Nat) (code : ByteArray) (call : Call) : Message .fusaka :=
  { blockEnv, txEnv := txEnvFrom caller, caller := address caller,
    target := some (address selfAddress),
    currentTarget := address selfAddress, gas, value := call.callvalue,
    data := call.calldata, codeAddress := some (address selfAddress),
    code, depth := 0, shouldTransferValue := true, isStatic := false,
    disablePrecompiles := false }

theorem preStateFrom_callerAddress : preStateFrom callerAddress = preState := rfl

end SolidCore.Refinement.Target

namespace SolidCore.Refinement.Final.Target

open EthLib.Base EthLib.Execution EthLib.Execution.Evm

/-- **EthLib's run of `call` from the account `caller` with `gas` gas.** -/
def runWithFrom (caller gas : Nat) (code : ByteArray) (call : Call) : Option Observable :=
  match processMessage (Meter := Nat) .fusaka (Refinement.Target.messageFromWith caller gas code call)
      (Refinement.Target.preStateFrom caller code call) Substate.empty with
  | .error _ => none
  | .ok ⟨evm, _⟩ =>
    let success := evm.error.isNone
    some
      { success
        output := evm.output.toList.map (·.toNat)
        logs :=
          if success then
            evm.substate.logs.toList.map fun log =>
              (log.topics.map fun topic => bytesToNat topic.toList,
                log.data.toList.map (·.toNat))
          else []
        storage := fun slot =>
          if success then
            (evm.state.getStorage (Refinement.Target.address selfAddress)
              (Refinement.Target.storageKey slot)).toNat
          else slotValue call.storage slot }

/-- From `callerAddress` it is `runWith`. -/
theorem messageFromWith_callerAddress (gas : Nat) (code : ByteArray) (call : Call) :
    Refinement.Target.messageFromWith callerAddress gas code call = messageWith gas code call := rfl

theorem runWithFrom_callerAddress : runWithFrom callerAddress = runWith := by
  funext gas code call
  simp only [runWithFrom, runWith, runMsg, messageFromWith_callerAddress,
    Refinement.Target.preStateFrom_callerAddress]
  split <;> rename_i h <;> rw [h]

end SolidCore.Refinement.Final.Target

namespace SolidCore.Refinement.Solar.Assemble

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex

/-- The word of the address of a number below `2 ^ 160` is the number. -/
theorem address_toNat {n : Nat} (h : n < 2 ^ 160) : (Target.address n).toU256.toNat = n := by
  have h20 : n < 256 ^ 20 := by simpa using h
  simp only [Address.toU256, Target.address, BitVec.toNat_ofNat]
  rw [show (⟨(natToBytes 20 n).toArray, _⟩ : Address).toList = natToBytes 20 n from rfl,
    bytesToNat_natToBytes_of_lt h20]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

/-- The address of an account below `2 ^ 160` other than `selfAddress` is not the contract's. -/
theorem address_ne_self {a : Nat} (ha : a < 2 ^ 160) (hne : a ≠ selfAddress) :
    Target.address selfAddress ≠ Target.address a := fun h => by
  apply hne
  have : (Target.address selfAddress).toU256.toNat = (Target.address a).toU256.toNat :=
    congrArg (fun x : Address => x.toU256.toNat) h
  rw [address_toNat ha, address_toNat (show selfAddress < 2 ^ 160 by decide)] at this
  exact this.symm

theorem precompileAddress_messageFromWith (a gas : Nat) (code : ByteArray) (call : SolarTV.Call) :
    precompileAddress .fusaka (Target.messageFromWith a gas code call) = none := by
  have h := precompileAddress_message code call
  unfold precompileAddress at h ⊢
  exact h

theorem getStorage_preStateFrom (a : Nat) (code : ByteArray) (call : SolarTV.Call) (k : Nat) :
    ((Target.preStateFrom a code call).getStorage (Target.address selfAddress)
      (Target.storageKey k)).toNat = slotValue call.storage k := by
  simp only [Target.preStateFrom, TransactionState.getStorage, TransactionState.ofBlock,
    StorageMap.slot, State.getStorage]
  simp
  exact getD_foldl_insert _ _ _ _ (by simp)

theorem getAccount_preStateFrom_self (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) :
    (Target.preStateFrom a code call).getAccount (Target.address selfAddress) =
      { nonce := 1, balance := 0, codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 code } := by
  simp only [Target.preStateFrom, TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock, State.getAccountOptional]
  rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right (fun h => absurd (Std.LawfulEqCmp.eq_of_compare h).symm hAB),
    Std.ExtTreeMap.getElem?_insert, ite_eq_left (Std.ReflCmp.compare_self)]
  simp

theorem account_preStateFrom (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) :
    (Target.preStateFrom a code call).getAccountOptional (Target.address selfAddress) ≠ none := by
  simp only [Target.preStateFrom, TransactionState.getAccountOptional, TransactionState.ofBlock,
    State.getAccountOptional]
  rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right (fun h => absurd (Std.LawfulEqCmp.eq_of_compare h).symm hAB),
    Std.ExtTreeMap.getElem?_insert, ite_eq_left (Std.ReflCmp.compare_self)]
  simp

theorem getAccount_preStateFrom_caller (a : Nat) (code : ByteArray) (call : SolarTV.Call) :
    ((Target.preStateFrom a code call).getAccount (Target.address a)).balance =
      BitVec.ofNat 256 call.callvalue := by
  simp only [Target.preStateFrom, TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock, State.getAccountOptional]
  simp

/-- `rel_initial` from the account `a`, at any gas. -/
theorem rel_initialFrom (a gas : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) :
    Rel (Target.messageFromWith a gas code call) Substate.empty (Target.preStateFrom a code call)
      Substate.empty (SolarTV.Machine.State.initial call) :=
  rel_of_pre rfl (getStorage_preStateFrom a code call) (account_preStateFrom a hAB code call)

/-- `moveEther_preState_any` from the account `a`. -/
theorem moveEther_preStateFrom_any (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) :
    ∃ st', (Target.preStateFrom a code call).moveEther .fusaka (Target.address a)
      (Target.address selfAddress) (BitVec.ofNat 256 call.callvalue) = .ok st' :=
  moveEther_of_balance hAB (by rw [getAccount_preStateFrom_caller]; exact BitVec.le_refl _)
    (by rw [getAccount_preStateFrom_self a hAB])

/-- `run_of_rel_with` from the account `a`: `runWithFrom a gas` of any call, with or without value. -/
theorem run_of_rel_withFrom (a gas : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) (s : SolarTV.Machine.State)
    (halt : SolarTV.Machine.Halt)
    (h : ∀ st, Rel (Target.messageFromWith a gas code call) Substate.empty st Substate.empty
        (SolarTV.Machine.State.initial call) →
      Spec .fusaka (At code (Target.messageFromWith a gas code call) 0 [] .empty gas st Substate.empty
        .empty) (PostL call (Target.address selfAddress) Substate.empty s halt)) :
    Final.Target.runWithFrom a gas code call = some (SolarTV.Machine.observe call s halt) := by
  obtain ⟨evm, hr, he⟩ := run_of_rel_msg (Target.messageFromWith a gas code call)
    (Target.preStateFrom a code call) rfl rfl (precompileAddress_messageFromWith a gas code call) hAB
    (show ((Target.preStateFrom a code call).getAccount (Target.address selfAddress)).nonce ≠ 0 by
      rw [getAccount_preStateFrom_self a hAB]; simp)
    (moveEther_preStateFrom_any a hAB code call) (rel_initialFrom a gas hAB code call) h
  simp only [Final.Target.runWithFrom, hr]
  exact congrArg some he

end SolidCore.Refinement.Solar.Assemble

namespace SolidCore.Refinement.Solar.AssembleCtxGas

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- **The forward assembly theorem with gas, from any caller.** For every account `a` but the
contract's: when SolarTV's run of `guard F p` under an oracle whose CALLER is `a` ends within
`n` blocks, then at every gas from `gasBoundL cx.base n` on, EthLib runs the exact bytecode from
`a` to exactly that result, a revert with its data included. A program that reads the
transaction's environment (`cx.base.reads`) is covered only where that environment is
`Target.txEnv`'s. -/
theorem forward_of_checkXLFrom {F : List Nat} {p : Assemble.Program} {code : ByteArray}
    {cx : CtxCert} (hc : checkXL F p code cx = true) (a : Nat)
    (hAB : Target.address selfAddress ≠ Target.address a) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → OracleOkAt a o)
    (he : cx.base.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv)
    (call : SolarTV.Call) (n : Nat) (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL cx.base n ≤ gas) :
    Final.Target.runWithFrom a gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hcount, hneed0, hF0⟩ := globXL_of_checkXL hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine Assemble.run_of_rel_withFrom a gas hAB code call r.2 r.1 fun st R => ?_
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  refine SpecG.toSpec (run_simXL (a := a) G rfl (by simp [Target.messageFromWith]) rfl rfl rfl ho rfl
    (fun h => (he h).2) (fun h => (he h).1)
    n 0 [] [] _ 0 .empty gas st Substate.empty
    ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame, Nat.zero_le _,
      fun _ => ⟨by simp [hn0, hneed0], by simp⟩, SR.nil _ _, ⟨?_, ?_, by simp, memRel_initial⟩,
      fun _ => ⟨0, hcount, hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
        by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩ R r hit)
  · rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  · rw [hm0, hsame.2.2]
    unfold gasBoundL at hg
    exact Nat.le_trans (Nat.add_le_add_left (Nat.sub_le _ _) _) hg

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_of_checkXLFrom

/-- At `callerAddress` it is `forward_of_checkXL`'s statement. -/
theorem forward_of_checkXL' {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXL F p code cx = true) (o : SolarTV.Machine.Oracle)
    (ho : cx.base.env = true → OracleOk o) (he : cx.base.reads = true → EnvOk o)
    (call : SolarTV.Call) (n : Nat) (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL cx.base n ≤ gas) :
    Final.Target.runWith gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  rw [← Final.Target.runWithFrom_callerAddress]
  exact forward_of_checkXLFrom hc callerAddress (by decide) o ho (fun h => ⟨he h, rfl⟩) call n r hit hg

end SolidCore.Refinement.Solar.AssembleCtxGas

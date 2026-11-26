import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# The backward assembly theorem with contexts, from any caller

`within_of_checkXLFrom` is `AssembleCtxGas.within_of_checkXL` for `Final.Target.runWithFrom a`:
when SolarTV's run of `guard F p`, under an oracle whose CALLER is `a`, ends within `n` blocks,
every result EthLib gives for the exact bytecode from `a` at any gas is that run's result, or a
failure that changes nothing. A run that succeeds is `observe_of_checkXL`'s, with the message,
the pre-state and its relation from `a` (`rel_startFrom`, after `rel_start`), for a certificate
that reads no block or transaction field (`cx.base.reads = false`, whose oracle obligations then do
not arise).
-/

namespace SolidCore.Refinement.Solar.AssembleCtxGas

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- `rel_start` from the account `a`. -/
theorem rel_startFrom (a gas : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) {st' : State.TransactionState} (ss' : Substate)
    (h : ¬ ((Target.messageFromWith a gas code call).shouldTransferValue = true ∧
        (Target.messageFromWith a gas code call).value ≠ 0) → st' = Target.preStateFrom a code call)
    (hm : ((Target.messageFromWith a gas code call).shouldTransferValue = true ∧
        (Target.messageFromWith a gas code call).value ≠ 0) →
      (Target.preStateFrom a code call).moveEther .fusaka (Target.messageFromWith a gas code call).caller
        (Target.messageFromWith a gas code call).currentTarget
        (Target.messageFromWith a gas code call).value = .ok st') :
    Rel (Target.messageFromWith a gas code call) ss' st' ss' (SolarTV.Machine.State.initial call) := by
  have R0 := rel_initialFrom a gas hAB code call
  by_cases htr : (Target.messageFromWith a gas code call).shouldTransferValue = true ∧
      (Target.messageFromWith a gas code call).value ≠ 0
  · have hmove := hm htr
    have hn : ((Target.preStateFrom a code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
      rw [getAccount_preStateFrom_self a hAB]; simp
    exact ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
      (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, ⟨[], by simp, .nil⟩⟩
  · obtain rfl := h htr
    exact ⟨R0.storage, R0.account, ⟨[], by simp, .nil⟩⟩

open SolidCore.Refinement.Evm.Symex in
theorem within_of_checkXLFrom {F : List Nat} {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXL F p code cx = true) (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (o : SolarTV.Machine.Oracle) (ho : cx.base.env = true → OracleOkAt a o)
    (hreads : cx.base.reads = false) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call (guard F p)) n
      (0, [], SolarTV.Machine.State.initial call) = some r) (gas : Nat) (obs : Observable)
    (hrun : Final.Target.runWithFrom a gas code call = some obs) :
    obs = SolarTV.Machine.observe call r.2 r.1 ∨
      (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) := by
  unfold Final.Target.runWithFrom at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  cases hrun
  by_cases hok : evm.error = none
  · exact Or.inl (observe_of_checkXL hc (msg := Target.messageFromWith a gas code call)
      (st0 := Target.preStateFrom a code call) rfl rfl (by simp [Target.messageFromWith]) rfl rfl rfl
      (precompileAddress_messageFromWith a gas code call) ho rfl (fun h => absurd h (by simp [hreads]))
      (fun h => absurd h (by simp [hreads])) (rel_startFrom a gas hAB code call) n r hit hpm hok)
  · exact Or.inr (by simp [hok, Option.ne_none_iff_isSome.mp hok])

end SolidCore.Refinement.Solar.AssembleCtxGas

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXLFrom

import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# The backward assembly theorem with contexts, from any caller

\`within_of_checkXLFrom\` is \`AssembleCtxGas.within_of_checkXL\` for \`Final.Target.runWithFrom a\`:
when SolarTV's run of \`guard F p\`, under an oracle whose CALLER is \`a\`, ends within \`n\` blocks,
every result EthLib gives for the exact bytecode from \`a\` at any gas is that run's result, or a
failure that changes nothing. Same proof, with the message, the pre-state and its relation from
\`a\` (\`rel_startFrom\`, after \`rel_start\`), for a certificate that reads no block or transaction
field (\`cx.base.reads = false\`, whose oracle obligations then do not arise).
-/

namespace SolidCore.Refinement.Solar.AssembleCtxGas

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCtx
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- \`rel_start\` from the account \`a\`. -/
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
  obtain ⟨G, hseg, hcount, hneed0, hF0⟩ := globXL_of_checkXL hc
  unfold Final.Target.runWithFrom at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  cases hrun
  cases hok : evm.error
  case some => exact Or.inr (by simp)
  left
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Target.messageFromWith a gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_messageFromWith a gas code call) hpm hok
  simp only at hrf
  set msg := Target.messageFromWith a gas code call with hmsg
  have hcode : msg.code = code := rfl
  have R := rel_startFrom a gas hAB code call ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hsim := run_simXL (msg := msg) (ss0 := ss') G rfl (by simp [msg, Target.messageFromWith]) rfl rfl
    (a := a) rfl ho rfl (fun h => absurd h (by simp [hreads])) (fun h => absurd h (by simp [hreads])) n 0 [] [] _ 0 .empty (gas + gasBoundL cx.base n) st' ss'
    ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame, Nat.zero_le _,
      fun _ => ⟨by simp [hn0, hneed0], by simp⟩, SR.nil _ _,
      ⟨by rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]; exact hseg,
        by
          rw [hm0]
          show 22100 * (n * bmax cx.base) + (memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0) ≤ _
          have : memoryGasCost (certAt cx (p.blocks.length + 1) 0 0).top - 0 ≤ memoryGasCost cx.base.top := by
            rw [hsame.2.2]; exact Nat.sub_le _ _
          unfold gasBoundL; omega,
        by simp, memRel_initial⟩,
      fun _ => ⟨0, hcount, hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
        by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩ R r hit
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas (gasBoundL cx.base n)
  rcases r with ⟨halt, sF⟩
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := SpecG.low hsim hp within hrf hok
  have hss' : ss'.logs.toList = [] := by
    by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
    · rw [(hmove htr).2]
      simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
    · rw [(hcases htr).2]
      simp [Substate.empty]
  have hlogs : (SolarTV.Machine.observe call sF halt).success = true →
      (SolarTV.Machine.observe call sF halt).logs = SolarTV.Machine.logs sF := by
    cases halt <;> simp [SolarTV.Machine.observe]
  generalize SolarTV.Machine.observe call sF halt = X at herr hout hst hlogs ⊢
  obtain ⟨success, output, logs, storage⟩ := X
  obtain rfl : success = true := by cases success <;> simp_all [errorOf]
  simp only at hst hlogs
  simp only [Option.isNone_none, ite_true, SolarTV.Observable.mk.injEq, true_and]
  refine ⟨hout, ?_, funext (hst trivial)⟩
  rw [show evm.substate.logs = ssF.logs from hlogsF, hL1, hss', List.nil_append, logs_of_match hL2,
    hlogs trivial]
  rfl


end SolidCore.Refinement.Solar.AssembleCtxGas

/-- info: 'SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXLFrom

import SolidCore.Refinement.Solar.AssembleLoopRun

namespace SolidCore.Refinement.Solar.AssembleLoop

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State

theorem rollbackOnError_ok {snap : TransactionState} {e : Evm .fusaka Nat}
    (h : (rollbackOnError snap e).error = none) : rollbackOnError snap e = e := by
  unfold rollbackOnError at h ⊢
  split at h
  · rename_i hs; simp only at h; simp [h] at hs
  · rename_i hs; simp [hs]

/-- A message to code that is no precompile that ends with no error ran its frame to that end:
from the state, or from the state after the move of the value. -/
theorem processMessage_ok {message : Message .fusaka} (hpre : precompileAddress .fusaka message = none)
    {st : TransactionState} {ss : Substate} {evm}
    (hr : processMessage (Meter := Nat) .fusaka message st ss = .ok evm) (hok : evm.1.error = none) :
    ∃ (st' : TransactionState) (ss' : Substate) (runChild : MessageRunner .fusaka Nat message.gas)
      (within : GasMeter.gasHeld (startFrame message st' ss' message.gas).gas ≤ message.gas),
      (¬ (message.shouldTransferValue = true ∧ message.value ≠ 0) → st' = st ∧ ss' = ss) ∧
      ((message.shouldTransferValue = true ∧ message.value ≠ 0) →
        st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st' ∧
        ss' = { ss with logs := (pushTransferLog .fusaka ss.logs message.caller message.currentTarget
          message.value) }) ∧
      runFrame (step .fusaka) (step_decreases .fusaka) message.gas runChild
        (startFrame message st' ss' message.gas) within = .ok evm.1 := by
  rw [processMessage] at hr
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre] at hr
  by_cases htr : message.shouldTransferValue = true ∧ message.value ≠ 0
  · simp only [htr, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hr
    cases hm : st.moveEther .fusaka message.caller message.currentTarget message.value with
    | error e => simp [hm, Except.mapError, bind, Except.bind, Except.map] at hr
    | ok st' =>
      simp only [hm, Except.mapError, bind, Except.bind, pure, Except.pure] at hr
      split at hr
      · simp [throw, throwThe, MonadExceptOf.throw, Except.map] at hr
      · rename_i after hrf
        simp only [Except.map, Except.ok.injEq] at hr
        subst hr
        have := rollbackOnError_ok hok
        simp only [htr.1, htr.2, not_false_eq_true, and_self, ↓reduceIte] at hrf
        rw [← this] at hrf
        exact ⟨st', _, _, _, fun h => absurd htr h, fun _ => ⟨rfl, rfl⟩, hrf⟩
  · simp only [htr, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · simp [throw, throwThe, MonadExceptOf.throw, Except.map] at hr
    · rename_i after hrf
      simp only [Except.map, Except.ok.injEq] at hr
      subst hr
      have := rollbackOnError_ok hok
      simp only [htr, ↓reduceIte] at hrf
      rw [← this] at hrf
      exact ⟨st, ss, _, _, fun _ => ⟨rfl, rfl⟩, fun h => absurd h htr, hrf⟩

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Evm.Wide in
/-- The frame of a call with `gas` gas, from a state related to the call's storage. -/
theorem rel_start (code : ByteArray) (call : SolarTV.Call) (gas : Nat) {st' : TransactionState}
    (ss' : Substate)
    (h : ¬ ((Final.Target.messageWith gas code call).shouldTransferValue = true ∧
        (Final.Target.messageWith gas code call).value ≠ 0) → st' = Target.preState code call)
    (hm : ((Final.Target.messageWith gas code call).shouldTransferValue = true ∧
        (Final.Target.messageWith gas code call).value ≠ 0) →
      (Target.preState code call).moveEther .fusaka (Final.Target.messageWith gas code call).caller
        (Final.Target.messageWith gas code call).currentTarget
        (Final.Target.messageWith gas code call).value = .ok st') :
    Rel (Final.Target.messageWith gas code call) ss' st' ss' (SolarTV.Machine.State.initial call) := by
  have R0 := rel_initial code call
  by_cases htr : (Final.Target.messageWith gas code call).shouldTransferValue = true ∧
      (Final.Target.messageWith gas code call).value ≠ 0
  · have hmove := hm htr
    have hn : ((Target.preState code call).getAccount (Target.address selfAddress)).nonce ≠ 0 := by
      rw [getAccount_preState_self]; simp
    have hAB : Target.address selfAddress ≠ Target.address callerAddress := by decide
    exact ⟨fun k => ((moveEther_recipient hmove hAB hn _).1).trans (R0.storage k),
      (moveEther_recipient hmove hAB hn (Target.storageKey 0)).2, ⟨[], by simp, .nil⟩⟩
  · obtain rfl := h htr
    exact ⟨R0.storage, R0.account, ⟨[], by simp, .nil⟩⟩

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Final
  SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at every gas, for code with loops.** For every program and code the checker
of code with loops accepts, under every oracle whose caller and hash are EthLib's when the program
reads them, at every gas: every result the bytecode gives on a call is the result SolarTV's EVM IR
semantics gives, or a failure that leaves the storage and logs nothing. -/
theorem within_of_checkL {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (scope : SolarTV.Call → Prop) (gas : Nat) :
    Within (SolarTV.evmirSem o) (ethLibWith gas) p code scope := by
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  intro call _ obs hrun
  change Target.runWith gas code call = some obs at hrun
  cases hs : obs.success
  · exact Or.inr ⟨rfl, Target.runWith_failure hrun hs⟩
  left
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hs
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  -- The run, the reserve and the fuel.
  set msg := Final.Target.messageWith gas code call with hmsg
  have hcode : msg.code = code := rfl
  have hgas : msg.gas = gas := rfl
  have R := rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  generalize hW : p.blocks.length + 2 = W
  generalize hn : 2 * (W * gas) + W + p.blocks.length + 1 = n
  generalize hK : 22100 * (n * bmax c) + memoryGasCost c.top = K
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty (gas + K) :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; omega, by simp, memRel_initial⟩
  have hsim := run_simL (msg := msg) (ss0 := ss') G rfl (by simp [msg, Final.Target.messageWith,
    Target.message]) rfl rfl rfl ho n 0 [] [] _ 0 .empty (gas + K) st' ss' (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _) E0 R
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas K
  cases hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) with
  | none =>
    exfalso
    obtain ⟨z, hz, hmeas⟩ := hsim.2 hit _ hp
    obtain ⟨m, -, rfl, -⟩ := reaches_low hz K _ rfl within hrf hok
    have h1 : W * K ≤ W * (m.gas + K) := Nat.mul_le_mul_left _ (by simp)
    simp only [gas_addGas] at hmeas h1
    unfold meas at hmeas
    rw [hW] at hmeas
    have h2 : W * (gas + K) = W * gas + W * K := Nat.mul_add _ _ _
    split at hmeas <;> omega
  | some r =>
    rcases r with ⟨halt, sF⟩
    have hres : (SolarTV.evmirSem o).run p call = some (SolarTV.Machine.observe call sF halt) := by
      change (SolarTV.EVM.Program.layer.result o p call).map _ = _
      rw [SolarTV.EVM.Program.layer.result_of_ends ⟨n, hit⟩]
      rfl
    rw [hres]
    obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ :=
      SpecG.low (hsim.1 _ hit) hp within hrf hok
    have hss' : ss'.logs.toList = [] := by
      by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
      · rw [(hmove htr).2]
        simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
      · rw [(hcases htr).2]
        simp [Substate.empty]
    have hlogs := logs_of_match hL2
    have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
    have herr' : evm.error = errorOf (SolarTV.Machine.observe call sF halt) := herr
    have hout' : evm.output.toList.map (·.toNat) = (SolarTV.Machine.observe call sF halt).output := hout
    have hst' : (SolarTV.Machine.observe call sF halt).success = true →
        evm.substate.logs = ssF.logs ∧ ∀ slot,
          (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
            (SolarTV.Machine.observe call sF halt).storage slot :=
      fun h => ⟨hlogsF, hst h⟩
    have hfail : (SolarTV.Machine.observe call sF halt).success = false →
        (SolarTV.Machine.observe call sF halt).logs = [] ∧
        (SolarTV.Machine.observe call sF halt).storage = slotValue call.storage := by
      cases halt <;> simp [SolarTV.Machine.observe]
    have hok2 : (SolarTV.Machine.observe call sF halt).success = true →
        (SolarTV.Machine.observe call sF halt).logs = SolarTV.Machine.logs sF := by
      cases halt <;> simp [SolarTV.Machine.observe]
    clear herr hout hst hres hsim hit
    generalize SolarTV.Machine.observe call sF halt = X at *
    have hsucc : evm.error.isNone = X.success := by
      rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
    symm
    congr 1
    cases X with
    | mk success output logs storage =>
      simp only at hsucc hout' hfail hok2 hst' ⊢
      rw [SolarTV.Observable.mk.injEq]
      refine ⟨hsucc, hout', ?_, ?_⟩
      · rw [hsucc]
        cases hs : success
        · simp [hok, hs] at hsucc
        · simp only [ite_true]
          rw [(hst' hs).1, hL1', hlogs, hok2 hs]
          rfl
      · funext slot
        rw [hsucc]
        cases hs : success
        · simp [hok, hs] at hsucc
        · simp only [ite_true]
          exact (hst' hs).2 slot

/--
info: 'SolidCore.Refinement.Solar.AssembleLoop.within_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms within_of_checkL

end SolidCore.Refinement.Solar.AssembleLoop

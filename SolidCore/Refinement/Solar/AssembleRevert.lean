import SolidCore.Refinement.Solar.EthLibErrLow
import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# EVM IR to bytecode with the revert data related

`Final.Within` lets every failure of the bytecode stand for itself: a run that fails rolls back and
logs nothing, and nothing relates its output to the EVM IR's. That admits a bytecode that reverts
with other data than the program, or reverts where the program does not. `WithinR` keeps the
weaker disjunct only for an exceptional halt (`HaltsExceptionally`: the run ends with an error that
is no REVERT, such as out of gas): every other result of the bytecode, a run that reverts among
them, is the EVM IR's result, so its revert data are the program's, byte for byte, and its storage
is the call's.

* `processMessage_frame`: a message to code that is no precompile ran its frame, and the message
  ends with that frame's error and output (`rollbackOnError` keeps them).
* `withinR_of_checkL`: for every program and code the checker of code with loops accepts, at every
  gas, `WithinR`. A run that reverts is transferred to the run with the checker's reserve of gas by
  `RevertErr.SpecG.lowR`, which rests on `RevertErr.step_good` (no step throws a revert, and only
  REVERT ends a frame with it).
* `WithinR.within`: `WithinR` gives `Final.Within`.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolarTV

theorem error_rollbackOnError (snap : TransactionState) (e : Evm .fusaka Nat) :
    (rollbackOnError snap e).error = e.error := by
  unfold rollbackOnError; split <;> rfl

theorem output_rollbackOnError (snap : TransactionState) (e : Evm .fusaka Nat) :
    (rollbackOnError snap e).output = e.output := by
  unfold rollbackOnError; split <;> rfl

/-- A message to code that is no precompile ran its frame, from the state or from the state after
the move of the value, and ends with the error and the output of that frame. -/
theorem processMessage_frame {message : Message .fusaka}
    (hpre : precompileAddress .fusaka message = none) {st : TransactionState} {ss : Substate} {evm}
    (hr : processMessage (Meter := Nat) .fusaka message st ss = .ok evm) :
    ∃ (st' : TransactionState) (ss' : Substate) (runChild : MessageRunner .fusaka Nat message.gas)
      (within : GasMeter.gasHeld (startFrame message st' ss' message.gas).gas ≤ message.gas)
      (fr : Evm .fusaka Nat),
      (¬ (message.shouldTransferValue = true ∧ message.value ≠ 0) → st' = st ∧ ss' = ss) ∧
      ((message.shouldTransferValue = true ∧ message.value ≠ 0) →
        st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st' ∧
        ss' = { ss with logs := (pushTransferLog .fusaka ss.logs message.caller message.currentTarget
          message.value) }) ∧
      runFrame (step .fusaka) (step_decreases .fusaka) message.gas runChild
        (startFrame message st' ss' message.gas) within = .ok fr ∧
      evm.1.error = fr.error ∧ evm.1.output = fr.output := by
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
        simp only [htr.1, htr.2, not_false_eq_true, and_self, ↓reduceIte] at hrf
        exact ⟨st', _, _, _, _, fun h => absurd htr h, fun _ => ⟨rfl, rfl⟩, hrf,
          error_rollbackOnError _ _, output_rollbackOnError _ _⟩
  · simp only [htr, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · simp [throw, throwThe, MonadExceptOf.throw, Except.map] at hr
    · rename_i after hrf
      simp only [Except.map, Except.ok.injEq] at hr
      subst hr
      simp only [htr, ↓reduceIte] at hrf
      exact ⟨st, ss, _, _, _, fun _ => ⟨rfl, rfl⟩, fun h => absurd h htr, hrf,
        error_rollbackOnError _ _, output_rollbackOnError _ _⟩

open SolidCore.Refinement.Final

/-- The run of `code` on `call` with `gas` gas halts exceptionally: it ends with an error that is
no REVERT (out of gas, a stack error, an invalid jump, ...). -/
def HaltsExceptionally (gas : Nat) (code : ByteArray) (call : SolarTV.Call) : Prop :=
  ∃ evm, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (Refinement.Target.preState code call) Substate.empty = .ok evm ∧
    ∃ e, e ≠ .revert ∧ evm.1.error = some e

/-- **Refinement that relates reverts**: every result of `code` with `gas` gas on the scope is
the result of `p`, or the run halted exceptionally (`HaltsExceptionally`) and failed, leaving the
storage and logging nothing. A run that succeeds or reverts gives `p`'s result: the same output
(the revert data of a revert), the same logs and the same storage. -/
def WithinR (A : Sem) (gas : Nat) (p : A.Prog) (code : ByteArray) (scope : SolarTV.Call → Prop) :
    Prop :=
  ∀ call, scope call → ∀ obs, Final.Target.runWith gas code call = some obs →
    A.run p call = some obs ∨
      (HaltsExceptionally gas code call ∧ obs.success = false ∧
        obs.storage = slotValue call.storage ∧ obs.logs = [])

/-- `WithinR` is `Within` with the failures that may stand for themselves narrowed to exceptional
halts. -/
theorem WithinR.within {A : Sem} {gas : Nat} {p : A.Prog} {code : ByteArray}
    {scope : SolarTV.Call → Prop} (h : WithinR A gas p code scope) :
    Within A (ethLibWith gas) p code scope := by
  intro call hc obs hrun
  rcases h call hc obs hrun with h | ⟨-, hs, hst, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hs, hst, hl⟩

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Evm.Wide
  SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at every gas, for code with loops, with the revert data related.** For
every program and code the checker of code with loops accepts, under every oracle that
`within_of_checkL` admits, at every gas: every result the bytecode gives on a call is the result
of SolarTV's EVM IR semantics (a run that reverts too, with its revert data), or the run halted
exceptionally and failed with the storage kept and no log. -/
theorem withinR_of_checkL {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (scope : SolarTV.Call → Prop) (gas : Nat)
    (he : c.reads = true → EnvOk o := by intro h; exact absurd h (by decide)) :
    WithinR (SolarTV.evmirSem o) gas p code scope := by
  intro call hcall obs hrun
  have hrun0 := hrun
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  by_cases hex : ∃ e, e ≠ EvmError.revert ∧ evm.error = some e
  · obtain ⟨e, hne, he'⟩ := hex
    have hs : obs.success = false := by rw [← hrun]; simp [he']
    exact Or.inr ⟨⟨⟨evm, hev⟩, hpm, e, hne, he'⟩, hs, Target.runWith_failure hrun0 hs⟩
  left
  rcases herrc : evm.error with _ | e
  · rcases within_of_checkL hc o ho scope gas he call hcall obs hrun0 with h | ⟨hs, -⟩
    · exact h
    · rw [← hrun] at hs; simp [herrc] at hs
  have hrev : e = .revert := by
    by_contra hne
    exact hex ⟨e, hne, herrc⟩
  subst hrev
  subst hrun
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  obtain ⟨st', ss', runChild, within, fr, hcases, hmove, hrf, herrfr, houtfr⟩ :=
    processMessage_frame (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm
  simp only at herrfr houtfr
  have hfrrev : fr.error = some .revert := by rw [← herrfr, herrc]
  set msg := Final.Target.messageWith gas code call with hmsg
  have hcode : msg.code = code := rfl
  have R := rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  generalize hW : p.blocks.length + 2 = W
  generalize hn : 2 * (W * gas) + W + p.blocks.length + 1 = n
  generalize hK : 22100 * (n * bmax c) + memoryGasCost c.top = K
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty (gas + K) :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; omega, by simp, memRel_initial⟩
  have hsim := run_simL (msg := msg) (ss0 := ss') G rfl (by simp [msg, Final.Target.messageWith,
    Target.message]) rfl rfl rfl ho rfl rfl he n 0 [] [] _ 0 .empty (gas + K) st' ss' (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _) E0 R
  have hl : At code msg 0 [] .empty gas st' ss' .empty (startFrame msg st' ss' msg.gas) :=
    ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  have hp := hl.addGas K
  have hstart : (startFrame msg st' ss' msg.gas).error ≠ some .revert := by
    rw [hl.2.2.2.2.2.2.2.2.1]; simp
  have hfork : Fork.byzantium ≤ Fork.fusaka := by decide
  cases hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) with
  | none =>
    exfalso
    obtain ⟨z, hz, hmeas⟩ := hsim.2 hit _ hp
    obtain ⟨m, -, rfl, -⟩ := RevertErr.reaches_lowR hfork hz K _ rfl hstart within hrf hfrrev
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
    obtain ⟨ssF, ⟨herr, hout, -, -⟩, -⟩ :=
      RevertErr.SpecG.lowR hfork (hsim.1 _ hit) hp hstart within hrf hfrrev
    have herr' : fr.error = errorOf (SolarTV.Machine.observe call sF halt) := herr
    have hout' : fr.output.toList.map (·.toNat) = (SolarTV.Machine.observe call sF halt).output :=
      hout
    have hfail : (SolarTV.Machine.observe call sF halt).success = false →
        (SolarTV.Machine.observe call sF halt).logs = [] ∧
        (SolarTV.Machine.observe call sF halt).storage = slotValue call.storage := by
      cases halt <;> simp [SolarTV.Machine.observe]
    clear herr hout hres hsim hit
    generalize SolarTV.Machine.observe call sF halt = X at *
    have hsucc : fr.error.isNone = X.success := by
      rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
    rw [hfrrev] at hsucc
    simp only [Option.isNone_some] at hsucc
    obtain ⟨hlogs, hst⟩ := hfail hsucc.symm
    congr 1
    cases X with
    | mk success output logs storage =>
      simp only at hsucc hout' hlogs hst ⊢
      subst hsucc hlogs hst
      rw [SolarTV.Observable.mk.injEq]
      refine ⟨by simp [herrc], ?_, by simp [herrc], by funext slot; simp [herrc]⟩
      rw [houtfr]
      exact hout'.symm

/--
info: 'SolidCore.Refinement.Solar.AssembleLoop.withinR_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms withinR_of_checkL

end SolidCore.Refinement.Solar.AssembleLoop

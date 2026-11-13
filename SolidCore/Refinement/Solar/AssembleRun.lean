import SolidCore.Refinement.Solar.RunOracle
import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# EVM IR to bytecode at the given gas, run by run

The assembly theorems so far (`Assemble.stage_of_check`, `AssembleLoop.within_of_checkL`) run
EthLib's interpreter with gas to spare and carry a gas reserve through the simulation; a run with
less gas is then the same run with less gas left (`Logic.LessGas`). That argument holds only for
code whose every step is monotone in gas: GAS pushes the gas left, a call forwards all but a 64th
of it, and a copy of dynamic size has no static bound on its memory, so none of them fits it.

This file proves the refinement at the gas the run has, from a simulation block by block over
EthLib's steps under the runner of messages (`StepBy`, `HoareUnder`), with the oracle of the run
built as the run goes:

* `Advances`: from a frame related to a SolarTV block state, EthLib reaches a frame that failed
  (out of gas, or any exceptional halt), or the table of the run grows to `T'` (the gas a GAS read
  pushed, the success and output of a call) and every oracle of a table extending `T'` runs the
  block to the same end, which EthLib's frame shows (`Post`), or to the next block state, related
  to EthLib's frame with a lower measure.
* `run_of_advances`: a run of EthLib that ends with no error is, for every table extending the
  last one, SolarTV's run to the same end.
* `within_of_advances`: at every gas, for every call, the oracle of that run's table makes every
  result of the bytecode the EVM IR's or a failure that changes nothing: the per-run theorem
  (`RunOracle.WithinRun`) for code with GAS, calls and dynamic copies, from a block simulation.

The block simulation of the checker's fragment in this form (each instruction's rule when the
gas suffices, the frame failing when it does not, and the single-instruction effects of
`AssembleEffects` for GAS, the return data, copies and calls) is what remains to instantiate it.
-/

namespace SolidCore.Refinement.Solar.AssembleRun

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic
open EthLib.Execution.State

/-! ## Tables that grow -/

/-- `T'` extends `T`: each table of `T` is a prefix of `T'`'s. -/
def _root_.SolidCore.Refinement.Solar.RunOracle.RunTable.Le (T T' : RunTable) : Prop :=
  T.oks <+: T'.oks ∧ T.outs <+: T'.outs ∧ T.stores <+: T'.stores ∧
    T.transients <+: T'.transients ∧ T.gases <+: T'.gases

theorem _root_.SolidCore.Refinement.Solar.RunOracle.RunTable.Le.refl (T : RunTable) : T.Le T :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _⟩

theorem _root_.SolidCore.Refinement.Solar.RunOracle.RunTable.Le.trans {T1 T2 T3 : RunTable} (a : T1.Le T2) (b : T2.Le T3) : T1.Le T3 :=
  ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.1.trans b.2.2.1, a.2.2.2.1.trans b.2.2.2.1,
    a.2.2.2.2.trans b.2.2.2.2⟩

/-- An entry of a table is the same in every extension. -/
theorem getD_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : Nat} (hi : i < l.length)
    (d : α) : l'.getD i d = l.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-! ## A run, block by block -/

section Blocks

variable {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
  (O : RunTable → Oracle)

/-- **One block of the simulation, read back from a run that succeeds**: under every runner of
messages, when the loop runs the frame `evm` to a frame `fin` with no error, the table grows to `T'`
and every oracle of a table extending `T'` runs the block from `x` to the same `r`: an end `fin`
shows (`Post`), or the next block state, related (`E T'`) to a frame with a lower measure that the
loop runs to `fin` too. -/
def Advances (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets (fun _ _ _ => True) runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none →
      ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

/-- **One block of the simulation, forwards**: from the frame `evm`, under every runner of messages,
EthLib reaches a frame that failed, or the table grows to `T'` and every oracle of a table extending
`T'` runs the block to the same `r`: an end the frame reached shows, or the next block state,
related to the frame reached with a lower measure. -/
def AdvancesFwd (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  HoareUnder .fusaka (fun _ _ _ => True) (· = evm) fun after =>
    (after.running = false ∧ after.error ≠ none) ∨
    ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
      (∀ res, r = .inl res → after.running = false ∧ Post res after) ∧
      (∀ y, r = .inr y → E T' y after ∧ meas y after < meas x evm)

/-- A block that advances forwards advances in a run that succeeds. -/
theorem advances_of_fwd {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    {T : RunTable} {x : σ} {evm : Evm .fusaka Nat} (h : AdvancesFwd blk O E Post meas T x evm) :
    Advances blk O E Post meas T x evm := by
  intro bound runChild meets within fin hrun hok
  obtain ⟨after, hreach, hq⟩ := h bound runChild meets evm rfl within
  have within' := Nat.le_trans (hreach.gasHeld_le StepBy.gasHeld_le) within
  have hrun' := hrun
  rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within] at hrun'
  rcases hq with hq | aborted
  · rcases hq with ⟨hstop, herr⟩ | ⟨T', r, hle, hstep, hinl, hinr⟩
    · rw [runFrame_of_running_eq_false hstop] at hrun'
      cases hrun'
      exact absurd hok herr
    · refine ⟨T', r, hle, hstep, fun res hr => ?_, fun y hy => ?_⟩
      · obtain ⟨hstop, hpost⟩ := hinl res hr
        rw [runFrame_of_running_eq_false hstop] at hrun'
        cases hrun'
        exact hpost
      · obtain ⟨hE', hm'⟩ := hinr y hy
        exact ⟨after, within', hE', hm', hrun'⟩
  · obtain ⟨e, he, -⟩ := runFrame_of_abortsBy meets.aborts aborted within'
    rw [he] at hrun'
    cases hrun'

/-- **A run of EthLib that ends with no error is SolarTV's**, for every table extending the last
one the run grew. -/
theorem run_of_advances {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → Advances blk O E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets (fun _ _ _ => True) runChild) :
    ∀ (n : Nat) (T : RunTable) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none →
      ∃ T' res, T.Le T' ∧
        (∀ T'', T'.Le T'' → ∃ k, iterate (blk (O T'')) k x = some res) ∧
        Post res fin
  | 0, _, _, _, _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, T, x, evm, within, fin, hE, hm, hrun, hok => by
    obtain ⟨T', r, hle, hstep, hinl, hinr⟩ := adv T x evm hE bound runChild meets within fin hrun hok
    cases r with
    | inl res =>
      exact ⟨T', res, hle, fun T'' h => ⟨1, by simp [iterate, hstep T'' h]⟩, hinl res rfl⟩
    | inr y =>
      obtain ⟨after, within', hE', hm', hrun'⟩ := hinr y rfl
      obtain ⟨T2, res, hle2, hit, hpost⟩ :=
        run_of_advances adv meets n T' y after within' fin hE' (by omega) hrun' hok
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [iterate, hstep T'' (hle2.trans h), hk]⟩

end Blocks

/-! ## The message of a call -/

/-- `AssembleLoop.processMessage_ok` with the runner of messages named: the one the interpreter
runs the frame's calls and creations with. -/
theorem processMessage_ok' {message : Message .fusaka}
    (hpre : precompileAddress .fusaka message = none) {st : TransactionState} {ss : Substate} {evm}
    (hr : processMessage (Meter := Nat) .fusaka message st ss = .ok evm) (hok : evm.1.error = none) :
    ∃ (st' : TransactionState) (ss' : Substate)
      (within : GasMeter.gasHeld (startFrame message st' ss' message.gas).gas ≤ message.gas),
      (¬ (message.shouldTransferValue = true ∧ message.value ≠ 0) → st' = st ∧ ss' = ss) ∧
      ((message.shouldTransferValue = true ∧ message.value ≠ 0) →
        st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st' ∧
        ss' = { ss with logs := (pushTransferLog .fusaka ss.logs message.caller message.currentTarget
          message.value) }) ∧
      runFrame (step .fusaka) (step_decreases .fusaka) message.gas
        (processRunner .fusaka message.gas) (startFrame message st' ss' message.gas) within =
          .ok evm.1 := by
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
        have := AssembleLoop.rollbackOnError_ok hok
        simp only [htr.1, htr.2, not_false_eq_true, and_self, ↓reduceIte] at hrf
        rw [← this] at hrf
        exact ⟨st', _, _, fun h => absurd htr h, fun _ => ⟨rfl, rfl⟩, hrf⟩
  · simp only [htr, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · simp [throw, throwThe, MonadExceptOf.throw, Except.map] at hr
    · rename_i after hrf
      simp only [Except.map, Except.ok.injEq] at hr
      subst hr
      have := AssembleLoop.rollbackOnError_ok hok
      simp only [htr, ↓reduceIte] at hrf
      rw [← this] at hrf
      exact ⟨st, ss, _, fun _ => ⟨rfl, rfl⟩, fun h => absurd h htr, hrf⟩

/-! ## The refinement at the given gas -/

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at the given gas, run by run, from a block simulation**: when every frame
related to a block state (`E`, from the substate the frame started with) advances (`Advances`) to
an end SolarTV's halt shows (`PostL`) or to the next block, and the frame a call starts with is
related to SolarTV's initial state, then the oracle of the run's table makes every result of the
bytecode on the call the EVM IR's or a failure that changes nothing. -/
theorem within_of_advances {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → Advances (fun o => block o call p) O (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, Within (evmirSem (O T)) (ethLibWith gas) p code (· = call) := by
  by_cases hs : ∃ obs, Target.runWith gas code call = some obs ∧ obs.success = true
  swap
  · refine ⟨{}, fun call' hc obs hrun => Or.inr ?_⟩
    subst hc
    have hf : obs.success = false := by
      cases h : obs.success
      · rfl
      · exact absurd ⟨obs, hrun, h⟩ hs
    exact ⟨hf, Target.runWith_failure hrun hf⟩
  obtain ⟨obs, hrun, hsucc⟩ := hs
  suffices H : ∃ T, (evmirSem (O T)).run p call = some obs by
    obtain ⟨T, hT⟩ := H
    refine ⟨T, fun call' hc obs' hrun' => Or.inl ?_⟩
    subst hc
    change Target.runWith gas code call' = some obs' at hrun'
    rw [hrun] at hrun'
    cases hrun'
    exact hT
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hsucc
  obtain ⟨st', ss', within, hcases, hmove, hrf⟩ :=
    processMessage_ok' (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  have R := AssembleLoop.rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advances (fun o => block o call p) O (adv ss')
    (meets_process .fusaka _) _ {} _ _ within evm (start st' ss' R) (Nat.lt_succ_self _) hrf hok
  obtain ⟨k, hk⟩ := hit T (RunTable.Le.refl T)
  refine ⟨T, ?_⟩
  have hres : (evmirSem (O T)).run p call = some (observe call sF halt) := by
    change (SolarTV.EVM.Program.layer.result (O T) p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨k, hk⟩]
    rfl
  rw [hres]
  set msg := Final.Target.messageWith gas code call with hmsg
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := hpost
  have hss' : ss'.logs.toList = [] := by
    by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
    · rw [(hmove htr).2]
      simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
    · rw [(hcases htr).2]
      simp [Substate.empty]
  have hlogs := logs_of_match hL2
  have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
  have herr' : evm.error = errorOf (observe call sF halt) := herr
  have hout' : evm.output.toList.map (·.toNat) = (observe call sF halt).output := hout
  have hst' : (observe call sF halt).success = true →
      evm.substate.logs = ssF.logs ∧ ∀ slot,
        (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
          (observe call sF halt).storage slot :=
    fun h => ⟨hlogsF, hst h⟩
  have hfail : (observe call sF halt).success = false →
      (observe call sF halt).logs = [] ∧
      (observe call sF halt).storage = slotValue call.storage := by
    cases halt <;> simp [observe]
  have hok2 : (observe call sF halt).success = true →
      (observe call sF halt).logs = logs sF := by
    cases halt <;> simp [observe]
  clear herr hout hst hres hit hk
  generalize observe call sF halt = X at *
  have hsucc' : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  symm
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc' hout' hfail hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc', hout', ?_, ?_⟩
    · rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        exact (hst' hs).2 slot

/-- **Per run, from a block simulation**: under a base oracle meeting the certificate's constraints,
a block simulation at every gas and call gives the per-run refinement. -/
theorem withinRun_of_advances {p : Assemble.Program} {code : ByteArray} {scope : Call → Prop}
    {Ok : Oracle → Prop} (O : RunTable → Oracle) (hok : ∀ T, Ok (O T))
    (sim : ∀ gas call, scope call → ∃ (E : Substate → RunTable → Nat × List Word × Machine.State →
        Evm .fusaka Nat → Prop) (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat),
      (∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
          (Machine.State.initial call) →
        E ss' {} (0, [], Machine.State.initial call)
          (startFrame (Final.Target.messageWith gas code call) st' ss' gas)) ∧
      (∀ ss0 T x evm, E ss0 T x evm → Advances (fun o => SolarTV.EVM.Program.block o call p) O
        (E ss0)
        (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
        meas T x evm)) :
    WithinRun evmirSem (fun _ => p) code scope Ok := by
  intro gas call hc
  obtain ⟨E, meas, start, adv⟩ := sim gas call hc
  obtain ⟨T, hT⟩ := within_of_advances O E meas start adv
  exact ⟨O T, hok T, hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleRun.within_of_advances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_advances

/-- info: 'SolidCore.Refinement.Solar.AssembleRun.withinRun_of_advances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_of_advances

end SolidCore.Refinement.Solar.AssembleRun

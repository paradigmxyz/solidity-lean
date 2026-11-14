import SolidCore.Refinement.Solar.AssembleCreateSegF
import SolidCore.Refinement.Solar.AssembleCreateExample

/-!
# EVM IR to bytecode, run by run, for code with CALLs, CREATE2s and CODECOPYs

`AssembleCreateSegF.segF` reads a block back from a run that succeeds under the oracle of the run's two
tables (`AssembleCreateRun.FO`): the run table of GAS reads and messages, and the creation table.
`within_of_advancesF` is `AssembleCallSeg.within_of_advancesQ` over the pair of tables (`Tabs`), with an
assumption on the runner of messages that may name the runner (`RunOut`: the frames it returns), and
`runs_of_checkCF` is the per-run theorem for every program the checker with calls and creations
(`AssembleCut.checkCF`) accepts, under the named hypothesis `SitesRun` on the run.

Scope: the runtime code of one frame, as the other assembly theorems; the source side of CALL and
CREATE2 (a world answering them, `RunOracle.CallsAgree`) is not covered, so the composition with the
source's specification is stated at EVM IR (`holds_of_checkCF`), not at SolidCore.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateRunF

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallSeg
open SolidCore.Refinement.Solar.AssembleCreateSeg SolidCore.Refinement.Solar.AssembleCreateRun
open SolidCore.Refinement.Solar.AssembleCreateSegF
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## The tables of a run with creations -/

/-- The two tables of a run with creations. -/
structure Tabs where
  run : RunTable := {}
  cre : CreateTable := {}

/-- Tables that answer everything the shorter ones do, the same. -/
def Tabs.Le (a b : Tabs) : Prop := a.run.Le b.run ∧ a.cre.Le b.cre

theorem Tabs.Le.refl (a : Tabs) : a.Le a := ⟨RunTable.Le.refl _, CreateTable.Le.refl _⟩

theorem Tabs.Le.trans {a b c : Tabs} (h1 : a.Le b) (h2 : b.Le c) : a.Le c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- The frames a runner of messages returns. -/
def RunOut {bound : Nat} (runChild : MessageRunner .fusaka Nat bound) (caller : Evm .fusaka Nat)
    (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  ∃ lt ended, runChild caller m lt = .ok ended ∧ ended.val = child

/-- EthLib's runner of messages meets the assumption that names its frames. -/
theorem meets_runOut (bound : Nat) :
    Meets (bound := bound) (RunOut (processRunner .fusaka (Meter := Nat) bound))
      (processRunner .fusaka (Meter := Nat) bound) :=
  ⟨fun _ _ lt e h => ⟨lt, e, h, rfl⟩, (meets_static bound).aborts⟩

/-! ## Runs under a runner meeting an assumption that names it, over two tables -/

section BlocksF

variable {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
  (O : Tabs → Oracle)

/-- **One block of the simulation, read back from a run that succeeds**, as
`AssembleCall.AdvancesS` under every runner of messages meeting `P`, for the runs to a frame `fin`
that meet the hypothesis `Q`. -/
def AdvancesF (P : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Tabs → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : Tabs) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets (P bound runChild) runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none → Q bound runChild fin →
      ∃ T' r, Tabs.Le T T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

/-- A run of EthLib that ends with no error and meets the hypothesis is SolarTV's, for every table
extending the last one the run grew. -/
theorem run_of_advancesF {P : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop}
    {Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop}
    {E : Tabs → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → AdvancesF blk O P Q E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets (P bound runChild) runChild) :
    ∀ (n : Nat) (T : Tabs) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none → Q bound runChild fin →
      ∃ T' res, Tabs.Le T T' ∧
        (∀ T'', T'.Le T'' → ∃ k, SolarTV.Machine.iterate (blk (O T'')) k x = some res) ∧
        Post res fin
  | 0, _, _, _, _, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, T, x, evm, within, fin, hE, hm, hrun, hok, hq => by
    obtain ⟨T', r, hle, hstep, hinl, hinr⟩ :=
      adv T x evm hE bound runChild meets within fin hrun hok hq
    cases r with
    | inl res =>
      exact ⟨T', res, hle, fun T'' h => ⟨1, by simp [SolarTV.Machine.iterate, hstep T'' h]⟩,
        hinl res rfl⟩
    | inr y =>
      obtain ⟨after, within', hE', hm', hrun'⟩ := hinr y rfl
      obtain ⟨T2, res, hle2, hit, hpost⟩ :=
        run_of_advancesF adv meets n T' y after within' fin hE' (by omega) hrun' hok hq
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [SolarTV.Machine.iterate, hstep T'' (hle2.trans h), hk]⟩

end BlocksF

section Runs

open EthLib.Execution.State

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at the given gas, run by run, from a block simulation**: when every frame
related to a block state (`E`, from the substate the frame started with) advances (`Advances`) to
an end SolarTV's halt shows (`PostL`) or to the next block, and the frame a call starts with is
related to SolarTV's initial state, then the oracle of the run's table makes every result of the
bytecode on the call the EVM IR's or a failure that changes nothing. -/
theorem within_of_advancesF {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : Tabs → Oracle) (P : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Substate → Tabs → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (hP : Meets (P _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas)) (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas))
    (hQ : ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
        (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
      Q _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas) r.1)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesF (fun o => block o call p) O P Q (E ss0)
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
    AssembleRun.processMessage_ok' (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  have R := AssembleLoop.rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advancesF (fun o => block o call p) O (adv ss')
    hP _ {} _ _ within evm (start st' ss' R) (Nat.lt_succ_self _) hrf hok (hQ _ hpm hok)
  obtain ⟨k, hk⟩ := hit T (Tabs.Le.refl T)
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


end Runs

/-! ## The checker with calls and creations -/

theorem globC_of_checkCF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkCF p code c mx = true) :
    GlobC p c mx code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 := by
  simp only [checkCF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, htop⟩, hsize⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨⟨hmod, htop, hsize, fun t ht htgt => ?_⟩, fun t ht => ?_⟩, hseg, hneed⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (c.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p c t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p c ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksOkC_get p.blocks 0 hblocks t ht
    simpa using this

/-- The relation at a block entry, with the run's tables in step with its world. -/
def EntF (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray)
    (msg : Message .fusaka) (ss0 : Substate) (T : Tabs) (x : Nat × List Word × State)
    (evm : Evm .fusaka Nat) : Prop :=
  EntC p c mx code msg ss0 x evm ∧ TabF T.run T.cre x.2.2.world ∧
    memoryGasCost evm.memory.size + evm.gas ≤ msg.gas

/-- **A block of code with loops, GAS, CALLs, CREATE2s and CODECOPYs, read back from a run that
succeeds**, under every runner meeting `P` for the runs meeting `SitesOk`. -/
theorem advances_checkCF {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobC p c mx code) (hcr : c.creates = true) {call : Call} {msg : Message .fusaka}
    {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (P : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Message .fusaka →
      Evm .fusaka Nat → Prop)
    (T0 : Tabs) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntF p c mx code msg ss0 T0 x evm) :
    AdvancesF (fun o => SolarTV.EVM.Program.block o call p) (fun T => FO code T.run T.cre) P
      (fun bound runChild fin => SitesOk code msg (P bound runChild) bound runChild fin)
      (EntF p c mx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p c e.gas y.1) T0 x evm := by
  intro bound runChild meets within fin hrun hok hsites
  obtain ⟨b, S, s⟩ := x
  obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTab, hbud⟩ := hE
  simp only at hle hneed hR hseg hmem R hTab
  by_cases hb : b < p.blocks.length
  · obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
    obtain ⟨hn, hm⟩ := hneed hb
    have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
    rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at hseg
    obtain ⟨pc1, m1, within1, hat1, hseg1, hg1, hrun1⟩ : ∃ (pc1 : Nat) (m1 : Evm .fusaka Nat)
        (within1 : GasMeter.gasHeld m1.gas ≤ bound),
        At code msg pc1 Tw M m1.gas st ss rd m1 ∧
        Seg (bytesOf code) c.offset pc1 (lowerInstrs p c b p.blocks[b] ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size ∧
        m1.gas + (if isTarget p c b then 1 else 0) ≤ evm.gas ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m1 within1 = .ok fin := by
      by_cases ht : isTarget p c b = true
      · simp only [ht, ite_true, List.singleton_append, List.cons_append] at hseg
        obtain ⟨next, hd, hseg'⟩ := hseg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hp := hat.addGas 1
        obtain ⟨e1, r1, he1⟩ := Logic.jumpdestG hlt hcode (show 1 ≤ evm.gas + 1 by omega) _ hp
        obtain ⟨m, within', hz, hrm⟩ := reaches_low r1 1 evm rfl within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hgm⟩ := at_of_addGasR he1
        exact ⟨pc + 1, m, within', hatm, hseg', by simp only [ht, ite_true]; omega, hrm⟩
      · simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at hseg
        exact ⟨pc, evm, within, hat, hseg, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          hrun⟩
    obtain ⟨T', A', r, hle', hA', hex, hpost, hnext⟩ := segF (G0 := msg.gas) G.toGlobT hcr hdata
      hvalue hstatic hself hcaller hbenv htx hb hok hgas hdepth meets hsites
      (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss rd T0.run T0.cre m1 within1
      (Nat.lt_succ_self _) hblock hn (by omega) List.nil_prefix hR hseg1 (by omega) htop hmem R hat1
      hTab (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨⟨T', A'⟩, r, ⟨hle', hA'⟩, fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T''.run T''.cre h.1 h.2]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj⟩, after, within', hE', hT', hga, hbud', hra⟩ := hnext _ hy
      refine ⟨after, within', ⟨hE', hT', hbud'⟩, ?_, hra⟩
      have := meas_step (c := c) (g := evm.gas) (g' := after.gas) hb htle (by omega) hj
      dsimp only at this ⊢
      omega
  · obtain rfl : b = p.blocks.length := by omega
    have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
    have hbl : ∀ o, SolarTV.EVM.Program.block o call p (p.blocks.length, S, s) =
        some (.inl (.stop, s)) := by
      intro o
      simp only [SolarTV.EVM.Program.block, hblk, ite_true]
    refine ⟨T0, _, Tabs.Le.refl T0, fun _ _ => hbl _, ?_, ?_⟩
    · intro res hres
      cases hres
      have hseg' := hseg
      rw [lowerFrom_nil p c (by omega)] at hseg'
      have hpc := hseg'.nil_end
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy

/-- **Named hypothesis on a run of the bytecode with calls and creations**: the run of the call, when
it succeeds, meets `SitesOk` for the frames EthLib's runner returns (`RunOut`): at each CALL and
CREATE2, the frames the runner returns for its message from the caller state it makes keep the
frame's account, add no log when they succeed and have outputs below `2 ^ 256` bytes, and a CALL
with value calls code that is no EIP-7702 delegation. -/
def SitesRun (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
    SitesOk code (Final.Target.messageWith gas code call)
      (RunOut (processRunner .fusaka (Meter := Nat) gas)) gas (processRunner .fusaka (Meter := Nat) gas)
      r.1

/-- **EVM IR to bytecode, run by run, for code with loops, GAS, memory at any offset, CALLs,
CREATE2s and CODECOPYs**: for every program the checker with calls and creations accepts, at every
gas below `2 ^ 256` and every call whose run meets `SitesRun`, the oracle of the run's two tables makes
every result of the bytecode the EVM IR's or a failure that changes nothing. -/
theorem runs_of_checkCF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCF p code c mx = true) (hcr : c.creates = true) (gas : Nat) (hgas : gas < 2 ^ 256)
    (call : Call) (hQ : SitesRun gas code call) :
    ∃ T : Tabs, Within (evmirSem (FO code T.run T.cre)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨G, hseg, hneed0⟩ := globC_of_checkCF hc
  refine within_of_advancesF (fun T => FO code T.run T.cre) (fun _ runChild => RunOut runChild)
    (fun bound runChild fin => SitesOk code (Final.Target.messageWith gas code call) (RunOut runChild)
      bound runChild fin)
    (fun ss0 => EntF p c mx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p c e.gas y.1) (meets_runOut _) hQ (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkCF G hcr rfl
      (by simp [Final.Target.messageWith, SolidCore.Refinement.Target.message]) rfl rfl rfl rfl rfl
      hgas (by show 0 + 1 ≤ 1024; decide) (fun _ runChild => RunOut runChild) T x evm hE)
  refine ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hneed0], by simp⟩,
    SR.nil c _, by rw [List.drop_zero]; exact hseg, by simp, memRel_initial, R, ?_⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRunF.runs_of_checkCF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runs_of_checkCF

/-- The per-run theorem below `2 ^ 256` gas for every program the checker with calls and creations
accepts, on the calls in scope whose runs meet `SitesRun`: the oracle meets the certificate. -/
theorem withinRun_of_checkCF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCF p code c mx = true) (hcr : c.creates = true) (scope : Call → Prop)
    (hQ : ∀ gas call, scope call → SitesRun gas code call) :
    WithinRunLt evmirSem (fun _ => p) code scope (CertOk c) := by
  intro gas hgas call hs
  obtain ⟨T, hT⟩ := runs_of_checkCF hc hcr gas hgas call (hQ gas call hs)
  exact ⟨FO code T.run T.cre, FO_ok c code T.run T.cre, hT⟩

/-- **The assembly premise for code with calls and creations**: below `2 ^ 256` gas, for every call
in scope whose run meets `SitesRun`, an oracle meeting the certificate under which the EVM IR gives
the bytecode's result or a failure that changes nothing. (No world answering its calls at the
source is given: the source side of CALL and CREATE2 is out of scope.) -/
theorem assembly_of_checkCF {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCF p code c mx = true) (hcr : c.creates = true) (scope : Call → Prop)
    (hQ : ∀ gas call, scope call → SitesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ o : Oracle, CertOk c o ∧
      Within (evmirSem o) (ethLibWith gas) p code (· = call) :=
  withinRun_of_checkCF hc hcr scope hQ

/-- **The first lowered MIR to the exact bytecode, run by run, for code with calls and creations**:
the backend stages read backwards and the checker with calls and creations. -/
theorem withinRun_mir_of_checkCF {stage0 : SolarTV.MIR.Lowered.moduleLayer.Prog}
    {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {S scope : Call → Prop}
    (back : ∀ o, Certified SolarTV.EVM.Program.layer SolarTV.MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call) (hc : checkCF p code c mx = true) (hcr : c.creates = true)
    (hQ : ∀ gas call, scope call → SitesRun gas code call) :
    WithinRunLt mirSem (fun _ => stage0) code scope (CertOk c) :=
  WithinRunLt.of_back (fun o _ => fun call hcall obs h =>
      stage_of_certified (back o) call (hS call hcall) obs h)
    (withinRun_of_checkCF hc hcr scope hQ)

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRunF.withinRun_mir_of_checkCF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_mir_of_checkCF

/-- **A specification at EVM IR to the exact bytecode, for code with calls and creations**: a
specification of the EVM IR under every oracle meeting the certificate, the checker and `SitesRun`
on the calls in scope give the specification of the bytecode at every gas below `2 ^ 256`. -/
theorem holds_of_checkCF {St : Type} {p : Assemble.Program} {code : ByteArray} {c : Cert}
    {mx : List Nat} {spec : Final.ContractSpec St}
    (evmir : ∀ o, CertOk c o → Final.Holds (evmirSem o) p spec)
    (hc : checkCF p code c mx = true) (hcr : c.creates = true)
    (hQ : ∀ gas call, spec.Calls call → SitesRun gas code call)
    (gas : Nat) (hgas : gas < 2 ^ 256) : Final.Holds (Final.ethLibWith gas) code spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hcall : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  obtain ⟨o, ho, hwithin⟩ := assembly_of_checkCF hc hcr spec.Calls hQ gas hgas _ hcall
  rcases hwithin _ rfl obs hrun with h | ⟨hs, hst, hl⟩
  · exact evmir o ho f hf args ht v hv σ hinv hreq obs h
  · exact ⟨fun h'' => absurd (hs.symm.trans h'') (by decide), fun _ => ⟨hst, hl⟩⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRunF.holds_of_checkCF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_checkCF

/-! ## The example: CODECOPY, CREATE2 and CALL with value, run by run -/

/-- **The example's bytecode, run by run**: at every gas below `2 ^ 256` and every call whose run meets
`SitesRun`, every result of `AssembleCreateExample.code` (CODECOPY of its init code, CREATE2 with salt
`0x2a`, CALL with value 1 to the created address) is the EVM IR program's under the oracle of the
run's tables, or a failure that changes nothing. -/
theorem example_runs (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call)
    (hQ : SitesRun gas AssembleCreateExample.code call) :
    ∃ T : Tabs, Within (evmirSem (FO AssembleCreateExample.code T.run T.cre)) (ethLibWith gas)
      AssembleCreateExample.prog AssembleCreateExample.code (· = call) :=
  runs_of_checkCF AssembleCreateExample.check_ok rfl gas hgas call hQ

/-- The same checker refuses the example's bytecode with another salt or value: the premise of
`runs_of_checkCF` fails for them. -/
theorem example_mutants :
    checkCF AssembleCreateExample.prog (AssembleCreateExample.codeOf 2 0x2b 1)
        AssembleCreateExample.cert AssembleCreateExample.maxs = false ∧
      checkCF AssembleCreateExample.prog (AssembleCreateExample.codeOf 2 0x2a 2)
        AssembleCreateExample.cert AssembleCreateExample.maxs = false :=
  ⟨AssembleCreateExample.mutantSalt_fails, AssembleCreateExample.mutantValue_fails⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRunF.example_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms example_runs

end SolidCore.Refinement.Solar.AssembleCreateRunF

import SolidCore.Refinement.Solar.AssembleLoopWithin
import SolidCore.Refinement.Solar.AssembleGasLoop
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# The loop checker from any caller

`AssembleLoop.within_of_checkL` and `forward_of_checkL` (the loop checker's two bytecode edges:
partial correctness at every gas, and the forward run from the gas bound on) speak of
`Final.Target.runWith`, one message from `callerAddress`. Their proofs use the caller only through
`run_simL`'s `hcaller` and the message's pre-state. `exec_simL`, the block simulation under them,
already takes any account `a` (`OracleOkAt a`), as the checker with contexts does
(`AssembleCtxGas.forward_of_checkXLFrom`).

This file restates the two edges for every account `a` but the contract's, with
`Target.messageFromWith a` and `Target.preStateFrom a` (Verify/Final's `runWithFrom`). The proofs
are those of `run_simL`, `within_of_checkL` and `forward_of_checkL` with the caller generalised;
no premise is added. A program that reads the transaction's environment (`c.reads`) is covered
only where `Target.txEnvFrom a = Target.txEnv`, as in `forward_of_checkXLFrom`.
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex

/-- A failure of `runWithFrom` changes nothing. -/
theorem runWithFrom_failureL {a gas : Nat} {code : ByteArray} {call : Call} {obs : Observable}
    (h : Final.Target.runWithFrom a gas code call = some obs) (hf : obs.success = false) :
    obs.storage = slotValue call.storage ∧ obs.logs = [] := by
  unfold Final.Target.runWithFrom at h
  split at h
  · cases h
  · cases h
    simp only at hf
    simp [hf]

theorem rel_startFromL (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (code : ByteArray) (call : SolarTV.Call) (gas : Nat) {st' : State.TransactionState}
    (ss' : Substate)
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


open SolarTV.EVM.Program in
/-- `run_simL` for a message from any account `a`. -/
theorem run_simLFrom {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobL p c mx code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    {a : Nat} (hcaller : msg.caller = Target.address a) (ho : c.env = true → OracleOkAt a o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : c.reads = true → msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o) :
    ∀ (fuel b : Nat) (S T : List Word) (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray)
      (g : Nat) (st : State.TransactionState) (ss : Substate),
      b ≤ p.blocks.length → (b < p.blocks.length → c.need b ≤ S.length ∧ S.length ≤ maxH mx b) →
      SR c (c.entry b) S T →
      EntryL c code call (lowerFrom p c b (p.blocks.drop b)) (fuel * bmax c) pc s M g →
      Rel msg ss0 st ss s →
      (∀ r, SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = some r →
        SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 r.2 r.1)) ∧
      (SolarTV.Machine.iterate (block o call p) fuel (b, S, s) = none →
        Triple (StepG .fusaka) (At code msg pc T M g st ss .empty)
          (fun z => 2 * ((p.blocks.length + 2) * z.gas) + fuel ≤ meas p c g b))
  | 0, b, S, T, s, pc, M, g, st, ss, _, _, _, _, _ => by
    refine ⟨fun r hr => by simp [SolarTV.Machine.iterate] at hr, fun _ evm hp => ⟨evm, Reaches.refl _, ?_⟩⟩
    obtain ⟨-, -, -, -, -, -, hg, -⟩ := hp
    rw [hg]
    unfold meas
    omega
  | fuel + 1, b, S, T, s, pc, M, g, st, ss, hle, hneed, hR, E, R => by
    by_cases hb : b < p.blocks.length
    · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
      obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
      obtain ⟨hn, hm⟩ := hneed hb
      have hbm := budget_le_bmax c b
      have hfm : (fuel + 1) * bmax c = fuel * bmax c + bmax c := Nat.succ_mul _ _
      obtain ⟨pc1, g1, hlabel, hg1, I1⟩ : ∃ pc1 g1, HoareG .fusaka (At code msg pc T M g st ss .empty)
          (At code msg pc1 T M g1 st ss .empty) ∧ g1 + (if isTarget p c b then 1 else 0) ≤ g ∧
          InvL c code call (lowerInstrs p c b p.blocks[b] ++
            lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) (budget c b - labelItems p c b)
            (fuel * bmax c) pc1 S s M g1 := by
        have E' := E
        rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at E'
        have hG := E'.gas
        rw [hfm] at hG
        by_cases ht : isTarget p c b = true
        · have hl : labelItems p c b = 1 := by simp [labelItems, ht]
          rw [hl] at hL ⊢
          simp only [ht, ite_true, List.singleton_append] at E'
          obtain ⟨next, hd, hseg⟩ := E'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          exact ⟨pc + 1, g - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
            ⟨hseg, by omega, by omega, E'.le_top, E'.mem⟩⟩
        · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
          rw [hl, Nat.sub_zero]
          simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
          exact ⟨pc, g, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
            ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
      have hsim := exec_simL (o := o) G.toT hdata hvalue hstatic hself hcaller ho hbenv htx he b hb (fuel * bmax c)
        p.blocks[b] (c.need b) [] (c.entry b) S T _ s pc1 M g1 st ss hblock hn (by omega)
        (KR.nil _) hR I1 R
      simp only [SolarTV.Machine.iterate, block, hblk]
      generalize exec o call b p.blocks[b] S s = x at hsim
      rcases x with ⟨halt, s'⟩ | ⟨t, S', s'⟩
      · refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
        simp only [Option.some.injEq] at hr
        subst hr
        exact SpecG.seq hlabel hsim
      · obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', E', R'⟩ := hsim
        have IH := run_simLFrom G hdata hvalue hstatic hself hcaller ho hbenv htx he fuel t S' T' s' pc' M' g' st' ss'
          htle hneedt hR' E' R'
        refine ⟨fun r hr => SpecG.seq (Triple.seq hlabel hh) (IH.1 r hr), fun hr evm hp => ?_⟩
        obtain ⟨e1, r1, he1⟩ := hlabel evm hp
        obtain ⟨mid, r2, hmid⟩ := hh e1 he1
        obtain ⟨z, r3, hz⟩ := IH.2 hr mid hmid
        refine ⟨z, (r1.trans r2).trans r3, ?_⟩
        have hgm := reaches_gas_le r2
        rw [hmid.2.2.2.2.2.2.1, he1.2.2.2.2.2.2.1] at hgm
        have := meas_step (c := c) (g := g) (g' := g') hb htle (by omega) hj
        omega
    · obtain rfl : b = p.blocks.length := by omega
      have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
      simp only [SolarTV.Machine.iterate, block, hblk, ite_true]
      refine ⟨fun r hr => ?_, fun hr => by simp at hr⟩
      simp only [Option.some.injEq] at hr
      subst hr
      have hseg := E.seg
      rw [lowerFrom_nil p c (by omega)] at hseg
      have hpc := hseg.nil_end
      exact SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h


/-- **EVM IR to bytecode at every gas, for code with loops, from any account** `a` but the
contract's. -/
theorem within_of_checkLFrom {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOkAt a o)
    (he : c.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv)
    (call : SolarTV.Call) (gas : Nat) (obs : SolarTV.Observable)
    (hrun : Final.Target.runWithFrom a gas code call = some obs) :
    (SolarTV.evmirSem o).run p call = some obs ∨
      (obs.success = false ∧ obs.storage = slotValue call.storage ∧ obs.logs = []) := by
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  cases hs : obs.success
  · exact Or.inr ⟨rfl, runWithFrom_failureL hrun hs⟩
  left
  unfold Final.Target.runWithFrom at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hs
  obtain ⟨st', ss', runChild, within, hcases, hmove, hrf⟩ :=
    processMessage_ok (message := Target.messageFromWith a gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_messageFromWith a gas code call) hpm hok
  simp only at hrf
  -- The run, the reserve and the fuel.
  set msg := Target.messageFromWith a gas code call with hmsg
  have hcode : msg.code = code := rfl
  have hgas : msg.gas = gas := rfl
  have R := rel_startFromL a hAB code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  generalize hW : p.blocks.length + 2 = W
  generalize hn : 2 * (W * gas) + W + p.blocks.length + 1 = n
  generalize hK : 22100 * (n * bmax c) + memoryGasCost c.top = K
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty (gas + K) :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; omega, by simp, memRel_initial⟩
  have hsim := run_simLFrom (msg := msg) (ss0 := ss') (a := a) G rfl (by simp [msg, Target.messageFromWith])
    rfl rfl rfl ho rfl (fun h => (he h).2) (fun h => (he h).1) n 0 [] [] _ 0 .empty (gas + K) st' ss' (Nat.zero_le _)
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


/-- **The forward assembly theorem for code with loops, from any account** `a` but the
contract's: from `gasBoundL c n` gas on, EthLib runs the bytecode from `a` to the EVM IR's result. -/
theorem forward_of_checkLFrom {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOkAt a o)
    (he : c.reads = true → EnvOk o ∧ Target.txEnvFrom a = Target.txEnv) (call : SolarTV.Call) (n : Nat)
    (r : SolarTV.Machine.Halt × SolarTV.Machine.State)
    (hit : SolarTV.Machine.iterate (SolarTV.EVM.Program.block o call p) n
      (0, [], SolarTV.Machine.State.initial call) = some r)
    {gas : Nat} (hg : gasBoundL c n ≤ gas) :
    Final.Target.runWithFrom a gas code call = some (SolarTV.Machine.observe call r.2 r.1) := by
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  have hm0 : memoryGasCost (ByteArray.empty).size = 0 := by decide
  refine Assemble.run_of_rel_withFrom a gas hAB code call r.2 r.1 fun st R => ?_
  have E0 : EntryL c code call (lowerFrom p c 0 (p.blocks.drop 0)) (n * bmax c) 0
      (SolarTV.Machine.State.initial call) .empty gas :=
    ⟨by rw [List.drop_zero]; exact hseg, by rw [hm0]; unfold gasBoundL at hg; omega, by simp,
      memRel_initial⟩
  have hsim := run_simLFrom (msg := Target.messageFromWith a gas code call) (ss0 := Substate.empty)
    (a := a) G rfl (by simp [Target.messageFromWith]) rfl rfl rfl ho rfl (fun h => (he h).2)
    (fun h => (he h).1) n 0 [] [] _ 0 .empty gas st Substate.empty (Nat.zero_le _)
    (fun _ => ⟨by simp [hneed0], by simp⟩) (SR.nil c _) E0 R
  exact SpecG.toSpec (hsim.1 r hit)

/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.within_of_checkLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_checkLFrom

/-- info: 'SolidCore.Refinement.Solar.AssembleLoop.forward_of_checkLFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_of_checkLFrom

end SolidCore.Refinement.Solar.AssembleLoop

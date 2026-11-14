import SolidCore.Refinement.Solar.AssembleCtx
import SolidCore.Refinement.Solar.AssembleCallSeg
import SolidCore.Refinement.Solar.AssembleFast

/-!
# The checker with contexts, for code with STATICCALLs

\`AssembleCtx.checkX\` without its no-call gate (\`checkXB\`): each block checked once per context by
\`AssembleCut.blockOkC\` under the context's certificate, which may make STATICCALLs, and run against
the bytecode by \`AssembleCallSeg.segS\` (the runner of messages under \`StaticOkE\`, the calls' flags
and outputs in the run's table). \`assembly_of_checkXB\` is \`AssembleCallSeg.assembly_of_checkCB\`'s
statement, with the same named hypotheses (\`StaticRunner\`, \`CalleesRun\`), for every program the
checker with contexts accepts.
-/

namespace SolidCore.Refinement.Solar.AssembleCtx

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallWorld
open SolidCore.Refinement.Solar.AssembleCallCut SolidCore.Refinement.Solar.AssembleDyn
open SolidCore.Refinement.Solar.AssembleCallSeg
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- **The checker with contexts**, for programs that may make STATICCALLs: \`checkX\` without its
no-call gate. -/
def checkXB (p : Assemble.Program) (code : ByteArray) (cx : CtxCert) : Bool :=
  (walk (bytesOf code) cx.base.offset 0 (lower p cx.base)).isSome && labelsValid p cx.base code &&
    decide (cx.base.top % 32 = 0) && decide (cx.base.top ≤ 2 ^ 200) && decide (code.size < 2 ^ 32) &&
    decide (0 < cx.count 0) && decide ((cx.at 0 0).need = 0) && !cx.base.creates && blocksX p cx 0 p.blocks

/-- The facts of the checker with contexts and calls. -/
structure GlobXB (p : Assemble.Program) (cx : CtxCert) (code : ByteArray) : Prop where
  glob : GlobT p cx.base code
  block : ∀ b (hb : b < p.blocks.length) j, j < cx.count b → ctxOk p cx b j p.blocks[b] = true
  creates : cx.base.creates = false

theorem globXB_of_checkXB {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (h : checkXB p code cx = true) :
    GlobXB p cx code ∧ Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size ∧
      0 < cx.count 0 ∧ (cx.at 0 0).need = 0 := by
  simp only [checkXB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hlabels⟩, hmod⟩, htop⟩, hsize⟩, hcount⟩, hneed⟩, hcre⟩, hblocks⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) cx.base.offset 0 (lower p cx.base) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨⟨hmod, htop, hsize, fun t ht htgt => ?_⟩, fun b hb j hj => ?_, by simpa using hcre⟩, hseg, hcount, hneed⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (cx.base.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p cx.base t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p cx.base ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksX_get p.blocks 0 hblocks b hb j (by simpa using hj)
    simpa using this

/-- The relation at a block entry of code with calls: \`AssembleCallSeg.EntS\` under a certificate of
the layout, at one of the block's contexts. -/
def EntXS (codes : SolidCore.Solidity.Shared.Account.BytesMap) (p : Assemble.Program) (cx : CtxCert)
    (code : ByteArray) (msg : Message .fusaka) (ss0 : Substate) (T : RunTable)
    (x : Nat × List Word × State) (evm : Evm .fusaka Nat) : Prop :=
  ∃ (c : Cert) (mx : List Nat), Same c cx.base ∧ EntS codes p c mx code msg ss0 T x evm ∧
    (x.1 < p.blocks.length → ∃ j, j < cx.count x.1 ∧ c.need x.1 = (cx.at x.1 j).need ∧
      maxH mx x.1 = (cx.at x.1 j).max ∧ c.entry x.1 = (cx.at x.1 j).types ∧
      LabOk (cx.at x.1 j).labs x.2.1)

theorem entS_congr {codes : SolidCore.Solidity.Shared.Account.BytesMap} {p : Assemble.Program}
    {code : ByteArray} {msg : Message .fusaka} {ss0 : Substate}
    {T : RunTable} {c1 c2 : Cert} {mx1 mx2 : List Nat} (h : Same c1 c2) {x : Nat × List Word × State}
    {evm : Evm .fusaka Nat}
    (hn : x.1 < p.blocks.length → c1.need x.1 = c2.need x.1 ∧ maxH mx1 x.1 = maxH mx2 x.1)
    (he : c1.entry x.1 = c2.entry x.1)
    (hl : ∀ i (hi : i < x.2.1.length), tyAt (c1.entry x.1) i = some true → x.2.1[i].toNat ∈ c2.rets)
    (hE : EntS codes p c1 mx1 code msg ss0 T x evm) :
    EntS codes p c2 mx2 code msg ss0 T x evm :=
  ⟨entC_congr h hn he hl hE.1, hE.2⟩

/-- **A block of code with loops, GAS and STATICCALLs, in one of its contexts, read back from a run
that succeeds.** -/
theorem advances_checkXS {p : Assemble.Program} {cx : CtxCert} {code : ByteArray}
    (G : GlobXB p cx code) (codes : SolidCore.Solidity.Shared.Account.BytesMap) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntXS codes p cx code msg ss0 T0 x evm) :
    AdvancesQ (fun o => SolarTV.EVM.Program.block o call p) (OS codes) StaticOkE
      (CalleesOk code msg StaticOkE) (EntXS codes p cx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p cx.base e.gas y.1) T0 x evm := by
  intro bound runChild meets within fin hrun hok hcal
  obtain ⟨b, S, s⟩ := x
  obtain ⟨c0, mx0, hsame0, hE0, hctx⟩ := hE
  by_cases hb : b < p.blocks.length
  · obtain ⟨j, hj, hn0, hm0, he0, hlab⟩ := hctx hb
    have hbn : b < p.blocks.length + 1 := by omega
    obtain ⟨c, hc⟩ : ∃ c, c = certAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
    obtain ⟨mx, hmx⟩ : ∃ mx, mx = maxsAt cx (p.blocks.length + 1) b j := ⟨_, rfl⟩
    have hsame : Same c cx.base := hc ▸ certAt_same cx _ b j
    have hcb : c.need b = (cx.at b j).need := by
      rw [hc, certAt_need hbn, pick_of_exit (exitCtx_self cx b j)]
    have hmb : maxH mx b = (cx.at b j).max := by
      rw [hmx, maxsAt_max hbn, pick_of_exit (exitCtx_self cx b j)]
    have heb : c.entry b = (cx.at b j).types := by
      rw [hc, certAt_entry hbn, pick_of_exit (exitCtx_self cx b j)]
    have hck := G.block b hb j hj
    simp only [ctxOk, Bool.and_eq_true] at hck
    obtain ⟨⟨hblk0, hexOk⟩, hcov⟩ := hck
    have hcr : c.rets = (cx.at b j).rets := by rw [hc]; rfl
    have hE' : EntS codes p c mx code msg ss0 T0 (b, S, s) evm :=
      entS_congr (c1 := c0) (mx1 := mx0) ⟨hsame0.1.trans hsame.1.symm, hsame0.2.1.trans hsame.2.1.symm,
        hsame0.2.2.trans hsame.2.2.symm⟩
        (fun _ => ⟨hn0.trans hcb.symm, hm0.trans hmb.symm⟩) (he0.trans heb.symm)
        (by rw [he0, hcr]; exact labsCover_mem hcov hlab) hE0
    have hGc : GlobT p c code := globT_congr ⟨hsame.1.symm, hsame.2.1.symm, hsame.2.2.symm⟩ G.glob
    rw [← hc, ← hmx] at hblk0
    simp only [blockCtxOk, Bool.and_eq_true, decide_eq_true_eq] at hblk0
    obtain ⟨⟨⟨hL, hnm⟩, hstk⟩, hblock⟩ := hblk0
    cases hexE : exits b (cx.at b j).labs p.blocks[b] with
    | none => rw [hexE] at hexOk; simp [exitsOk] at hexOk
    | some Ex =>
    rw [hexE] at hexOk
    obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hrdr, hbud⟩ := hE'
    simp only at hle hneed hR hseg hmem R hTg hs0 hrdr
    obtain ⟨hn, hm⟩ := hneed hb
    have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
    rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at hseg
    -- The label, at the frame's gas.
    obtain ⟨pc1, m1, within1, hat1, hseg1, hg1, hrun1⟩ : ∃ (pc1 : Nat) (m1 : Evm .fusaka Nat)
        (within1 : GasMeter.gasHeld m1.gas ≤ bound),
        At code msg pc1 Tw M m1.gas st ss rd m1 ∧
        Seg (bytesOf code) c.offset pc1 (lowerInstrs p c b p.blocks[b] ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size ∧
        m1.gas + (if isTarget p c b then 1 else 0) ≤ evm.gas ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m1 within1 = .ok fin := by
      by_cases ht : isTarget p c b = true
      · simp only [ht, ite_true, List.cons_append] at hseg
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
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := segS (G0 := msg.gas) hGc codes (hc ▸ G.creates) hdata hvalue hstatic
      hself hcaller hbenv htx hb hok hgas hdepth meets (fun _ _ _ h => h.1) hcal (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss rd T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) List.nil_prefix hR hseg1 (by omega) htop hmem R hat1 hTg hs0
      (by rw [← hat.2.2.2.2.2.2.2.2.2.2.2.2]; exact hrdr)
      (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨T', r, hle', fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T'' h]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj'⟩, after, within', hE', hT', hs', hrdy', hga, hbud', hra⟩ := hnext _ hy
      have hr := hex T' (RunTable.Le.refl T')
      rw [hy] at hr
      obtain ⟨L', hmemE, hL'⟩ := exits_sound (OS codes T') call b p.blocks[b] _ S s Ex _ hlab hexE hr
      refine ⟨after, within', ⟨c, mx, hsame, ⟨hE', hT', hs', hrdy', hbud'⟩, fun ht => ?_⟩, ?_, hra⟩
      · obtain ⟨j', hx, hj'c, hlabs⟩ := exitsOk_mem hexOk hmemE ht
        have htn : t < p.blocks.length + 1 := by omega
        have hpk := pick_of_exit hx
        refine ⟨j', hj'c, ?_, ?_, ?_, hL'.le hlabs⟩
        · rw [hc, certAt_need htn, hpk]
        · rw [hmx, maxsAt_max htn, hpk]
        · rw [hc, certAt_entry htn, hpk]
      · have := meas_step (c := c) (g := evm.gas) (g' := after.gas) hb htle (by omega) hj'
        rw [meas_congr hsame.2.1, meas_congr hsame.2.1] at this
        dsimp only at this ⊢
        omega
  · obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hrdr, hbud⟩ := hE0
    simp only at hle hseg R
    obtain rfl : b = p.blocks.length := by omega
    have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
    have hbl : ∀ o, SolarTV.EVM.Program.block o call p (p.blocks.length, S, s) =
        some (.inl (.stop, s)) := by
      intro o
      simp only [SolarTV.EVM.Program.block, hblk, ite_true]
    refine ⟨T0, _, RunTable.Le.refl T0, fun _ _ => hbl _, ?_, ?_⟩
    · intro res hres
      cases hres
      have hseg' := hseg
      rw [lowerFrom_nil p c0 (by omega)] at hseg'
      have hpc := hseg'.nil_end
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy

/-- **EVM IR to bytecode, run by run, for code with loops, GAS, memory at any offset, STATICCALLs to
code and internal functions called in several contexts**: \`AssembleCallSeg.runs_of_checkCB\` for
every program the checker with contexts accepts. -/
theorem runs_of_checkXB {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) (hP : StaticRunner gas)
    (hQ : CalleesRun gas code call) :
    ∃ T, Within (evmirSem (OS codes T)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨G, hseg, hcount, hneed0⟩ := globXB_of_checkXB hc
  refine within_of_advancesQ (OS codes) StaticOkE
    (CalleesOk code (Final.Target.messageWith gas code call) StaticOkE)
    (fun ss0 => EntXS codes p cx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p cx.base e.gas y.1) (staticOkE_of gas hP) hQ (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkXS G codes rfl
      (by simp [Final.Target.messageWith, SolidCore.Refinement.Target.message]) rfl rfl rfl rfl rfl
      hgas (by show 0 + 1 ≤ 1024; decide) T x evm hE)
  have h0n : 0 < p.blocks.length + 1 := by omega
  have hsame := certAt_same cx (p.blocks.length + 1) 0 0
  have hn0 : (certAt cx (p.blocks.length + 1) 0 0).need 0 = (cx.at 0 0).need := by
    rw [certAt_need h0n, pick_of_exit (exitCtx_self cx 0 0)]
  have hseg0 : Seg (bytesOf code) (certAt cx (p.blocks.length + 1) 0 0).offset 0
      (lowerFrom p (certAt cx (p.blocks.length + 1) 0 0) 0 (p.blocks.drop 0)) code.size := by
    rw [hsame.offset, lowerFrom_congr hsame.2.1, List.drop_zero]
    exact hseg
  refine ⟨certAt cx (p.blocks.length + 1) 0 0, maxsAt cx (p.blocks.length + 1) 0 0, hsame,
    ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hn0, hneed0], by simp⟩,
    SR.nil _ _, hseg0, by simp, memRel_initial, R, ?_⟩, rfl, ⟨rfl, rfl, rfl⟩,
    fun T'' _ => rdRel_nil codes T'', ?_⟩, fun _ => ⟨0, hcount,
    hn0, by rw [maxsAt_max h0n, pick_of_exit (exitCtx_self cx 0 0)],
    by rw [certAt_entry h0n, pick_of_exit (exitCtx_self cx 0 0)], LabOk.empty _⟩⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- **The assembly premise of \`holds_of_runs\` for code with STATICCALLs and internal functions
called in several contexts**: \`AssembleCallSeg.assembly_of_checkCB\`'s statement, with its named
hypotheses, for every program the checker with contexts accepts. -/
theorem assembly_of_checkXB {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB p code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hP : ∀ gas, StaticRunner gas)
    (hQ : ∀ gas call, scope call → CalleesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk cx.base o ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hs
  obtain ⟨T, hT⟩ := runs_of_checkXB hc codes gas hgas call (hP gas) (hQ gas call hs)
  exact ⟨OS codes T, tabWorld T.oks T.outs codes, (OS_agree codes T).1, (OS_agree codes T).2,
    OS_ok codes cx.base T, hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkXB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkXB

/-! ## RETURNDATASIZE as a stack operation

solar's export writes RETURNDATASIZE as the stack operation \`.op (.stack .returndatasize)\`, which
SolarTV runs as the effect \`.effect .returndatasize 0\` does (both push the oracle's return data
size and fail on the same stacks), and which the checkers lower only in its effect form. \`norm\`
writes the program with every such operation as the effect; it runs as the program does
(\`sem_norm\`), so the checker's theorem for \`norm p\` is one for \`p\`. -/

/-- An instruction with RETURNDATASIZE in its effect form. -/
def normI : SolarTV.EVM.Program.Instr → SolarTV.EVM.Program.Instr
  | .op (.stack .returndatasize) => .effect .returndatasize 0
  | i => i

/-- The program with RETURNDATASIZE in its effect form. -/
def norm (p : Assemble.Program) : Assemble.Program := ⟨p.blocks.map (·.map normI)⟩

theorem normI_of_ne {i : SolarTV.EVM.Program.Instr} (h : i ≠ .op (.stack .returndatasize)) :
    normI i = i := by
  unfold normI; split
  · exact absurd rfl h
  · rfl

open SolarTV.EVM.Program in
theorem exec_norm (o : Oracle) (call : Call) (b : Nat) :
    ∀ (is : List SolarTV.EVM.Program.Instr) (S : List Word) (s : State),
      exec o call b (is.map normI) S s = exec o call b is S s
  | [], _, _ => rfl
  | i :: rest, S, s => by
    have ih := exec_norm o call b rest
    by_cases hi : i = .op (.stack .returndatasize)
    · subst hi
      simp only [List.map_cons, normI]
      by_cases h1 : S.length + 1 > 1024
      · have h2 : ¬ S.length < 0 := by omega
        simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Effect.apply, h1, Except.map]
      · simp [exec, stepOp, SolarTV.EVM.stepChecked, SolarTV.EVM.step, Effect.apply, Except.map,
          show ¬ 1024 < S.length by omega, show ¬ 1024 < S.length + 1 by omega, ih, context]
    · rw [List.map_cons, normI_of_ne hi]
      cases i <;> simp only [exec, ih]

theorem run_norm (o : Oracle) (p : Assemble.Program) :
    SolarTV.EVM.Program.run o (norm p) = SolarTV.EVM.Program.run o p := by
  have hb : ∀ call, SolarTV.EVM.Program.block o call (norm p) = SolarTV.EVM.Program.block o call p := by
    intro call
    funext x
    obtain ⟨b, S, s⟩ := x
    simp only [SolarTV.EVM.Program.block, norm, List.getElem?_map, List.length_map]
    cases p.blocks[b]? with
    | none => rfl
    | some instrs => simp only [Option.map_some, exec_norm]
  funext call fuel
  simp only [SolarTV.EVM.Program.run]
  rw [hb call]

theorem sem_norm (o : Oracle) (p : Assemble.Program) (call : Call) :
    (evmirSem o).run (norm p) call = (evmirSem o).run p call := by
  have h : SolarTV.EVM.Program.layer.run o (norm p) = SolarTV.EVM.Program.layer.run o p :=
    run_norm o p
  have hE : ∀ r, SolarTV.EVM.Program.layer.Ends o (norm p) call r ↔
      SolarTV.EVM.Program.layer.Ends o p call r := by
    intro r; simp only [Layer.Ends, h]
  have hres : SolarTV.EVM.Program.layer.result o (norm p) call =
      SolarTV.EVM.Program.layer.result o p call := by
    by_cases hq : ∃ r, SolarTV.EVM.Program.layer.Ends o p call r
    · obtain ⟨r, hr⟩ := hq
      rw [SolarTV.EVM.Program.layer.result_of_ends hr,
        SolarTV.EVM.Program.layer.result_of_ends ((hE r).2 hr)]
    · have hq' : ¬ ∃ r, SolarTV.EVM.Program.layer.Ends o (norm p) call r :=
        fun ⟨r, hr⟩ => hq ⟨r, (hE r).1 hr⟩
      simp only [Layer.result, hq, hq', dite_false]
  simp only [evmirSem, SolarTV.EVM.Program.sem, Layer.sem, hres]

theorem within_norm {o : Oracle} {T : Sem} {p : Assemble.Program} {code : T.Prog}
    {scope : Call → Prop} (h : Within (evmirSem o) T (norm p) code scope) :
    Within (evmirSem o) T p code scope := by
  intro call hc obs hrun
  rw [← sem_norm o p call]
  exact h call hc obs hrun

/-! ## The check, block by block -/

theorem all_range_of {n : Nat} {f : Nat → Bool} (h : ∀ j, j < n → f j = true) :
    (List.range n).all f = true := by
  simp only [List.all_eq_true, List.mem_range]
  exact h

theorem blocksX_of_forall {p : Assemble.Program} {cx : CtxCert} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat),
      (∀ k (_ : k < l.length), (List.range (cx.count (b + k))).all
        (fun j => ctxOk p cx (b + k) j (l.getD k [])) = true) → blocksX p cx b l = true
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [blocksX, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), blocksX_of_forall l (b + 1) fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    rw [show b + (k + 1) = b + 1 + k by omega] at this
    simpa using this

/-- \`checkXB\` from its parts, each its own evaluation: the walk of the code, the layout's bounds
and each block in each of its contexts. -/
theorem checkXB_of_parts {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hw : (walk (bytesOf code) cx.base.offset 0 (lower p cx.base)).isSome = true)
    (hrest : (decide (cx.base.top % 32 = 0) && decide (cx.base.top ≤ 2 ^ 200) &&
      decide (code.size < 2 ^ 32) && decide (0 < cx.count 0) && decide ((cx.at 0 0).need = 0)) = true)
    (hb : ∀ k (_ : k < p.blocks.length), (List.range (cx.count k)).all
      (fun j => ctxOk p cx k j (p.blocks.getD k [])) = true)
    (hcre : cx.base.creates = false := by decide) :
    checkXB p code cx = true := by
  have hl := SolidCore.Refinement.Solar.Assemble.labelsValid_of_walk hw
  have hbx := blocksX_of_forall (cx := cx) p.blocks 0 (fun k hk => by simpa using hb k hk)
  simp only [Bool.and_eq_true] at hrest
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hrest
  simp only [checkXB, hw, hl, h1, h2, h3, h4, h5, hcre, hbx, Bool.and_self, Bool.not_false]

/-- **The assembly premise for an exported program with RETURNDATASIZE as a stack operation**:
\`assembly_of_checkXB\` for the program the checker accepts in its effect form. -/
theorem assembly_of_checkXB_norm {p : Assemble.Program} {code : ByteArray} {cx : CtxCert}
    (hc : checkXB (norm p) code cx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hP : ∀ gas, StaticRunner gas)
    (hQ : ∀ gas call, scope call → CalleesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk cx.base o ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hs
  obtain ⟨o, W, hW, hA, hok, hwi⟩ := assembly_of_checkXB hc codes scope hP hQ gas hgas call hs
  exact ⟨o, W, hW, hA, hok, within_norm hwi⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCtx.assembly_of_checkXB_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkXB_norm

end SolidCore.Refinement.Solar.AssembleCtx

import SolidCore.Refinement.Solar.AssembleRun
import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# The loop assembly theorem at the run's gas

`AssembleRun.within_of_advances` instantiated for the checker of code with loops: each block is read
back from a run that succeeds (`advances_checkL`) by the block simulation of `AssembleLoopSim`, run
with gas to spare for that block alone (`K` more than the frame holds) and moved back to the frame's
own gas by `Logic.reaches_low`, block by block rather than for the whole run. The relation at a block
entry (`Ent`) holds at any gas, so no gas reserve crosses blocks.

`withinRun_of_checkL_atGas` is `RunOracle.withinRun_of_checkL` proved this way: the per-run theorem
through the block framework that GAS, calls and copies of dynamic size need, here with the oracle
the fragment needs (any oracle meeting `CertOk`), so the framework's hypotheses are met by every
program the checker accepts.
-/

namespace SolidCore.Refinement.Solar.AssembleRunLoop

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- The relation at a block entry, at any gas: the block is within the layout with a stack between
its bounds, typed as its entry says, the code from EthLib's pc is the rest of the layout, memory is
below the certificate's bound and agrees, and the storage and logs agree. -/
def Ent (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray) (msg : Message .fusaka)
    (ss0 : Substate) (x : Nat × List Word × Machine.State) (evm : Evm .fusaka Nat) : Prop :=
  ∃ (Tw : List Word) (pc : Nat) (M : ByteArray) (st : State.TransactionState) (ss : Substate),
    x.1 ≤ p.blocks.length ∧
    (x.1 < p.blocks.length → c.need x.1 ≤ x.2.1.length ∧ x.2.1.length ≤ maxH mx x.1) ∧
    SR c (c.entry x.1) x.2.1 Tw ∧
    Seg (bytesOf code) c.offset pc (lowerFrom p c x.1 (p.blocks.drop x.1)) code.size ∧
    M.size ≤ c.top ∧ MemRel x.2.2.memory M ∧ Rel msg ss0 st ss x.2.2 ∧
    At code msg pc Tw M evm.gas st ss .empty evm

/-- A frame with `K` more gas that meets `At` is a frame that meets it with its own gas. -/
theorem at_of_addGas {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {G : Nat} {st : State.TransactionState} {ss : Substate} {K : Nat}
    {m : Evm .fusaka Nat} (h : At code msg pc T M G st ss .empty (addGas K m)) :
    At code msg pc T M m.gas st ss .empty m ∧ m.gas + K = G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, rfl, h8, h9, h10, h11, h12, h13⟩, by simpa using h7⟩

open SolarTV.EVM.Program in
/-- **A block of code with loops, read back from a run that succeeds.** -/
theorem advances_checkL {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobL p c mx code) {o : Oracle} {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o) (T0 : RunTable) (x : Nat × List Word × Machine.State)
    (evm : Evm .fusaka Nat) (hE : Ent p c mx code msg ss0 x evm) :
    Advances (fun o => block o call p) (fun _ => o) (fun _ => Ent p c mx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p c e.gas y.1) T0 x evm := by
  intro bound runChild _ within fin hrun hok
  obtain ⟨b, S, s⟩ := x
  obtain ⟨Tw, pc, M, st, ss, hle, hneed, hR, hseg, htop, hmem, R, hat⟩ := hE
  simp only at hle hneed hR hseg hmem R
  -- The block with gas to spare: `K` more than the frame holds.
  generalize hK : 22100 * bmax c + memoryGasCost c.top = K
  generalize hg : evm.gas = g at hat
  have hp : At code msg pc Tw M (g + K) st ss .empty (addGas K evm) := hat.addGas K
  have E : EntryL c code call (lowerFrom p c b (p.blocks.drop b)) (bmax c) pc s M (g + K) :=
    ⟨hseg, by omega, htop, hmem⟩
  by_cases hb : b < p.blocks.length
  · have hblk : p.blocks[b]? = some p.blocks[b] := List.getElem?_eq_getElem hb
    obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
    obtain ⟨hn, hm⟩ := hneed hb
    have hbm := budget_le_bmax c b
    obtain ⟨pc1, g1, hlabel, hg1, I1⟩ : ∃ pc1 g1, HoareG .fusaka (At code msg pc Tw M (g + K) st ss .empty)
        (At code msg pc1 Tw M g1 st ss .empty) ∧ g1 + (if isTarget p c b then 1 else 0) ≤ g + K ∧
        InvL c code call (lowerInstrs p c b p.blocks[b] ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) (budget c b - labelItems p c b)
          0 pc1 S s M g1 := by
      have E' := E
      rw [lowerFrom_drop p c hb, lowerBlock, List.append_assoc] at E'
      have hG := E'.gas
      by_cases ht : isTarget p c b = true
      · have hl : labelItems p c b = 1 := by simp [labelItems, ht]
        rw [hl] at hL ⊢
        simp only [ht, ite_true, List.singleton_append] at E'
        obtain ⟨next, hd, hseg'⟩ := E'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        exact ⟨pc + 1, g + K - 1, Logic.jumpdestG hlt hcode (by omega), by simp only [ht, ite_true]; omega,
          ⟨hseg', by omega, by omega, E'.le_top, E'.mem⟩⟩
      · have hl : labelItems p c b = 0 := by simp [labelItems, ht]
        rw [hl, Nat.sub_zero]
        simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at E'
        exact ⟨pc, g + K, Triple.of_imp fun _ h => h, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          ⟨E'.seg, by omega, by omega, E'.le_top, E'.mem⟩⟩
    have hsim := exec_simL (o := o) G.toT hdata hvalue hstatic hself hcaller ho hbenv (fun _ => htx) he b hb 0
      p.blocks[b] (c.need b) [] (c.entry b) S Tw _ s pc1 M g1 st ss hblock hn (by omega)
      (KR.nil _) hR I1 R
    have hbl : block o call p (b, S, s) = some (exec o call b p.blocks[b] S s) := by
      simp only [block, hblk]
    refine ⟨T0, exec o call b p.blocks[b] S s, RunTable.Le.refl T0, fun _ _ => hbl, ?_, ?_⟩
    · intro res hres
      rw [hres] at hsim
      exact SpecG.low (SpecG.seq hlabel hsim) hp within hrun hok
    · intro y hy
      rw [hy] at hsim
      obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh, hR', E', R'⟩ := hsim
      obtain ⟨e1, r1, he1⟩ := hlabel _ hp
      obtain ⟨mid, r2, hmid⟩ := hh e1 he1
      obtain ⟨m, within', hz, hrm⟩ := reaches_low (r1.trans r2) K evm rfl within hrun hok
      rw [hz] at hmid
      obtain ⟨hatm, hgm'⟩ := at_of_addGas hmid
      have hgm := reaches_gas_le r2
      rw [hz, he1.2.2.2.2.2.2.1] at hgm
      simp only [gas_addGas] at hgm
      have hms := meas_step (c := c) (g := g) (g' := m.gas) hb htle (by omega) hj
      refine ⟨m, within', ⟨T', pc', M', st', ss', htle, hneedt, hR', E'.seg, E'.le_top, E'.mem, R',
        hatm⟩, ?_, hrm⟩
      show meas p c m.gas t < meas p c evm.gas b
      rw [hg]
      omega
  · obtain rfl : b = p.blocks.length := by omega
    have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
    have hbl : block o call p (p.blocks.length, S, s) = some (.inl (.stop, s)) := by
      simp only [block, hblk, ite_true]
    refine ⟨T0, _, RunTable.Le.refl T0, fun _ _ => hbl, ?_, ?_⟩
    · intro res hres
      cases hres
      have hseg' := hseg
      rw [lowerFrom_nil p c (by omega)] at hseg'
      have hpc := hseg'.nil_end
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) hp within hrun hok
    · intro y hy
      cases hy

/-- The oracle the fragment of the checker runs under: any one meeting `CertOk`. -/
def fragOracle : Oracle := tableOracle (envOracle (ethOracle anyOracle)) {}

/-- **The loop assembly theorem, run by run, at the run's own gas**: `RunOracle.withinRun_of_checkL`
through the block framework of `AssembleRun`, with no gas reserve across blocks. -/
theorem withinRun_of_checkL_atGas {p : Assemble.Program} {code : ByteArray} {c : Cert}
    {mx : List Nat} (hc : checkL p code c mx = true) (scope : Call → Prop) :
    WithinRun evmirSem (fun _ => p) code scope (CertOk c) := by
  obtain ⟨G, hseg, hneed0⟩ := globL_of_checkL hc
  have hok := table_ok anyOracle {}
  refine withinRun_of_advances (fun _ => fragOracle) (fun _ => ⟨fun _ => hok.1, fun _ => hok.2⟩)
    fun gas call _ => ⟨fun ss0 _ => Ent p c mx code (Final.Target.messageWith gas code call) ss0,
      fun y e => AssembleLoop.meas p c e.gas y.1, fun st' ss' R => ?_,
      fun ss0 T x evm hE => advances_checkL G rfl
        (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl (fun _ => hok.1) rfl rfl
        (fun _ => hok.2) T x evm hE⟩
  refine ⟨[], 0, .empty, st', ss', Nat.zero_le _, fun _ => ⟨by simp [hneed0], by simp⟩, SR.nil c _,
    by rw [List.drop_zero]; exact hseg, by simp, memRel_initial, R, ?_⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleRunLoop.advances_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms advances_checkL

/-- info: 'SolidCore.Refinement.Solar.AssembleRunLoop.withinRun_of_checkL_atGas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_of_checkL_atGas

end SolidCore.Refinement.Solar.AssembleRunLoop

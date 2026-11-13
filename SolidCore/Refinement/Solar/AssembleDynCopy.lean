import SolidCore.Refinement.Solar.AssembleDyn
import SolidCore.Refinement.Solar.AssembleEffects

/-!
# CALLDATACOPY of any range at the frame's own gas

A run that succeeds paid for CALLDATACOPY's growth of memory (`cdc_back`), so with the budget of
`AssembleDyn` SolarTV's copy agrees with EthLib's at any destination and size (`cdc_dyn`): the
calldata-sized copies of ABI decoding.
-/

namespace SolidCore.Refinement.Solar.AssembleDynCopy

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleDyn SolidCore.Refinement.Solar.AssembleEffects
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- **CALLDATACOPY in a run that succeeds**: the frame had the gas for the copy and the growth of
memory, and the run goes on from the frame after it. -/
theorem cdc_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss .empty evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat ⟨(bufferRead msg.data off.toNat sz.toNat).toArray⟩)
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss .empty m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.calldatacopy (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss .empty)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .calldatacopy := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded instruction_calldatacopy]
      rw [copyToMemory_cons hst]
      have hlt' : g < 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost :=
        Nat.lt_of_not_le hg
      have hc : GasMeter.charge e.gas (OPCODE_CALLDATACOPY_BASE + OPCODE_COPY_PER_WORD *
          wordCount sz.toNat + (extendMemory e.memory.size [(d, sz)]).cost) = .error .outOfGas := by
        rw [hgas, hmem, show OPCODE_CALLDATACOPY_BASE = 3 from rfl,
          show OPCODE_COPY_PER_WORD = 3 from rfl]
        simp only [GasMeter.charge]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      simp only [hc]
      rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rw [hf.2.1] at hok
    cases hok

/-- **CALLDATACOPY of any range, in a run that succeeds**: with the budget below `2 ^ 300`,
SolarTV's copy agrees with EthLib's memory after it, the budget holds at the gas left, and the run
goes on. -/
theorem cdc_dyn {code : ByteArray} {msg : Message .fusaka} {call : Call} (hdata : msg.data = call.calldata)
    {pc : Nat} {d off sz : Word} {T : List Word} {M : ByteArray} {g G : Nat}
    {st : State.TransactionState} {ss : Substate} {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M)
    (hb : MemBudget G M g) (hG : G < 2 ^ 300) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (d :: off :: sz :: T) M g st ss .empty evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => calldataByte call (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss .empty m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := cdc_back hat hlt hbyte within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hbound : sz = 0 ∨ (d.toNat + sz.toNat + 31) / 32 < 2 ^ 251 := by
    by_cases hz : sz = 0
    · exact .inl hz
    · exact .inr (words_lt_of_cost (budget_grow hmod hz hb hg).1 hG)
  have hfit : sz.toNat ≠ 0 →
      d.toNat + sz.toNat ≤ (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy).size := by
    intro hz
    have hz' : sz ≠ 0 := fun h => hz (by simp [h])
    rw [size_memoryExtend_extendMemory' hmod hz']
    have := le_ceil32 (d.toNat + sz.toNat)
    omega
  refine ⟨_, _, m, within', ?_, ?_, by omega, hat', hrun'⟩
  · have he := memRel_expandW hm hbound
    rw [← write_expand]
    refine memRel_write he hfit (size_bufferRead _ _ _) (fun i hi => ?_)
    rw [byteAt_bufferRead, ite_cond_eq_true _ _ (eq_true hi), hdata, calldataByte_eq]
  · refine MemBudget.grow hmod hb hg ?_
    rw [size_memoryWrite_of_fit, size_memoryExtend]
    intro h
    rw [size_bufferRead] at h ⊢
    exact hfit h

/-- info: 'SolidCore.Refinement.Solar.AssembleDynCopy.cdc_dyn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cdc_dyn

end SolidCore.Refinement.Solar.AssembleDynCopy

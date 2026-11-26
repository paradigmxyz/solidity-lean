import SolidCore.Refinement.Solar.AssembleDyn
import SolidCore.Refinement.Solar.AssembleEffects

/-!
# CALLDATACOPY of any range at the frame's own gas

A run that succeeds paid for CALLDATACOPY's growth of memory (`cdc_back`), so with the budget of
`AssembleDyn` SolarTV's copy agrees with EthLib's at any destination and size (`cdc_dyn`): the
calldata-sized copies of ABI decoding. `copy_dyn` is the memory half of every such copy (calldata,
code and return data): a paid copy of any range keeps memory related and the budget.
-/

namespace SolidCore.Refinement.Solar.AssembleDynCopy

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleDyn SolidCore.Refinement.Solar.AssembleEffects
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

variable {rd : ByteArray}

/-- **CALLDATACOPY in a run that succeeds**: the frame had the gas for the copy and the growth of
memory, and the run goes on from the frame after it. -/
theorem cdc_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none ∨ fin.error = some .revert) :
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat ⟨(bufferRead msg.data off.toNat sz.toNat).toArray⟩)
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  backR (Logic.calldatacopy hlt hbyte)
    (fun hg => faultAt hlt hbyte (ofByte_of_decode rfl (Fork.frontier_le _))
      instruction_calldatacopy fun e hat' => by
        obtain ⟨-, -, -, -, hst, rfl, rfl, -⟩ := hat'
        rw [copyToMemory_cons hst]
        exact map_charge_lt (Nat.lt_of_not_le hg) _) hat within hrun hok

/-- **A paid copy of any range**: when the frame pays `pre` and the growth of memory for the range,
with the budget below `2 ^ 300`, writing bytes `B` that agree with SolarTV's source over the range
into the grown memory keeps memory related, and the budget holds at the gas left. -/
theorem copy_dyn {M B : ByteArray} {g G pre : Nat} {m0 : SolarTV.Machine.Mem} {d sz : Word}
    {src : Nat → Memory.Byte} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hg : pre + (extendMemory M.size [(d, sz)]).cost ≤ g) (hB : B.size = sz.toNat)
    (hsrc : ∀ i, i < sz.toNat → (byteAt B i).toBitVec = src i) :
    MemRel (m0.write d.toNat sz.toNat src)
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy) d.toNat B) ∧
      MemBudget G (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy) d.toNat B)
        (g - (pre + (extendMemory M.size [(d, sz)]).cost)) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hfit : sz.toNat ≠ 0 →
      d.toNat + sz.toNat ≤ (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy).size := by
    intro hz
    rw [size_memoryExtend_extendMemory' hmod fun h => hz (by simp [h])]
    have := le_ceil32 (d.toNat + sz.toNat)
    omega
  refine ⟨?_, MemBudget.grow hmod hb hg ?_⟩
  · rw [← write_expand]
    exact memRel_write (memRel_expandW hm (boundR hm hb hG hg)) hfit hB hsrc
  · rw [size_memoryWrite_of_fit, size_memoryExtend]
    intro h
    rw [hB] at h ⊢
    exact hfit h

/-- **CALLDATACOPY of any range, in a run that succeeds**: with the budget below `2 ^ 300`,
SolarTV's copy agrees with EthLib's memory after it, the budget holds at the gas left, and the run
goes on. -/
theorem cdc_dyn {code : ByteArray} {msg : Message .fusaka} {call : Call} (hdata : msg.data = call.calldata)
    {pc : Nat} {d off sz : Word} {T : List Word} {M : ByteArray} {g G : Nat}
    {st : State.TransactionState} {ss : Substate} {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M)
    (hb : MemBudget G M g) (hG : G < 2 ^ 300) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => calldataByte call (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := cdc_back hat hlt hbyte within hrun (.inl hok)
  obtain ⟨hR, hB⟩ := copy_dyn (src := fun i => calldataByte call (off.toNat + i)) hm hb hG hg
    (size_bufferRead msg.data off.toNat _) fun i hi => by
      rw [byteAt_bufferRead, ite_eq_left_of_eq_true _ _ (eq_true hi), hdata, calldataByte_eq]
  exact ⟨_, _, m, within', hR, hB, by omega, hat', hrun'⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleDynCopy.cdc_dyn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cdc_dyn

end SolidCore.Refinement.Solar.AssembleDynCopy

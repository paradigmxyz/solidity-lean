import SolidCore.Refinement.Solar.AssembleCall
import SolidCore.Refinement.Solar.AssembleCreate

/-!
# CALL with value and CREATE2 in SolarTV, beside EthLib

What SolarTV's effects do for a CALL with value and a CREATE2, under an oracle that answers each as
the callee's frame ended, and that this is what EthLib leaves (`AssembleCallValue.callValue_back`,
`AssembleCreateBack.create2_back`):

* `call_effectW`: CALL with operands `gas, addr, value, ranges` pushes the flag EthLib pushes, writes
  the callee's output to the output range as EthLib does, takes it as the return data, and leaves
  the storage and transient storage the oracle answers after the call (`storageAfter` of the world
  with the call): a reentrant callee may change them, so they are the oracle's, which a run's table
  takes from the frame after the callee.
* `create2_effectW`: CREATE2 pushes the word the oracle answers for the creation, which is EthLib's
  (the EIP-1014 address on success, below `2 ^ 160`, `toU256_lt`; 0 on failure), grows memory as
  EthLib does, and records as init code the bytes EthLib sends as the message's code.
-/

namespace SolidCore.Refinement.Solar.AssembleCallValueEffect

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCall
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- The world after a CALL with value, as SolarTV records it. -/
abbrev callWorld (s : State) (gas addr value inOff inSize outOff outSize : Word) : List Event :=
  s.world ++ [.call .call [gas, addr, value]
    (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
      inOff.toNat inSize.toNat) s.storage s.transient]

/-- **CALL with value in SolarTV at any ranges** whose words SolarTV counts, under an oracle that
answers the call as the callee's frame `child` ended. -/
theorem call_effectW {o : Oracle} {call : Call} {s : State} {M : ByteArray}
    {gas addr value inOff inSize outOff outSize : Word} {child : Evm .fusaka Nat}
    (hm : MemRel s.memory M)
    (hb1 : inSize = 0 ∨ (inOff.toNat + inSize.toNat + 31) / 32 < 2 ^ 251)
    (hb2 : outSize = 0 ∨ (outOff.toNat + outSize.toNat + 31) / 32 < 2 ^ 251)
    (hflag : callFlag o (callWorld s gas addr value inOff inSize outOff outSize) =
      if child.error.isNone then 1 else 0)
    (hrd : RdRel o (callWorld s gas addr value inOff inSize outOff outSize) child.output) :
    ∃ s', Effect.apply o call (.call .call) [gas, addr, value, inOff, inSize, outOff, outSize] s =
        some (some (if child.error.isNone then 1 else 0), s') ∧
      s'.storage = o.storageAfter (callWorld s gas addr value inOff inSize outOff outSize) ∧
      s'.transient = o.transientAfter (callWorld s gas addr value inOff inSize outOff outSize) ∧
      RdRel o s'.world child.output ∧
      s'.world = callWorld s gas addr value inOff inSize outOff outSize ∧
      MemRel s'.memory (memoryWrite (memoryExtend M
          (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
        outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size))) := by
  have he := memRel_expand2W hm hb1 hb2
  refine ⟨called o .call s ((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat) outOff outSize (callWorld s gas addr value inOff inSize outOff outSize),
    ?_, rfl, rfl, hrd, rfl, ?_⟩
  · simp only [Effect.apply, CallKind.shape, hflag]
  · simp only [called]
    rw [hrd.1]
    refine memRel_write he (fun hz => ?_) ?_ (fun i hi => ?_)
    · have hz' : outSize ≠ 0 := fun h => hz (by simp [h])
      have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
      have := le_ceil32_add_expandBy M.size [(inOff, inSize), (outOff, outSize)] (outOff, outSize)
        (by simp) hz'
      dsimp only at this
      rw [ceil32_of_mod hmod] at this
      rw [size_memoryExtend]
      have := Nat.min_le_left outSize.toNat child.output.size
      omega
    · simp [ByteArray.size_extract]
    · rw [byteAt_extract, Nat.zero_add, if_pos (by omega)]
      exact (hrd.2 i (by omega)).symm

/-- An address, as a word, is below `2 ^ 160`. -/
theorem toU256_lt (a : Address) : a.toU256.toNat < 2 ^ 160 := by
  unfold Address.toU256
  rw [BitVec.toNat_ofNat]
  have h := bytesToNat_lt a.toList
  simp only [Vector.length_toList] at h
  rw [show (256 : Nat) ^ 20 = 2 ^ 160 from rfl] at h
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- The world after a CREATE2, as SolarTV records it. -/
abbrev createWorld (s : State) (value offset size salt : Word) : List Event :=
  s.world ++ [.create [value, salt] ((s.memory.expand offset.toNat size.toNat).read offset.toNat
    size.toNat) s.storage s.transient]

/-- **CREATE2 in SolarTV** at any range whose words SolarTV counts, under an oracle that answers the
creation with the word `r` below `2 ^ 160` (the address EthLib pushes on success, 0 on failure): it
pushes `r`, grows memory as EthLib does, records as init code the bytes EthLib reads, and leaves
the storage the oracle answers after the creation. -/
theorem create2_effectW {o : Oracle} {call : Call} {s : State} {M : ByteArray}
    {value offset size salt r : Word} (hm : MemRel s.memory M)
    (hb : size = 0 ∨ (offset.toNat + size.toNat + 31) / 32 < 2 ^ 251)
    (hr : r.toNat < 2 ^ 160)
    (hres : (o.result (createWorld s value offset size salt)).toNat % 2 ^ 160 = r.toNat) :
    ∃ s', Effect.apply o call .create2 [value, offset, size, salt] s = some (some r, s') ∧
      s'.storage = o.storageAfter (createWorld s value offset size salt) ∧
      s'.transient = o.transientAfter (createWorld s value offset size salt) ∧
      s'.world = createWorld s value offset size salt ∧
      MemRel s'.memory (memoryExtend M (extendMemory M.size [(offset, size)]).expandBy) ∧
      ((s.memory.expand offset.toNat size.toNat).read offset.toNat size.toNat).map BitVec.toNat =
        (memoryReadBytes (memoryExtend M (extendMemory M.size [(offset, size)]).expandBy)
          offset.toNat size.toNat).toList.map (·.toNat) := by
  refine ⟨⟨s.memory.expand offset.toNat size.toNat, o.storageAfter (createWorld s value offset size salt),
    o.transientAfter (createWorld s value offset size salt), createWorld s value offset size salt⟩,
    ?_, rfl, rfl, rfl, memRel_expandW hm hb, (read_eq hm).symm⟩
  simp only [Effect.apply, created, hres]
  congr
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValueEffect.call_effectW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call_effectW

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValueEffect.create2_effectW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_effectW

end SolidCore.Refinement.Solar.AssembleCallValueEffect

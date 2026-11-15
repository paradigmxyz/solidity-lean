import SolidCore.Refinement.Solar.EthLibErrLow
import SolidCore.Refinement.Solar.AssembleRevert
import SolidCore.Refinement.Solar.AssembleCut

/-!
# EVM IR to bytecode with GAS and memory at any offset, with the revert data related

`AssembleCut.runs_of_checkC` reads each block back from a run that succeeds: a run that reverts
fails, and `AssembleDyn.revert_false` rules REVERT out, so its revert data stand for themselves.
Here the same reading back holds of a run that ends with no error or reverts (`OkR`): a segment
moved back to the frame's gas by `RevertErr.reaches_lowR` and `RevertErr.SpecG.lowR`
(`reaches_lowAt`, `lowAt`), each instruction at the frame's gas (`gas_backR`, `mstore_dynR`, ...)
ruling out only an exceptional halt, and REVERT at the frame's gas (`revert_backR`) showing the
program's revert, with its data, as RETURN shows its output.

* `segR`, `advances_checkCR`: `AssembleCut.seg` and `advances_checkC` for such runs, REVERT
  included.
* `within_of_advancesR`: `AssembleRun.within_of_advances` with the revert data related
  (`AssembleLoop.WithinR`).
* `runs_of_checkCR`, `withinRunR_of_checkC`: for every program the checker with GAS accepts, at
  every gas below `2 ^ 256` and every call, the oracle of the run's table makes every result of the
  bytecode the EVM IR's, a revert with its data among them, unless the run halted exceptionally.

The proofs of the instructions are those of `AssembleDyn`, `AssembleDynCopy` and `AssembleCut`
with the run's end allowed to revert: each rules out an exceptional halt the same way.
-/

namespace SolidCore.Refinement.Solar.AssembleRevertCut

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleDyn
  SolidCore.Refinement.Solar.AssembleDynCopy SolidCore.Refinement.Solar.AssembleEffects

/-- A run that ends with no error, or with the revert error. -/
def OkR (fin : Evm .fusaka Nat) : Prop := fin.error = none ∨ fin.error = some .revert

/-- `SpecG.low` from a frame of the code, for a run that ends with no error or reverts. -/
theorem lowAt {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {Q : Evm .fusaka Nat → Prop} (h : SpecG .fusaka (At code msg pc T M g st ss rd) Q) {k : Nat}
    {l : Evm .fusaka Nat} (hp : At code msg pc T M g st ss rd (addGas k l)) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld l.gas ≤ bound)
    {s : Evm .fusaka Nat}
    (hs : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild l within = .ok s)
    (hok : OkR s) : Q (addGas k s) := by
  have he : l.error = none := by
    have := hp.2.2.2.2.2.2.2.2.1
    simpa using this
  exact RevertErr.SpecG.lowE (by decide) h hp (by rw [he]; simp) within hs hok

/-- `reaches_low` from a frame of the code, for a run that ends with no error or reverts. -/
theorem reaches_lowAt {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {hi z : Evm .fusaka Nat} (hr : Reaches (StepG .fusaka) hi z) (k : Nat) (low : Evm .fusaka Nat)
    (e : hi = addGas k low) (hat : At code msg pc T M g st ss rd low) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld low.gas ≤ bound)
    {s : Evm .fusaka Nat}
    (hs : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild low within = .ok s)
    (hok : OkR s) : ∃ m within', z = addGas k m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok s := by
  rcases hok with h | h
  · exact reaches_low hr k low e within hs h
  · exact RevertErr.reaches_lowR (by decide) hr k low e
      (by rw [hat.2.2.2.2.2.2.2.2.1]; simp) within hs h

section Dyn

variable {rd : ByteArray}

/-- **MSTORE in a run that succeeds**: the frame had the gas for it and its growth of memory, and
the run goes on from the frame after it. -/
theorem mstore_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o v : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: v :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
          (wordBytes v))
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 3 + (extendMemory M.size [(o, 32)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.mstore (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (o :: v :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .mstore := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded instruction_mstore, mstoreStep_cons hst]
      have hc : GasMeter.charge e.gas (OPCODE_MSTORE_BASE + (extendMemory e.memory.size [(o, 32)]).cost)
          = .error .outOfGas := by
        rw [hgas, hmem, show OPCODE_MSTORE_BASE = 3 from rfl]
        have hlt' : g < 3 + (extendMemory M.size [(o, 32)]).cost := Nat.lt_of_not_le hg
        simp only [GasMeter.charge]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      simp only [hc]
      rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **MLOAD in a run that succeeds**: the frame had the gas for it and its growth of memory, and
the run goes on from the frame after it. -/
theorem mload_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat 32) 0 32 :: T)
        (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy)
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 3 + (extendMemory M.size [(o, 32)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.mload (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (o :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .mload := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded instruction_mload, mloadStep_cons hst]
      have hc : GasMeter.charge e.gas (OPCODE_MLOAD_BASE + (extendMemory e.memory.size [(o, 32)]).cost)
          = .error .outOfGas := by
        rw [hgas, hmem, show OPCODE_MLOAD_BASE = 3 from rfl]
        have hlt' : g < 3 + (extendMemory M.size [(o, 32)]).cost := Nat.lt_of_not_le hg
        simp only [GasMeter.charge]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      simp only [hc]
      rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **RETURN in a run that succeeds**: the frame had the gas for the growth of memory to its
range. -/
theorem return_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    (extendMemory M.size [(o, sz)]).cost ≤ g := by
  refine Nat.le_of_not_lt fun hlt' => ?_
  have hspec : Spec .fusaka (At code msg pc (o :: sz :: T) M g st ss rd)
      (Faulted .outOfGas st ss) := by
    refine At.fault rfl fun e hat' => ?_
    obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
    subst hcode hpc
    have decoded : Op.ofByte .fusaka e.code[e.pc] = some .«return» := by
      rw [hbyte]
      exact ofByte_of_decode rfl (Fork.frontier_le _)
    rw [step_of_instruction hlt decoded instruction_return, returnStep_cons hst]
    have hc : GasMeter.charge e.gas (extendMemory e.memory.size [(o, sz)]).cost =
        .error .outOfGas := by
      rw [hgas, hmem]
      simp only [GasMeter.charge]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
    simp only [hc]
    rfl
  obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
  rw [runFrame_of_reaches hr hstop within] at hrun
  cases hrun
  rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **KECCAK256 in a run that succeeds**: the frame had the gas for the hash and the growth of
memory to its range, and the run goes on from the frame after it. -/
theorem keccak_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (keccak (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
          o.toNat sz.toNat) :: T)
        (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.keccak256 (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (o :: sz :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .keccak256 := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded instruction_keccak256, keccak256Step_cons hst]
      have hlt' : g < keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost := Nat.lt_of_not_le hg
      have hc : GasMeter.charge e.gas (keccak256Cost sz +
          (extendMemory e.memory.size [(o, sz)]).cost) = .error .outOfGas := by
        rw [hgas, hmem]
        simp only [GasMeter.charge]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      simp only [hc]
      rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **KECCAK256 of any range, in a run that succeeds**: with the budget below `2 ^ 300`,
SolarTV's growth agrees with EthLib's memory after it, the budget holds at the gas left, and the run
goes on. -/
theorem keccak_dynR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.expand o.toNat sz.toNat) (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) ∧
      MemBudget G (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost)) ∧
      At code msg (pc + 1)
        (keccak (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
          o.toNat sz.toNat) :: T)
        (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := keccak_backR hat hlt hbyte within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hbound : sz = 0 ∨ (o.toNat + sz.toNat + 31) / 32 < 2 ^ 251 := by
    by_cases hz : sz = 0
    · exact .inl hz
    · exact .inr (words_lt_of_cost (budget_grow hmod hz hb hg).1 hG)
  refine ⟨m, within', memRel_expandW hm hbound, ?_, hat', hrun'⟩
  exact MemBudget.grow hmod hb hg (size_memoryExtend M _)

/-- **LOGn in a run that succeeds**: the frame had the gas for the log and the growth of memory
to its range, and the run goes on from the frame after it, with the log appended. -/
theorem log_backR {n : Fin 5} {byte : UInt8} {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {o sz : Word} {words T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} {evm : Evm .fusaka Nat}
    (hat : At code msg pc (o :: sz :: (words ++ T)) M g st ss rd evm)
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : msg.isStatic = false) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    logCost n.val sz + (extendMemory M.size [(o, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (logCost n.val sz + (extendMemory M.size [(o, sz)]).cost)) st
        { ss with
          logs := ss.logs.push
            { address := msg.currentTarget
              topics := words.map U256.toBeBytes
              data := memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
                o.toNat sz.toNat } } rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : logCost n.val sz + (extendMemory M.size [(o, sz)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.log (fork := .fusaka) hlen hlt hbyte decoded hstatic hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (o :: sz :: (words ++ T)) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have dec' : Op.ofByte .fusaka e.code[e.pc] = some (.log n) := by
        rw [hbyte]
        exact ofByte_of_decode decoded (Fork.frontier_le _)
      rw [step_of_instruction hlt dec' (instruction_log n)]
      have hl := e.stack.property
      rw [hst] at hl
      have hlr : (words ++ T).length ≤ STACK_LIMIT := by simp at hl ⊢; omega
      have hs : e.stack = ⟨o :: sz :: (words ++ T), hst ▸ e.stack.property⟩ := Subtype.ext hst
      have htop := popTopics_append (evm := { e with stack := ⟨words ++ T, hlr⟩ })
        (words := words) (rest := T) rfl
      rw [hlen] at htop
      have hlt' : e.gas < logCost n.val sz + (extendMemory e.memory.size [(o, sz)]).cost := by
        rw [hgas, hmem]
        omega
      simp only [logStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
      rw [htop]
      simp only [chargeGasAndMemory, chargeGas, GasMeter.charge, logCost] at hlt' ⊢
      simp [hlt']
      try rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **LOGn of any range, in a run that succeeds**: with the budget below `2 ^ 300`, SolarTV's
growth agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on
with the log appended. -/
theorem log_dynR {n : Fin 5} {byte : UInt8} {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {o sz : Word} {words T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState}
    {ss : Substate} {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g)
    (hG : G < 2 ^ 300) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (o :: sz :: (words ++ T)) M g st ss rd evm)
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : msg.isStatic = false) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.expand o.toNat sz.toNat) (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) ∧
      MemBudget G (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (logCost n.val sz + (extendMemory M.size [(o, sz)]).cost)) ∧
      At code msg (pc + 1) T (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (logCost n.val sz + (extendMemory M.size [(o, sz)]).cost)) st
        { ss with
          logs := ss.logs.push
            { address := msg.currentTarget
              topics := words.map U256.toBeBytes
              data := memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
                o.toNat sz.toNat } } rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := log_backR hat hlen hlt hbyte decoded hstatic within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hbound : sz = 0 ∨ (o.toNat + sz.toNat + 31) / 32 < 2 ^ 251 := by
    by_cases hz : sz = 0
    · exact .inl hz
    · exact .inr (words_lt_of_cost (budget_grow hmod hz hb hg).1 hG)
  exact ⟨m, within', memRel_expandW hm hbound, MemBudget.grow hmod hb hg (size_memoryExtend M _),
    hat', hrun'⟩

/-- **MSTORE at any offset, in a run that succeeds**: with the budget below `2 ^ 300`, SolarTV's
store agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on. -/
theorem mstore_dynR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o v : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: v :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.store o.toNat v) M' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := mstore_backR hat hlt hbyte within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hc, hb'⟩ := budget_grow (pre := 3) hmod (o := o) (sz := 32) (by decide) hb hg
  have h32 : (32 : Word).toNat = 32 := rfl
  rw [h32] at hc
  have hw := words_lt_of_cost hc hG
  obtain ⟨hmem', -⟩ := memRel_storeW (v := v) hm hw
  refine ⟨_, _, m, within', hmem', ?_, by omega, hat', hrun'⟩
  unfold MemBudget
  rw [size_memoryWrite_of_fit, size_memoryExtend]
  · exact hb'
  · intro _
    rw [size_wordBytes, size_memoryExtend_extendMemory' hmod (by decide), h32]
    have := le_ceil32 (o.toNat + 32)
    omega

/-- **MLOAD at any offset, in a run that succeeds**: EthLib pushes SolarTV's load, SolarTV's growth
agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on. -/
theorem mload_dynR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.expand o.toNat 32) M' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) (m0.load o.toNat :: T) M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := mload_backR hat hlt hbyte within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hc, hb'⟩ := budget_grow (pre := 3) hmod (o := o) (sz := 32) (by decide) hb hg
  have h32 : (32 : Word).toNat = 32 := rfl
  rw [h32] at hc
  have hw := words_lt_of_cost hc hG
  have hmem' := memRel_expandW (o := o) (sz := 32) hm (.inr (by rw [h32]; exact hw))
  rw [h32] at hmem'
  rw [load_eq hm] at hat'
  refine ⟨_, _, m, within', hmem', ?_, by omega, hat', hrun'⟩
  unfold MemBudget
  rw [size_memoryExtend]
  exact hb'

/-- **CALLDATACOPY in a run that succeeds**: the frame had the gas for the copy and the growth of
memory, and the run goes on from the frame after it. -/
theorem cdc_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat ⟨(bufferRead msg.data off.toNat sz.toNat).toArray⟩)
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.calldatacopy (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss rd)
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
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **CALLDATACOPY of any range, in a run that succeeds**: with the budget below `2 ^ 300`,
SolarTV's copy agrees with EthLib's memory after it, the budget holds at the gas left, and the run
goes on. -/
theorem cdc_dynR {code : ByteArray} {msg : Message .fusaka} {call : Call} (hdata : msg.data = call.calldata)
    {pc : Nat} {d off sz : Word} {T : List Word} {M : ByteArray} {g G : Nat}
    {st : State.TransactionState} {ss : Substate} {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M)
    (hb : MemBudget G M g) (hG : G < 2 ^ 300) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => calldataByte call (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := cdc_backR hat hlt hbyte within hrun hok
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


/-- **REVERT in a run that ends with no error or reverts**: the frame had the gas for the growth of
memory to its range. -/
theorem revert_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    (extendMemory M.size [(o, sz)]).cost ≤ g := by
  refine Nat.le_of_not_lt fun hlt' => ?_
  have hspec : Spec .fusaka (At code msg pc (o :: sz :: T) M g st ss rd)
      (Faulted .outOfGas st ss) := by
    refine At.fault rfl fun e hat' => ?_
    obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
    subst hcode hpc
    have decoded : Op.ofByte .fusaka e.code[e.pc] = some .revert := by
      rw [hbyte]
      exact ofByte_of_decode rfl (by decide)
    rw [step_of_instruction hlt decoded (instruction_revert (by decide)), revertStep_eq,
      returnStep_cons hst]
    have hc : GasMeter.charge e.gas (extendMemory e.memory.size [(o, sz)]).cost =
        .error .outOfGas := by
      rw [hgas, hmem]
      simp only [GasMeter.charge]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
    simp only [hc]
    rfl
  obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
  rw [runFrame_of_reaches hr hstop within] at hrun
  cases hrun
  rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

end Dyn

/-- **GAS in a run that succeeds**: the frame had the gas for it, and the run goes on from the frame
after it, with the gas left after its price pushed. -/
theorem gas_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {evm : Evm .fusaka Nat} (hat : At code msg pc T M g st ss rd evm) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5a) (hstack : T.length < STACK_LIMIT) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    2 ≤ g ∧ ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) (BitVec.ofNat 256 (g - 2) :: T) M (g - 2) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 2 ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.gas_rule (fork := .fusaka) hlt hbyte hg hstack evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc T M g st ss rd) (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, -, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .gas := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded rfl]
      simp [readFrame, chargeGas, GasMeter.charge, hgas, OPCODE_GAS, BASE, show g < 2 by omega, bind, Except.bind]
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **The rest of a block from an instruction, read back from a run that succeeds**: the segments
up to each GAS with gas to spare, moved back to the frame's gas, and each GAS at the frame's gas,
its gas added to the table. Every extension of the table it ends with runs the rest of the block to
the same end: a halt the frame shows, or the next block, related to a frame the run goes on from. -/
theorem segR {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobT p c code) (hnc : c.calls = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    {b : Nat} (hb : b < p.blocks.length) {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {fin : Evm .fusaka Nat} (hok : OkR fin) {G0 : Nat} (hG0 : G0 < 2 ^ 256)
    {rd : ByteArray} :
    ∀ (n : Nat) (is : List Assemble.Instr) (h : Nat) (known : Known) (ty : List Ty) (k : Nat)
      (S Tw : List Word) (s : State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate) (T : RunTable) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound),
      is.length < n → blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S Tw →
      Seg (bytesOf code) c.offset pc
        (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size →
      S.length + k ≤ 1000 → M.size ≤ c.top → MemRel s.memory M → Rel msg ss0 st ss s →
      At code msg pc Tw M g st ss rd evm → T.gases.length = gasReads s.world →
      sent s.world = 0 → MemBudget G0 M g →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      ∃ T' r, T.Le T' ∧
        (∀ T'', T'.Le T'' → SolarTV.EVM.Program.exec (O T'') call b is S s = r) ∧
        (∀ res, r = .inl res → PostL call msg.currentTarget ss0 res.2 res.1 fin) ∧
        (∀ y, r = .inr y → (y.1 ≤ p.blocks.length ∧
          (y.1 < p.blocks.length → c.need y.1 ≤ y.2.1.length ∧ y.2.1.length ≤ maxH mx y.1) ∧
          (y.1 = b + 1 ∨ isTarget p c y.1 = true)) ∧
          ∃ (after : Evm .fusaka Nat) (within' : GasMeter.gasHeld after.gas ≤ bound),
            EntC p c mx code msg ss0 y after ∧ T'.gases.length = gasReads y.2.2.world ∧
            sent y.2.2.world = 0 ∧ after.gas ≤ g ∧
            memoryGasCost after.memory.size + after.gas ≤ G0 ∧
            runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, is, h, known, ty, k, S, Tw, s, pc, M, g, st, ss, T, evm, within, hn, hokC, hh, hu, hk,
      hR, hseg, hstk, htop, hmem, R, hat, hTg, hs0, hB, hrun => by
    have hge : evm.gas = g := hat.2.2.2.2.2.2.1
    -- The segment with gas to spare for it alone: `K` more than the frame holds.
    generalize hK : 22100 * k + memoryGasCost c.top = K
    have hp := hat.addGas K
    have I : InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1)
        (p.blocks.drop (b + 1))) k 0 pc S s M (g + K) :=
      ⟨hseg, hstk, by simp only [Nat.add_zero]; omega, htop, hmem⟩
    have hsim := exec_simC (mx := mx) G (o := O T) hdata hvalue hstatic hself hcaller
      (O_ok c T).1 hbenv htx (O_ok c T).2 b hb 0 (G0 + K) rd is h known ty S Tw k s pc M
      (g + K) st ss hokC hh hu hk hR I R (by unfold MemBudget at *; omega)
    have hcnt := (execC_agree (Agree.refl (O T) (gasReads s.world) (sent s.world)) call b is S s
      le_rfl le_rfl).2
    have hex : ∀ T'', T.Le T'' → SolarTV.EVM.Program.exec (O T'') call b is S s =
        match execC (O T) call b is S s with
        | .done r => r
        | .cut i rest S' s' => SolarTV.EVM.Program.exec (O T'') call b (i :: rest) S' s' :=
      fun T'' hle => exec_O hle (by omega) hs0
    generalize hr : execC (O T) call b is S s = r at hsim hcnt hex
    cases r with
    | done r =>
      refine ⟨T, r, RunTable.Le.refl T, fun T'' hle => hex T'' hle, fun res hres => ?_,
        fun y hy => ?_⟩
      · subst hres
        exact lowAt hsim hp within hrun hok
      · subst hy
        obtain ⟨t, S', s'⟩ := y
        obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh', hR', E', R', hB'⟩ := hsim
        obtain ⟨e1, r1, he1⟩ := hh' _ hp
        obtain ⟨m, within', hz, hrm⟩ := reaches_lowAt r1 K evm rfl hat within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hmK⟩ := at_of_addGasR he1
        have hgm := reaches_gas_le r1
        rw [hz] at hgm
        simp only [gas_addGas] at hgm
        have hc1 := hcnt.1 s' rfl
        refine ⟨⟨htle, hneedt, hj⟩, m, within', ⟨T', pc', M', st', ss', rd, htle, hneedt, hR', E'.seg,
          E'.le_top, E'.mem, R', hatm⟩, ?_, ?_, by omega,
          by rw [hatm.2.2.2.2.2.1]; unfold MemBudget at hB'; omega, hrm⟩
        · dsimp only; omega
        · dsimp only; omega
    | cut i rest S' s' =>
      obtain ⟨hci, h', known', ty', k', pc', T', M', g', st', ss', hh', hok2, hh2, hu2, hk2, hR',
        I', R', hB'⟩ := hsim
      -- The segment, moved back to the frame's gas.
      obtain ⟨e1, r1, he1⟩ := hh' _ hp
      obtain ⟨m, within1, hz, hrm⟩ := reaches_lowAt r1 K evm rfl hat within hrun hok
      rw [hz] at he1
      obtain ⟨hatm, hmK⟩ := at_of_addGasR he1
      have hgm := reaches_gas_le r1
      rw [hz] at hgm
      simp only [gas_addGas] at hgm
      have hL := hR'.length
      have hst := I'.stack
      have hc1 := hcnt.1 s' rfl
      have hlen := hcnt.2 _ rest S' s' rfl
      have hmB : MemBudget G0 M' m.gas := by unfold MemBudget at *; omega
      have hci' : isGasI i = true ∨ isLoadI i = true ∨ isStoreI i = true ∨ isRetI i = true ∨
          isRevI i = true ∨ isKecI i = true ∨ isLogI i = true ∨ isCdcI i = true ∨ isScI i = true ∨
          isRdsI i = true ∨ isRdcI i = true ∨ isCallI i = true ∨ isC2I i = true ∨ isCcI i = true := by
        simpa [isCutI, isMemCutI, or_assoc] using hci
      rcases hci' with hgi | hli | hsi | hri | hvi | hki | hlgi | hcdi | hsci | hrdi | hrdci | hcalli |
        hc2i | hcci
      · obtain rfl := isGasI_eq hgi
        obtain ⟨hk1, hok3⟩ := blockOkC_gas hok2
        have hs := I'.seg
        rw [lowerInstrs_gas, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        -- GAS at the frame's gas.
        obtain ⟨h2, m2, within2, hat2, hrun2⟩ :=
          gas_backR hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
        let T1 : RunTable := { T with gases := T.gases ++ [m.gas - 2] }
        have hle1 : T.Le T1 := ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_append _ _⟩
        have hv : ∀ T'', T1.Le T'' → T''.gases.getD (gasReads s'.world) 0 = m.gas - 2 := by
          intro T'' hle
          rw [getD_of_prefix hle.2.2.2.2 (by simp [T1]; omega)]
          simp [T1, List.getD_eq_getElem?_getD, hc1.1, ← hTg]
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) G hnc hdata hvalue hstatic hself hcaller hbenv
          htx hb hok hG0 n rest (h' + 1) [] (some false :: ty') (k' - 1)
          (BitVec.ofNat 256 (m.gas - 2) :: S') (BitVec.ofNat 256 (m.gas - 2) :: T')
          { s' with world := s'.world ++ [.read "gas"] } (pc' + 1) M' (m.gas - 2) st' ss' T1 m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
          I'.mem ⟨R'.storage, R'.account, logsRel_read _ R'.logs⟩ hat2
          (by simp [T1]; omega) (by simp [hc1.2, hs0])
          (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, r, hle1.trans hle2, fun T'' hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T'' (hle1.trans (hle2.trans hle))]
          show SolarTV.EVM.Program.exec (O T'') call b (.effect .gas 0 :: rest) S' s' = r
          rw [exec_gas (hv T'' (hle2.trans hle)) (by omega)]
          exact hex2 T'' hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

      · -- MLOAD at the frame's gas, at any offset.
        obtain rfl := isLoadI_eq hli
        obtain ⟨hk1, hh1, hdat, htop', hok3⟩ := blockOkC_load hok2
        have hs := I'.seg
        rw [lowerInstrs_load, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, S''⟩
        · simp at hh2; omega
        rcases T' with _ | ⟨x', Tr⟩
        · simp at hL
        obtain rfl := (SR.head hR' hdat).symm
        have hR'' := (SR.uncons.1 hR').2
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨M2, g2, m2, within2, hmem2, hb2, hg2, hat2, hrun2⟩ :=
          mload_dynR I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest h' [] (some false :: ty'.drop 1) (k' - 1)
          (s'.memory.load x.toNat :: S'') (s'.memory.load x.toNat :: Tr)
          { s' with memory := s'.memory.expand x.toNat 32 } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.op .load :: rest) _ s' = r
          rw [exec_loadC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩
      · -- MSTORE at the frame's gas, at any offset.
        obtain rfl := isStoreI_eq hsi
        obtain ⟨hk1, hh1, hdat, htop', hok3⟩ := blockOkC_store hok2
        have hs := I'.seg
        rw [lowerInstrs_store, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, S''⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', Tr⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 2) S'' Tr := by simpa using SR.drop 2 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨M2, g2, m2, within2, hmem2, hb2, hg2, hat2, hrun2⟩ :=
          mstore_dynR I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - 2) [] (ty'.drop 2) (k' - 1) S'' Tr
          { s' with memory := s'.memory.store x.toNat y } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.op .store :: rest) _ s' = r
          rw [exec_storeC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

      · -- RETURN at the frame's gas, from any range.
        obtain rfl := isRetI_eq hri
        obtain ⟨hh1, hdat⟩ := blockOkC_ret hok2
        have hs := I'.seg
        rw [lowerInstrs_ret, List.cons_append] at hs
        obtain ⟨next, hd, -⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, S''⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', Tr⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        have hg := return_backR hatm hlt hcode within1 hrm hok
        refine ⟨T, .inl (SolarTV.EVM.Program.output s' (x :: y :: S'') false), RunTable.Le.refl T,
          fun T3 hle => ?_, fun res hres => ?_, fun y hy => ?_⟩
        · rw [hex T3 hle]
          rfl
        · obtain rfl := Sum.inl.inj hres
          simp only [SolarTV.EVM.Program.output, Bool.false_eq_true, ↓reduceIte]
          exact lowAt (SpecG.consequence (return_postSG (ss := ss') hlt hcode (by omega) rfl
            (by rw [read_eq I'.mem]; rfl) rfl (R'.slot hself)) (fun _ h => h)
            (fun _ h => ⟨ss', h, R'.logs⟩)) (hatm.addGas 0) within1 hrm hok
        · cases hy
      · -- REVERT at the frame's gas, from any range: the program's revert, with its data.
        obtain rfl := isRevI_eq hvi
        obtain ⟨hh1, hdat⟩ := blockOkC_revert hok2
        have hs := I'.seg
        rw [lowerInstrs_revert, List.cons_append] at hs
        obtain ⟨next, hd, -⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, S''⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', Tr⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        have hg := revert_backR hatm hlt hcode within1 hrm hok
        refine ⟨T, .inl (SolarTV.EVM.Program.output s' (x :: y :: S'') true), RunTable.Le.refl T,
          fun T3 hle => ?_, fun res hres => ?_, fun y hy => ?_⟩
        · rw [hex T3 hle]
          rfl
        · obtain rfl := Sum.inl.inj hres
          simp only [SolarTV.EVM.Program.output, ↓reduceIte]
          exact lowAt (SpecG.consequence (revert_postSG (ss := ss') (by decide) hlt hcode (by omega)
            rfl (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h)
            (fun _ h => ⟨ss', h, R'.logs⟩)) (hatm.addGas 0) within1 hrm hok
        · cases hy

      · -- KECCAK256 at the frame's gas, of any range.
        obtain rfl := isKecI_eq hki
        obtain ⟨henv, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_kec hok2
        have hs := I'.seg
        rw [lowerInstrs_kec, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, S''⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', Tr⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 2) S'' Tr := by simpa using SR.drop 2 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨m2, within2, hmem2, hb2, hat2, hrun2⟩ :=
          keccak_dynR I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        obtain ⟨-, hkec⟩ := (O_ok c T).1 henv
        rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hat2
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - 1) [] (some false :: ty'.drop 2) (k' - 1)
          ((O T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S'')
          ((O T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: Tr)
          { s' with memory := s'.memory.expand x.toNat y.toNat } (pc' + 1) _ _ st' ss' T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.effect .keccak256 2 :: rest) _ s' = r
          rw [exec_keccakC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

      · -- LOGn at the frame's gas, of any range.
        obtain ⟨nl, hn4, rfl⟩ := isLogI_eq hlgi
        obtain ⟨hk1, hnh, hdat, htop', hok3⟩ := blockOkC_log hn4 hok2
        have hs := I'.seg
        rw [lowerInstrs_log p c b hn4, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, S1⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', T1⟩⟩
        · simp at hL
        · simp at hL
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨tops, S2, rfl, hlen⟩ : ∃ tops S2, S1 = tops ++ S2 ∧ tops.length = nl :=
          ⟨S1.take nl, S1.drop nl, (List.take_append_drop nl S1).symm, by simp; omega⟩
        obtain ⟨tops', T2, rfl, hlen'⟩ : ∃ tops' T2, T1 = tops' ++ T2 ∧ tops'.length = nl :=
          ⟨T1.take nl, T1.drop nl, (List.take_append_drop nl T1).symm, by simp; omega⟩
        subst hlen
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.cons.injEq, List.take_left' hlen',
          List.take_left' rfl] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        have hR'' : SR c (ty'.drop (tops.length + 2)) S2 T2 := by
          simpa using SR.drop (tops.length + 2) hR'
        simp only [List.length_append] at hL hst hh2 hu2
        obtain ⟨m2, within2, hmem2, hb2, hat2, hrun2⟩ :=
          log_dynR (n := ⟨tops.length, by omega⟩) I'.mem hmB (by omega) hatm rfl hlt hcode
            (decode_log ⟨tops.length, by omega⟩) hstatic within1 hrm hok
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨L, hL1, hL2⟩ := R'.logs
        obtain ⟨T2', r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) (ss0 := ss0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - (tops.length + 2)) [] (ty'.drop (tops.length + 2))
          (k' - 1) S2 T2
          ⟨s'.memory.expand x.toNat y.toNat, s'.storage, s'.transient,
            s'.world ++ [.log tops ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩
          (pc' + 1) _ _ st' { ss' with logs := ss'.logs.push ⟨msg.currentTarget,
            tops.map U256.toBeBytes, memoryReadBytes (memoryExtend M' (extendMemory M'.size
              [(x, y)]).expandBy) x.toNat y.toNat⟩ } T m2 within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2
          ⟨R'.storage, R'.account, ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy)
                x.toNat y.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, read_eq I'.mem⟩⟩⟩ hat2
          (by show T.gases.length = gasReads (s'.world ++ [_]); rw [AssembleCut.gasReads_log, hc1.1]; exact hTg)
          (by show sent (s'.world ++ [_]) = 0; rw [AssembleCut.sent_log, hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2', r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b
            (.effect (.log tops.length) (tops.length + 2) :: rest) _ s' = r
          rw [exec_logC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

      · -- CALLDATACOPY at the frame's gas, of any range.
        obtain rfl := isCdcI_eq hcdi
        obtain ⟨hk1, hh1, hdat, htop', hok3⟩ := blockOkC_cdc hok2
        have hs := I'.seg
        rw [lowerInstrs_cdc, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, _ | ⟨z, S''⟩⟩⟩
        · simp at hh2; omega
        · simp at hh2; omega
        · simp at hh2; omega
        rcases T' with _ | ⟨x', _ | ⟨y', _ | ⟨z', Tr⟩⟩⟩
        · simp at hL
        · simp at hL
        · simp at hL
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 3) S'' Tr := by simpa using SR.drop 3 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨M2, g2, m2, within2, hmem2, hb2, hg2, hat2, hrun2⟩ :=
          cdc_dynR hdata I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segR (G0 := G0) (ss0 := ss0) G hnc hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 n rest (h' - 3) [] (ty'.drop 3) (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => SolarTV.Machine.calldataByte call (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.effect .calldatacopy 3 :: rest) _ s' = r
          rw [exec_cdcC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩
      · -- STATICCALL: only a certificate that says the program makes calls lets the checker cut there.
        obtain rfl := isScI_eq hsci
        exact absurd (blockOkC_sc hok2).1 (by simp [hnc])
      · obtain rfl := isRdsI_eq hrdi
        exact absurd (blockOkC_rds hok2).1 (by simp [hnc])
      · obtain rfl := isRdcI_eq hrdci
        exact absurd (blockOkC_rdc hok2).1 (by simp [hnc])
      · -- CALL, CREATE2 and CODECOPY: only a certificate that says the program creates lets the
        -- checker cut there.
        obtain rfl := isCallI_eq hcalli
        exact absurd (blockOkC_call hok2).1 (by simp [hnc])
      · obtain rfl := isC2I_eq hc2i
        exact absurd (blockOkC_c2 hok2).1 (by simp [hnc])
      · obtain rfl := isCcI_eq hcci
        exact absurd (blockOkC_cc hok2).1 (by simp [hnc])

/-- `AssembleRun.Advances` for a run that ends with no error or reverts. -/
def AdvancesR {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
    (O : RunTable → Oracle) (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets (fun _ _ _ => True) runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      OkR fin →
      ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

theorem AdvancesR.advances {σ : Type} {blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ)}
    {O : RunTable → Oracle} {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    {T : RunTable} {x : σ} {evm : Evm .fusaka Nat} (h : AdvancesR blk O E Post meas T x evm) :
    Advances blk O E Post meas T x evm :=
  fun bound runChild meets within fin hrun hok => h bound runChild meets within fin hrun (.inl hok)

/-- `AssembleRun.run_of_advances` for a run that ends with no error or reverts. -/
theorem run_of_advancesR {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
    (O : RunTable → Oracle) {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → AdvancesR blk O E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets (fun _ _ _ => True) runChild) :
    ∀ (n : Nat) (T : RunTable) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      OkR fin →
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
        run_of_advancesR blk O adv meets n T' y after within' fin hE' (by omega) hrun' hok
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [iterate, hstep T'' (hle2.trans h), hk]⟩

/-- **A block of code with loops and GAS, read back from a run that succeeds.** -/
theorem advances_checkCR {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobC p c mx code) (hnc : c.calls = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntT p c mx code msg ss0 T0 x evm) :
    AdvancesR (fun o => SolarTV.EVM.Program.block o call p) O (EntT p c mx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p c e.gas y.1) T0 x evm := by
  intro bound runChild _ within fin hrun hok
  obtain ⟨b, S, s⟩ := x
  obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hbud⟩ := hE
  simp only at hle hneed hR hseg hmem R hTg hs0
  by_cases hb : b < p.blocks.length
  · obtain ⟨hL, hnm, hstk, hblock⟩ := G.block b hb
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
      · simp only [ht, ite_true, List.singleton_append, List.cons_append] at hseg
        obtain ⟨next, hd, hseg'⟩ := hseg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hp := hat.addGas 1
        obtain ⟨e1, r1, he1⟩ := Logic.jumpdestG hlt hcode (show 1 ≤ evm.gas + 1 by omega) _ hp
        obtain ⟨m, within', hz, hrm⟩ := reaches_lowAt r1 1 evm rfl hat within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hgm⟩ := at_of_addGasR he1
        exact ⟨pc + 1, m, within', hatm, hseg', by simp only [ht, ite_true]; omega, hrm⟩
      · simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at hseg
        exact ⟨pc, evm, within, hat, hseg, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          hrun⟩
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := segR (G0 := msg.gas) G.toGlobT hnc hdata hvalue hstatic hself hcaller
      hbenv htx hb hok hgas (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) (KR.nil _) hR hseg1 (by omega) htop hmem R hat1 hTg hs0
      (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨T', r, hle', fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T'' h]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj⟩, after, within', hE', hT', hs', hga, hbud', hra⟩ := hnext _ hy
      refine ⟨after, within', ⟨hE', hT', hs', hbud'⟩, ?_, hra⟩
      have := meas_step (c := c) (g := evm.gas) (g' := after.gas) hb htle (by omega) hj
      dsimp only at this ⊢
      omega
  · obtain rfl : b = p.blocks.length := by omega
    have hblk : p.blocks[p.blocks.length]? = none := List.getElem?_eq_none (by omega)
    have hbl : ∀ o, SolarTV.EVM.Program.block o call p (p.blocks.length, S, s) =
        some (.inl (.stop, s)) := by
      intro o
      simp only [SolarTV.EVM.Program.block, hblk, ite_true]
    refine ⟨T0, _, RunTable.Le.refl T0, fun _ _ => hbl _, ?_, ?_⟩
    · intro res hres
      cases hres
      have hseg' := hseg
      rw [lowerFrom_nil p c (by omega)] at hseg'
      have hpc := hseg'.nil_end
      exact lowAt (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy


/-- `AssembleRun.processMessage_ok'` for a run that ends with any error: the frame the interpreter
runs under its runner of messages, whose error and output the message ends with. -/
theorem processMessage_frameP {message : Message .fusaka}
    (hpre : precompileAddress .fusaka message = none) {st : EthLib.Execution.State.TransactionState} {ss : Substate} {evm}
    (hr : processMessage (Meter := Nat) .fusaka message st ss = .ok evm) :
    ∃ (st' : EthLib.Execution.State.TransactionState) (ss' : Substate)
      (within : GasMeter.gasHeld (startFrame message st' ss' message.gas).gas ≤ message.gas)
      (fr : Evm .fusaka Nat),
      (¬ (message.shouldTransferValue = true ∧ message.value ≠ 0) → st' = st ∧ ss' = ss) ∧
      ((message.shouldTransferValue = true ∧ message.value ≠ 0) →
        st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st' ∧
        ss' = { ss with logs := (pushTransferLog .fusaka ss.logs message.caller message.currentTarget
          message.value) }) ∧
      runFrame (step .fusaka) (step_decreases .fusaka) message.gas
        (processRunner .fusaka message.gas) (startFrame message st' ss' message.gas) within =
          .ok fr ∧
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
        exact ⟨st', _, _, _, fun h => absurd htr h, fun _ => ⟨rfl, rfl⟩, hrf,
          AssembleLoop.error_rollbackOnError _ _, AssembleLoop.output_rollbackOnError _ _⟩
  · simp only [htr, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hr
    split at hr
    · simp [throw, throwThe, MonadExceptOf.throw, Except.map] at hr
    · rename_i after hrf
      simp only [Except.map, Except.ok.injEq] at hr
      subst hr
      simp only [htr, ↓reduceIte] at hrf
      exact ⟨st, ss, _, _, fun _ => ⟨rfl, rfl⟩, fun h => absurd h htr, hrf,
        AssembleLoop.error_rollbackOnError _ _, AssembleLoop.output_rollbackOnError _ _⟩

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **`AssembleRun.within_of_advances` with the revert data related**: when every frame related to a
block state advances in a run that ends with no error or reverts, the oracle of the run's table
makes every result of the bytecode on the call the EVM IR's, unless the run halted exceptionally. -/
theorem within_of_advancesR {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesR (fun o => block o call p) O (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, WithinR (evmirSem (O T)) gas p code (· = call) := by
  cases hrunE : Target.runWith gas code call with
  | none =>
    refine ⟨{}, fun call' hc obs h => ?_⟩
    subst hc
    rw [hrunE] at h
    cases h
  | some obs =>
  have hrun0 := hrunE
  unfold Target.runWith Target.runMsg at hrunE
  split at hrunE
  · cases hrunE
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrunE
  by_cases hex : ∃ e, e ≠ EvmError.revert ∧ evm.error = some e
  · obtain ⟨e, hne, he'⟩ := hex
    have hs : obs.success = false := by rw [← hrunE]; simp [he']
    have hfail := Target.runWith_failure hrun0 hs
    have hh : HaltsExceptionally gas code call := ⟨⟨evm, hev⟩, hpm, e, hne, he'⟩
    refine ⟨{}, fun call' hc obs' h => ?_⟩
    subst hc
    rw [hrun0] at h
    cases h
    exact Or.inr ⟨hh, hs, hfail⟩
  rcases herrc : evm.error with _ | e
  · obtain ⟨T, hT⟩ := within_of_advances O E meas start
      (fun ss0 T x evm h => (adv ss0 T x evm h).advances)
    have hsucc : obs.success = true := by rw [← hrunE]; simp [herrc]
    refine ⟨T, fun call' hc obs' h => ?_⟩
    rcases hT call' hc obs' h with h' | ⟨hs, -⟩
    · exact .inl h'
    · subst hc
      rw [hrun0] at h
      cases h
      rw [hsucc] at hs
      cases hs
  have hrev : e = .revert := by
    by_contra hne
    exact hex ⟨e, hne, herrc⟩
  subst hrev
  obtain ⟨st', ss', within, fr, hcases, hmove, hrf, herrfr, houtfr⟩ :=
    processMessage_frameP (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm
  simp only at herrfr houtfr
  have hfrrev : fr.error = some .revert := by rw [← herrfr, herrc]
  have R := AssembleLoop.rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advancesR (fun o => block o call p) O (adv ss')
    (meets_process .fusaka _) _ {} _ _ within fr (start st' ss' R) (Nat.lt_succ_self _) hrf
    (.inr hfrrev)
  obtain ⟨k, hk⟩ := hit T (RunTable.Le.refl T)
  have hres : (evmirSem (O T)).run p call = some (observe call sF halt) := by
    change (SolarTV.EVM.Program.layer.result (O T) p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨k, hk⟩]
    rfl
  obtain ⟨ssF, ⟨herr, hout, -, -⟩, -⟩ := hpost
  have hfinal : (evmirSem (O T)).run p call = some obs := by
    rw [hres, ← hrunE]
    have herr' : fr.error = errorOf (observe call sF halt) := herr
    have hout' : fr.output.toList.map (·.toNat) = (observe call sF halt).output := hout
    have hfail : (observe call sF halt).success = false →
        (observe call sF halt).logs = [] ∧
        (observe call sF halt).storage = slotValue call.storage := by
      cases halt <;> simp [observe]
    clear herr hout hres hit hk
    generalize observe call sF halt = X at *
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
  refine ⟨T, fun call' hc obs' h => ?_⟩
  subst hc
  rw [hrun0] at h
  cases h
  exact .inl hfinal

/-- **EVM IR to bytecode, run by run, for code with loops, GAS and memory at any offset, with the
revert data related**: for every program the checker with GAS accepts, at every gas below
`2 ^ 256` and every call, the oracle of the run's table makes every result of the bytecode the EVM
IR's (a revert with its data among them), unless the run halted exceptionally. -/
theorem runs_of_checkCR {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkC p code c mx = true) (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) :
    ∃ T, WithinR (evmirSem (O T)) gas p code (· = call) := by
  obtain ⟨hcb, hnc⟩ := checkC_base hc
  obtain ⟨G, hseg, hneed0⟩ := globC_of_checkC hcb
  refine within_of_advancesR O
    (fun ss0 => EntT p c mx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p c e.gas y.1) (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkCR G hnc rfl
      (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl rfl rfl hgas T x evm hE)
  refine ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hneed0], by simp⟩,
    SR.nil c _, by rw [List.drop_zero]; exact hseg, by simp, memRel_initial, R, ?_⟩, rfl, rfl, ?_⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- **The per-run theorem with the revert data related**, below `2 ^ 256` gas, for every program
the checker with GAS accepts: an oracle meeting the certificate's constraints for each run. -/
theorem withinRunR_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert}
    {mx : List Nat} (hc : checkC p code c mx = true) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, ∃ o, CertOk c o ∧
      WithinR (evmirSem o) gas p code (· = call) := by
  intro gas hgas call
  obtain ⟨T, hT⟩ := runs_of_checkCR hc gas hgas call
  exact ⟨O T, O_ok c T, hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertCut.withinRunR_of_checkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRunR_of_checkC

/-- `AssembleCut.WithinRunLt` with the revert data related (`AssembleLoop.WithinR`). -/
def WithinRunLtR (sem : Oracle → Sem) (p : ∀ o, (sem o).Prog) (code : ByteArray)
    (scope : Call → Prop) (Ok : Oracle → Prop) : Prop :=
  ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ o, Ok o ∧
    WithinR (sem o) gas (p o) code (· = call)

/-- `WithinRunLtR` gives `AssembleCut.WithinRunLt`. -/
theorem WithinRunLtR.withinRunLt {sem : Oracle → Sem} {p : ∀ o, (sem o).Prog} {code : ByteArray}
    {scope : Call → Prop} {Ok : Oracle → Prop} (h : WithinRunLtR sem p code scope Ok) :
    WithinRunLt sem p code scope Ok := by
  intro gas hgas call hc
  obtain ⟨o, ho, hw⟩ := h gas hgas call hc
  exact ⟨o, ho, hw.within⟩

/-- Stages read backwards before a per-run refinement with the revert data related give one from
the earlier program. -/
theorem WithinRunLtR.of_back {A sem : Oracle → Sem} {q : ∀ o, (A o).Prog} {p : ∀ o, (sem o).Prog}
    {code : ByteArray} {scope : Call → Prop} {Ok : Oracle → Prop}
    (back : ∀ o, Ok o → Stage (sem o) (A o) (p o) (q o) scope)
    (h : WithinRunLtR sem p code scope Ok) : WithinRunLtR A q code scope Ok := by
  intro gas hgas call hc
  obtain ⟨o, ho, hw⟩ := h gas hgas call hc
  refine ⟨o, ho, fun call' h' obs hrun => ?_⟩
  subst h'
  rcases hw call' rfl obs hrun with e | e
  · exact Or.inl (back o ho call' hc obs e)
  · exact Or.inr e

/-- **The per-run theorem with the revert data related** on a scope, for every program the checker
with GAS accepts. -/
theorem withinRunLtR_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert}
    {mx : List Nat} (hc : checkC p code c mx = true) (scope : Call → Prop) :
    WithinRunLtR evmirSem (fun _ => p) code scope (CertOk c) :=
  fun gas hgas call _ => withinRunR_of_checkC hc gas hgas call

/-- **The first lowered MIR to the exact bytecode, run by run, with the revert data related**: the
backend stages read backwards and the checker with GAS give, for every gas below `2 ^ 256` and
every call, an oracle meeting the certificate's constraints under which every result of the
bytecode is the first lowered MIR's (a revert with its data among them), unless the run halted
exceptionally. -/
theorem withinRunR_mir_of_checkC {stage0 : SolarTV.MIR.Lowered.moduleLayer.Prog}
    {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {S scope : Call → Prop}
    (back : ∀ o, Certified SolarTV.EVM.Program.layer SolarTV.MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call) (hc : checkC p code c mx = true) :
    WithinRunLtR mirSem (fun _ => stage0) code scope (CertOk c) :=
  WithinRunLtR.of_back (fun o _ => fun call hcall obs h =>
      stage_of_certified (back o) call (hS call hcall) obs h)
    (withinRunLtR_of_checkC hc scope)

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertCut.withinRunR_mir_of_checkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRunR_mir_of_checkC

end SolidCore.Refinement.Solar.AssembleRevertCut

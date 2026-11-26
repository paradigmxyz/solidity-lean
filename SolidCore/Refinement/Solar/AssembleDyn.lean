import SolidCore.Refinement.Solar.AssembleCutSim

/-!
# Memory at offsets the checker does not know

SolarTV counts the active words of memory in `BitVec 251`, so growth to an offset `o` with
`o + size + 31 ≥ 2 ^ 256` wraps there and not in EthLib. A run that succeeds never grows memory that
far: every growth is paid for, and the price of memory and the gas left never exceed what the frame
holds at the start of a block plus a fixed reserve (`MemBudget`). With that reserve below `2 ^ 300`, the
price `3 w + w² / 512` of `w` words keeps `w` below `2 ^ 155` (`words_lt_of_cost`), far from the
wrap.

* `budget_grow`: one paid growth of memory keeps the budget and bounds the range it grows to.
* `memRel_expandW`, `memRel_storeW`: `Assemble.memRel_expand` and `memRel_store` for any range whose
  words SolarTV holds, without the `2 ^ 32` bound of the constant-offset checker.
* `mstore_back`, `mload_back`: MSTORE and MLOAD at the frame's own gas in a run that succeeds (the
  frame had the gas for the growth), and `mstore_dyn`, `mload_dyn`: at any offset, SolarTV's
  memory after them agrees with EthLib's and the budget holds, with no bound on the offset.
-/

namespace SolidCore.Refinement.Solar.AssembleDyn

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

variable {rd : ByteArray}

/-! ## Gas bounds memory -/

/-- **A paid growth of memory keeps the budget**: when the frame pays `pre` and the growth for a
nonempty range, the range's price is within the budget, and so are the grown memory's price and the
gas left. -/
theorem budget_grow {size g G pre : Nat} (hmod : size % 32 = 0) {o sz : Word} (hz : sz ≠ 0)
    (hb : memoryGasCost size + g ≤ G) (hg : pre + (extendMemory size [(o, sz)]).cost ≤ g) :
    memoryGasCost (o.toNat + sz.toNat) ≤ G ∧
    memoryGasCost (size + (extendMemory size [(o, sz)]).expandBy) +
      (g - (pre + (extendMemory size [(o, sz)]).cost)) ≤ G := by
  by_cases h : size < o.toNat + sz.toNat
  · rw [extendMemory_of_lt' hmod hz h] at hg ⊢
    simp only at hg ⊢
    have hup := le_ceil32 (o.toNat + sz.toNat)
    have hc := memoryGasCost_ceil32 (o.toNat + sz.toNat)
    have hm := memoryGasCost_mono (show size ≤ ceil32 (o.toNat + sz.toNat) by omega)
    refine ⟨by omega, ?_⟩
    rw [show size + (ceil32 (o.toNat + sz.toNat) - size) = ceil32 (o.toNat + sz.toNat) by omega]
    omega
  · rw [extendMemory_of_le' (by omega)] at hg ⊢
    simp only at hg ⊢
    have := memoryGasCost_mono (show o.toNat + sz.toNat ≤ size by omega)
    refine ⟨by omega, ?_⟩
    rw [Nat.add_zero]
    omega

/-! ## An instruction at the frame's own gas, in a run that succeeds -/

/-- The meter fails a charge above the gas left. -/
theorem charge_oog {g c : Nat} (h : g < c) : GasMeter.charge g c = .error .outOfGas := by
  simp only [GasMeter.charge]
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- **A run that succeeds never halts out of gas**: no frame of it meets a precondition from which
the frame halts out of gas. -/
theorem oog_absurd {P : Evm .fusaka Nat → Prop} {st : State.TransactionState} {ss : Substate}
    (hspec : Spec .fusaka P (Faulted .outOfGas st ss)) {evm : Evm .fusaka Nat} (hp : P evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) : False := by
  obtain ⟨z, hr, hstop, hf⟩ := hspec evm hp
  rw [runFrame_of_reaches hr hstop within] at hrun
  cases hrun
  rw [hf.2.1] at hok
  cases hok

/-- **An instruction in a run that succeeds**: when with gas `c` it goes on to `Q` and with less
its step halts out of gas, the frame had `c`, and the run goes on from a frame of `Q`. -/
theorem back_of_step {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {S : List Word}
    {M : ByteArray} {g c : Nat} {st : State.TransactionState} {ss : Substate}
    {Q : Evm .fusaka Nat → Prop}
    (hgo : c ≤ g → Hoare .fusaka (At code msg pc S M g st ss rd) Q)
    (hfault : g < c → ∀ e, At code msg pc S M g st ss rd e → step .fusaka e = .error .outOfGas)
    {evm : Evm .fusaka Nat} (hat : At code msg pc S M g st ss rd evm) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    c ≤ g ∧ ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound), Q m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : c ≤ g
  · obtain ⟨m, hr, hm⟩ := hgo hg evm hat
    rw [runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within]
      at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exact (oog_absurd (At.fault rfl (hfault (Nat.lt_of_not_le hg))) hat within hrun hok).elim

/-- **A paid growth of memory at any range**: with the budget below `2 ^ 300`, SolarTV's growth
agrees with EthLib's memory after it and the budget holds at the gas left. -/
theorem grow_dyn {M : ByteArray} {g G pre : Nat} {o sz : Word} {m0 : SolarTV.Machine.Mem}
    (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hg : pre + (extendMemory M.size [(o, sz)]).cost ≤ g) :
    MemRel (m0.expand o.toNat sz.toNat) (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) ∧
      MemBudget G (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (pre + (extendMemory M.size [(o, sz)]).cost)) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  refine ⟨memRel_expandW hm ?_, MemBudget.grow hmod hb hg (size_memoryExtend M _)⟩
  by_cases hz : sz = 0
  · exact .inl hz
  · exact .inr (words_lt_of_cost (budget_grow hmod hz hb hg).1 hG)

/-! ## MSTORE and MLOAD at the frame's own gas -/

/-- **MSTORE in a run that succeeds**: the frame had the gas for it and its growth of memory, and
the run goes on from the frame after it. -/
theorem mstore_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o v : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: v :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
          (wordBytes v))
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  refine back_of_step (fun hg => Logic.mstore hlt hbyte hg) (fun hg e hat' => ?_) hat within hrun
    hok
  obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
  subst hcode hpc
  have hc : GasMeter.charge e.gas (OPCODE_MSTORE_BASE + (extendMemory e.memory.size [(o, 32)]).cost)
      = .error .outOfGas := by rw [hgas, hmem]; exact charge_oog hg
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode rfl (Fork.frontier_le _))
    instruction_mstore, mstoreStep_cons hst]
  simp only [hc]
  rfl

/-- **MLOAD in a run that succeeds**: the frame had the gas for it and its growth of memory, and
the run goes on from the frame after it. -/
theorem mload_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat 32) 0 32 :: T)
        (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy)
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  refine back_of_step (fun hg => Logic.mload hlt hbyte hg) (fun hg e hat' => ?_) hat within hrun
    hok
  obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
  subst hcode hpc
  have hc : GasMeter.charge e.gas (OPCODE_MLOAD_BASE + (extendMemory e.memory.size [(o, 32)]).cost)
      = .error .outOfGas := by rw [hgas, hmem]; exact charge_oog hg
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode rfl (Fork.frontier_le _))
    instruction_mload, mloadStep_cons hst]
  simp only [hc]
  rfl

/-! ## RETURN and REVERT at the frame's own gas -/

/-- **RETURN in a run that succeeds**: the frame had the gas for the growth of memory to its
range. -/
theorem return_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    (extendMemory M.size [(o, sz)]).cost ≤ g := by
  refine Nat.le_of_not_lt fun hg => oog_absurd (At.fault rfl fun e hat' => ?_) hat within hrun hok
  obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
  subst hcode hpc
  have hc : GasMeter.charge e.gas (extendMemory e.memory.size [(o, sz)]).cost =
      .error .outOfGas := by rw [hgas, hmem]; exact charge_oog hg
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode rfl (Fork.frontier_le _))
    instruction_return, returnStep_cons hst]
  simp only [hc]
  rfl

/-- **No run that succeeds reaches REVERT**: REVERT stops the frame with the revert error, or with
too little gas for its range, out of gas. -/
theorem revert_false {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) : False := by
  by_cases hg : (extendMemory M.size [(o, sz)]).cost ≤ g
  · have hspec := Logic.revertG (fork := .fusaka) (by decide) (message := msg) (state := st)
      (substate := ss) (returnData := rd) (rest := T) hlt hbyte (show _ ≤ g + 0 by omega)
    have hf := SpecG.low hspec (hat.addGas 0) within hrun hok
    have h2 : fin.error = some .revert := by simpa [addGas] using hf.2.1
    rw [h2] at hok
    cases hok
  · refine oog_absurd (At.fault rfl fun e hat' => ?_) hat within hrun hok
    obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
    subst hcode hpc
    have hc : GasMeter.charge e.gas (extendMemory e.memory.size [(o, sz)]).cost =
        .error .outOfGas := by rw [hgas, hmem]; exact charge_oog (Nat.lt_of_not_le hg)
    rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode rfl (by decide))
      (instruction_revert (by decide)), revertStep_eq, returnStep_cons hst]
    simp only [hc]
    rfl

/-! ## KECCAK256 at the frame's own gas -/

/-- **KECCAK256 in a run that succeeds**: the frame had the gas for the hash and the growth of
memory to its range, and the run goes on from the frame after it. -/
theorem keccak_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (keccak (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
          o.toNat sz.toNat) :: T)
        (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  refine back_of_step (fun hg => Logic.keccak256 hlt hbyte hg) (fun hg e hat' => ?_) hat within
    hrun hok
  obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
  subst hcode hpc
  have hc : GasMeter.charge e.gas (keccak256Cost sz +
      (extendMemory e.memory.size [(o, sz)]).cost) = .error .outOfGas := by
    rw [hgas, hmem]; exact charge_oog hg
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode rfl (Fork.frontier_le _))
    instruction_keccak256, keccak256Step_cons hst]
  simp only [hc]
  rfl

/-- **KECCAK256 of any range, in a run that succeeds**: with the budget below `2 ^ 300`,
SolarTV's growth agrees with EthLib's memory after it, the budget holds at the gas left, and the run
goes on. -/
theorem keccak_dyn {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
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
  obtain ⟨hg, m, within', hat', hrun'⟩ := keccak_back hat hlt hbyte within hrun hok
  exact ⟨m, within', (grow_dyn hm hb hG hg).1, (grow_dyn hm hb hG hg).2, hat', hrun'⟩

/-! ## LOGn at the frame's own gas -/

/-- **LOGn in a run that succeeds**: the frame had the gas for the log and the growth of memory
to its range, and the run goes on from the frame after it, with the log appended. -/
theorem log_back {n : Fin 5} {byte : UInt8} {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {o sz : Word} {words T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} {evm : Evm .fusaka Nat}
    (hat : At code msg pc (o :: sz :: (words ++ T)) M g st ss rd evm)
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : msg.isStatic = false) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
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
  refine back_of_step (fun hg => Logic.log hlen hlt hbyte decoded hstatic hg)
    (fun hg e hat' => ?_) hat within hrun hok
  obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
  subst hcode hpc
  rw [step_of_instruction hlt (by rw [hbyte]; exact ofByte_of_decode decoded (Fork.frontier_le _))
    (instruction_log n)]
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

/-- **LOGn of any range, in a run that succeeds**: with the budget below `2 ^ 300`, SolarTV's
growth agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on
with the log appended. -/
theorem log_dyn {n : Fin 5} {byte : UInt8} {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {o sz : Word} {words T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState}
    {ss : Substate} {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g)
    (hG : G < 2 ^ 300) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (o :: sz :: (words ++ T)) M g st ss rd evm)
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : msg.isStatic = false) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
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
  obtain ⟨hg, m, within', hat', hrun'⟩ := log_back hat hlen hlt hbyte decoded hstatic within hrun hok
  exact ⟨m, within', (grow_dyn hm hb hG hg).1, (grow_dyn hm hb hG hg).2, hat', hrun'⟩

/-! ## At any offset -/

/-- **MSTORE at any offset, in a run that succeeds**: with the budget below `2 ^ 300`, SolarTV's
store agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on. -/
theorem mstore_dyn {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o v : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: v :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.store o.toNat v) M' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := mstore_back hat hlt hbyte within hrun hok
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
theorem mload_dyn {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o : Word}
    {T : List Word} {M : ByteArray} {g G : Nat} {st : State.TransactionState} {ss : Substate}
    {m0 : SolarTV.Machine.Mem} (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.expand o.toNat 32) M' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) (m0.load o.toNat :: T) M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := mload_back hat hlt hbyte within hrun hok
  rw [load_eq hm] at hat'
  exact ⟨_, _, m, within', (grow_dyn hm hb hG hg).1, (grow_dyn hm hb hG hg).2, by omega, hat', hrun'⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleDyn.mstore_dyn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mstore_dyn

/-- info: 'SolidCore.Refinement.Solar.AssembleDyn.mload_dyn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mload_dyn

end SolidCore.Refinement.Solar.AssembleDyn

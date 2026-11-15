import SolidCore.Refinement.Solar.AssembleDynCopy

/-!
# CODECOPY of the frame's code at the frame's own gas

CODECOPY copies a range of the code that runs to memory, with zeros past its end. In SolarTV the
bytes come from the oracle's read `code` (`SolarTV.Machine.codeByte`), so the bytecode's CODECOPY
is SolarTV's under an oracle whose reads are the bytes of that code (`CodeOk`); every oracle has a
form that meets it (`codeOracle_ok`).

* `codecopy_back`: a CODECOPY in a run that succeeds had the gas for the copy and the growth of
  memory, and the run goes on from the frame after it (EthLib's `Logic.codecopy`).
* `codecopy_dyn`: with the budget of a frame below `2 ^ 256` gas and a code offset below `2 ^ 32`
  (a constant the checker reads), SolarTV's copy agrees with EthLib's memory after it at any
  destination and size. SolarTV's read takes its index as a word, so an offset near `2 ^ 256`
  would wrap where EthLib reads zeros: the bound on the offset excludes that, and the budget bounds
  the size by `2 ^ 140` (`size_le_of_cost`).
-/

namespace SolidCore.Refinement.Solar.AssembleCodeCopy

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleDyn SolidCore.Refinement.Solar.AssembleEffects
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

variable {rd : ByteArray}

/-! ## The oracle's reads of the code -/

/-- The oracle reads the frame's code: byte `w` of `code` at every word `w`, zero past its end. -/
def CodeOk (o : Oracle) (code : ByteArray) : Prop :=
  ∀ w : Word, (o.env "code" [] [w]).setWidth 8 = (byteAt code w.toNat).toBitVec

/-- Any oracle, with the reads of `code`. -/
def codeOracle (code : ByteArray) (o : Oracle) : Oracle :=
  { o with env := fun name w args =>
      if name = "code" ∧ w = [] then
        match args with
        | [a] => BitVec.ofNat 256 (byteAt code a.toNat).toNat
        | _ => o.env name w args
      else o.env name w args }

theorem setWidth_ofNat_byte (x : UInt8) : (BitVec.ofNat 256 x.toNat).setWidth 8 = x.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have hx := UInt8.toNat_lt x
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 256), Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 8)]

/-- `CodeOk` is no vacuous hypothesis: every oracle has a form that meets it. -/
theorem codeOracle_ok (code : ByteArray) (o : Oracle) : CodeOk (codeOracle code o) code := by
  intro w
  simp only [codeOracle, and_self, ite_true]
  exact setWidth_ofNat_byte _

/-- The other reads of `codeOracle` are the oracle's. -/
theorem codeOracle_env (code : ByteArray) (o : Oracle) {name : String} (h : name ≠ "code")
    (w : List Event) (args : List Word) : (codeOracle code o).env name w args = o.env name w args := by
  simp [codeOracle, h]

/-- SolarTV's byte of the code at an index below `2 ^ 256` is EthLib's. -/
theorem codeByte_eq {o : Oracle} {code : ByteArray} (hc : CodeOk o code) {i : Nat} (hi : i < 2 ^ 256) :
    codeByte o i = (byteAt code i).toBitVec := by
  unfold codeByte
  rw [hc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-! ## CODECOPY in a run that succeeds -/

/-- **CODECOPY in a run that succeeds**: the frame had the gas for the copy and the growth of
memory, and the run goes on from the frame after it. -/
theorem codecopy_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat ⟨(bufferRead code off.toNat sz.toNat).toArray⟩)
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.codecopy (fork := .fusaka) hlt hbyte hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .codecopy := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded instruction_codecopy]
      rw [copyToMemory_cons hst]
      have hlt' : g < 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost :=
        Nat.lt_of_not_le hg
      have hc : GasMeter.charge e.gas (OPCODE_CODECOPY_BASE + OPCODE_COPY_PER_WORD *
          wordCount sz.toNat + (extendMemory e.memory.size [(d, sz)]).cost) = .error .outOfGas := by
        rw [hgas, hmem, show OPCODE_CODECOPY_BASE = 3 from rfl,
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

/-- A copy the budget of a frame below `2 ^ 256` gas pays for has at most `2 ^ 140` bytes. -/
theorem size_le_of_budget {M : ByteArray} {g G pre : Nat} (hmod : M.size % 32 = 0) {d sz : Word}
    (hz : sz ≠ 0) (hb : MemBudget G M g) (hG : G < 2 ^ 256)
    (hg : pre + (extendMemory M.size [(d, sz)]).cost ≤ g) : d.toNat + sz.toNat ≤ 2 ^ 140 := by
  have h1 := (budget_grow hmod hz hb hg).1
  rw [← memoryGasCost_ceil32] at h1
  have h2 := size_le_of_cost h1 hG (by rw [ceil32_eq]; omega)
  have := le_ceil32 (d.toNat + sz.toNat)
  omega

/-- **CODECOPY of any range, in a run that succeeds**: with the budget of a frame below `2 ^ 256`
gas and the code offset below `2 ^ 32`, under an oracle that reads the frame's code, SolarTV's copy
agrees with EthLib's memory after it, the budget holds at the gas left, and the run goes on. -/
theorem codecopy_dyn {code : ByteArray} {msg : Message .fusaka} {o : Oracle} (hc : CodeOk o code)
    {pc : Nat} {d off sz : Word} (hoff : off.toNat < 2 ^ 32) {T : List Word} {M : ByteArray}
    {g G : Nat} {st : State.TransactionState} {ss : Substate} {m0 : SolarTV.Machine.Mem}
    (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 256) {evm : Evm .fusaka Nat}
    (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => codeByte o (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hg, m, within', hat', hrun'⟩ := codecopy_back hat hlt hbyte within hrun hok
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hsmall : sz = 0 ∨ d.toNat + sz.toNat ≤ 2 ^ 140 := by
    by_cases hz : sz = 0
    · exact .inl hz
    · exact .inr (size_le_of_budget hmod hz hb hG hg)
  have hbound : sz = 0 ∨ (d.toNat + sz.toNat + 31) / 32 < 2 ^ 251 := by
    rcases hsmall with h | h
    · exact .inl h
    · exact .inr (by omega)
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
    rw [byteAt_bufferRead, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    have hz : sz ≠ 0 := by
      intro h
      subst h
      simp at hi
    have hle := hsmall.resolve_left hz
    rw [codeByte_eq hc (by omega)]
  · refine MemBudget.grow hmod hb hg ?_
    rw [size_memoryWrite_of_fit, size_memoryExtend]
    intro h
    rw [size_bufferRead] at h ⊢
    exact hfit h

/-- **CODECOPY in SolarTV**: the effect writes the oracle's bytes of the code and grows nothing else. -/
theorem codecopy_effect (o : Oracle) (call : Call) (d off sz : Word) (s : SolarTV.Machine.State) :
    Effect.apply o call .codecopy [d, off, sz] s =
      some (none, { s with
        memory := s.memory.write d.toNat sz.toNat (fun i => codeByte o (off.toNat + i)) }) := rfl

/-- info: 'SolidCore.Refinement.Solar.AssembleCodeCopy.codecopy_dyn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codecopy_dyn

/-- info: 'SolidCore.Refinement.Solar.AssembleCodeCopy.codeOracle_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codeOracle_ok

end SolidCore.Refinement.Solar.AssembleCodeCopy

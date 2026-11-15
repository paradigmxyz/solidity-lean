import SolidCore.Refinement.Solar.AssembleCreate
import EthLib.Execution.Proofs.Evm.Logic.Create
import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# CREATE2 at the frame's own gas, from a run that succeeds

`create2_back`: a CREATE2 step in a run of EthLib's interpreter (Fusaka) that ends with no error had
the gas for its price and the growth of memory, its init code is within the limit of EIP-3860, and
the run goes on from the frame after it, in one of three ways, each with every fact the frame gives:

* the creator lacks the value, holds the greatest nonce or is at the greatest depth: no message, 0
  pushed, empty return data;
* the address of EIP-1014 (`AssembleCreate.create2Address_toU256`) holds code or a nonce: no
  message, the creator pays the gas it would pass on and its nonce grows, 0 pushed (EIP-684);
* otherwise the init code runs as a callee at that address, under any runner of messages meeting
  `P`: the frame that ends it meets `P` and the creator pushes the address when it ends with no
  error and 0 otherwise (EthLib's `Logic.create2With`).

Nothing is assumed of the init code: what it does is the callee's frame, which a run's table
records as it records a call's.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateBack

open SolidCore.Refinement.Solar.AssembleCreate
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- **CREATE2 in a run that succeeds.** -/
theorem create2_back {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {value start size salt : U256} {rest : List U256} {evm : Evm .fusaka Nat}
    (hat : At code msg pc (value :: start :: size :: salt :: rest) M g st ss rd evm)
    (hmod : M.size % 32 = 0) (hlt : pc < code.size) (hbyte : code[pc] = 0xf5)
    (hstatic : msg.isStatic = false)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    cost2 M.size start size ≤ g ∧ size.toNat ≤ maxInitCodeSize .fusaka ∧
    ((((st.getAccount msg.currentTarget).balance < value ∨
        (st.getAccount msg.currentTarget).nonce = MAX_NONCE ∨ STACK_DEPTH_LIMIT < msg.depth + 1) ∧
      ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
        At code msg (pc + 1) (0 :: rest)
          (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
          (g - cost2 M.size start size) (st.recordAccountRead msg.currentTarget) ss .empty m ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin) ∨
    (value ≤ (st.getAccount msg.currentTarget).balance ∧
      (st.getAccount msg.currentTarget).nonce ≠ MAX_NONCE ∧ msg.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      st.accountDeployable (create2Address msg.currentTarget salt (memoryReadBytes
        (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) =
        false ∧
      ∃ (st' : State.TransactionState) (m : Evm .fusaka Nat)
        (within' : GasMeter.gasHeld m.gas ≤ bound),
        ((st.recordAccountRead msg.currentTarget).recordAccountRead (create2Address
          msg.currentTarget salt (memoryReadBytes (memoryExtend M
            (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat))).incrementNonce
          .fusaka msg.currentTarget = .ok st' ∧
        At code msg (pc + 1) (0 :: rest)
          (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
          (g - cost2 M.size start size - createMessageGas .fusaka (g - cost2 M.size start size))
          st' { ss with accessedAddresses := ss.accessedAddresses.insert (create2Address
            msg.currentTarget salt (memoryReadBytes (memoryExtend M
              (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) }
          .empty m ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin) ∨
    (value ≤ (st.getAccount msg.currentTarget).balance ∧
      (st.getAccount msg.currentTarget).nonce ≠ MAX_NONCE ∧ msg.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      st.accountDeployable (create2Address msg.currentTarget salt (memoryReadBytes
        (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) =
        true ∧
      ∃ (caller : Evm .fusaka Nat) (m : Message .fusaka) (child after : Evm .fusaka Nat)
        (within' : GasMeter.gasHeld after.gas ≤ bound),
        P caller m child ∧ child.gas ≤ m.gas ∧
        ((st.recordAccountRead msg.currentTarget).recordAccountRead (create2Address
          msg.currentTarget salt (memoryReadBytes (memoryExtend M
            (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat))).incrementNonce
          .fusaka msg.currentTarget = .ok caller.state ∧
        caller.substate = { ss with accessedAddresses := ss.accessedAddresses.insert (create2Address
          msg.currentTarget salt (memoryReadBytes (memoryExtend M
            (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) } ∧
        m.gas = createMessageGas .fusaka (g - cost2 M.size start size) ∧
        m.caller = msg.currentTarget ∧
        m.currentTarget = create2Address msg.currentTarget salt (memoryReadBytes (memoryExtend M
          (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat) ∧
        m.code = memoryReadBytes (memoryExtend M
          (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat ∧
        m.value = value ∧ m.isStatic = false ∧
        At code msg (pc + 1) ((if child.error.isNone then (create2Address msg.currentTarget salt
            (memoryReadBytes (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
              start.toNat size.toNat)).toU256 else 0) :: rest)
          (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
          (g - cost2 M.size start size - createMessageGas .fusaka (g - cost2 M.size start size) +
            child.gas)
          (incorporateChild .fusaka caller child).state
          (incorporateChild .fusaka caller child).substate
          (if child.error.isNone then .empty else child.output) after ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)) := by
  have hat0 := hat
  obtain ⟨hc, hj, hm, hpc, hst, hmem, hgas, hrunning, herr, hout, hs, hss, hrd⟩ := hat0
  have hlt' : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
  have decoded : Op.ofByte .fusaka (evm.code[evm.pc]'hlt') = some .create2 := by
    have he : evm.code[evm.pc]'hlt' = code[pc]'hlt := by subst hc hpc; rfl
    rw [he, hbyte]
    exact ofByte_of_decode rfl (by decide)
  have hstep : step .fusaka evm = createStep true evm :=
    step_of_messageInstruction hlt' decoded instruction_create2
      (messageInstruction_create2 (by decide))
  have hmod' : evm.memory.size % 32 = 0 := by rw [hmem]; exact hmod
  have hst2 : evm.message.isStatic = false := by rw [hm]; exact hstatic
  -- The price, from the run's success.
  have hg : cost2 M.size start size ≤ g := by
    refine Nat.le_of_not_lt fun hlow => ?_
    obtain ⟨e, he⟩ := createStep2_oog (evm := evm) hst (by rw [hmem, hgas]; exact hlow)
    exact error_ne_none_of_stepFails hrunning (by rw [hstep]; exact .inl ⟨e, he⟩) hrun hok
  have hgE : cost2 evm.memory.size start size ≤ evm.gas := by rw [hmem, hgas]; exact hg
  have hinit : size.toNat ≤ maxInitCodeSize .fusaka := by
    refine Nat.le_of_not_lt fun hbig => ?_
    obtain ⟨e, he⟩ := createStep2_big (evm := evm) hst hmod' hgE hbig
    exact error_ne_none_of_stepFails hrunning (by rw [hstep]; exact .inl ⟨e, he⟩) hrun hok
  refine ⟨hg, hinit, ?_⟩
  by_cases hsk : (st.getAccount msg.currentTarget).balance < value ∨
      (st.getAccount msg.currentTarget).nonce = MAX_NONCE ∨ STACK_DEPTH_LIMIT < msg.depth + 1
  · -- No message.
    obtain ⟨after, h1, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, ar, as, ass⟩ :=
      createStep2_skip (evm := evm) hst hst2 hinit hgE (by rw [hs, hm]; exact hsk)
    have hS : Step .fusaka evm after := .next hrunning (by rw [hstep]; exact h1)
    have hrun' := hrun
    rw [runFrame_eq_of_reaches Step.gasHeld_le Step.runFrame_eq (.single hS) within] at hrun'
    refine .inl ⟨hsk, after, _, ⟨by rw [a1, hc], by rw [a2, hj], by rw [a3, hm],
      by rw [a4, hpc], a5, by rw [a6, hmem], by rw [a7, hmem, hgas], by rw [a8, hrunning],
      by rw [a9, herr], by rw [ao, hout], by rw [as, hs, hm], by rw [ass, hss], ar⟩, hrun'⟩
  have hbal : value ≤ (st.getAccount msg.currentTarget).balance := by
    rcases Nat.lt_or_ge (st.getAccount msg.currentTarget).balance.toNat value.toNat with h | h
    · exact absurd (.inl (BitVec.lt_def.mpr h)) hsk
    · exact BitVec.le_def.mpr h
  have hnonce : (st.getAccount msg.currentTarget).nonce ≠ MAX_NONCE := fun h =>
    hsk (.inr (.inl h))
  have hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT := Nat.le_of_not_lt fun h => hsk (.inr (.inr h))
  by_cases hdep : st.accountDeployable (create2Address msg.currentTarget salt (memoryReadBytes
      (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) = true
  · -- The init code runs as a callee.
    have H := (create2With (fork := .fusaka) (callee := P) (rest := rest) (returnData := rd)
      (substate := ss) (state := st) (memory := M) (gas := g) (by decide) (by decide) hlt hbyte hstatic
      (fun _ => hinit) hbal hnonce hdepth rfl hdep (by
        have := hg
        unfold cost2 at this
        simpa [show Fork.fusaka ≥ .shapella by decide] using this))
    obtain ⟨after, hr, hq⟩ := H bound runChild meets evm hat within
    have within' := Nat.le_trans (hr.gasHeld_le StepBy.gasHeld_le) within
    have hrun' := hrun
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hr within] at hrun'
    rcases hq with ⟨caller, m, child, hk, hcg, c1, c2, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10,
      hat'⟩ | aborted
    · refine .inr (.inr ⟨hbal, hnonce, hdepth, hdep, caller, m, child, after, within', hk, hcg, c1,
        c2, ?_, m2, m4, m6, m8, m10, ?_, hrun'⟩)
      · rw [m1]; unfold cost2; simp [show Fork.fusaka ≥ .shapella by decide]
      · unfold cost2
        simpa [show Fork.fusaka ≥ .shapella by decide] using hat'
    · obtain ⟨e, he, -⟩ := runFrame_of_abortsBy meets.aborts aborted within'
      rw [he] at hrun'
      cases hrun'
  · -- A collision: no message.
    have hdep' : st.accountDeployable (create2Address msg.currentTarget salt (memoryReadBytes
        (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)) =
        false := by simpa using hdep
    obtain ⟨after, st', h1, hinc, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, ar, as, ass⟩ :=
      createStep2_collision (evm := evm) hst hst2 hinit hgE (by rw [hs, hm]; exact hbal)
        (by rw [hs, hm]; exact hnonce) (by rw [hm]; exact hdepth)
        (by rw [hs, hm, hmem]; exact hdep')
    have hS : Step .fusaka evm after := .next hrunning (by rw [hstep]; exact h1)
    have hrun' := hrun
    rw [runFrame_eq_of_reaches Step.gasHeld_le Step.runFrame_eq (.single hS) within] at hrun'
    rw [hs, hm, hmem] at hinc
    refine .inr (.inl ⟨hbal, hnonce, hdepth, hdep', st', after, _, hinc,
      ⟨by rw [a1, hc], by rw [a2, hj], by rw [a3, hm], by rw [a4, hpc], a5, by rw [a6, hmem],
        by rw [a7, hmem, hgas], by rw [a8, hrunning], by rw [a9, herr], by rw [ao, hout], as,
        by rw [ass, hss, hm, hmem], ar⟩, hrun'⟩)

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateBack.create2_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_back

end SolidCore.Refinement.Solar.AssembleCreateBack

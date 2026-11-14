import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# CALL with value at the frame's own gas, from a run that succeeds

`callValue_back`: a CALL that sends a nonzero value, in a run of EthLib's interpreter (Fusaka) that ends
with no error, had the gas for its price (the access of EIP-2929, 9000 for the value, 25000 for a
dead callee and the growth of memory; `callValue_oog` shows the step fails short of it), and the run goes on
in one of two ways:

* the current account lacks the value: no message, 0 pushed, the gas it would pass on (with the
  stipend of 2300) given back, empty return data (EthLib's `Logic.callValueLow`);
* otherwise the callee runs with the value, its input and the gas EIP-150 passes on (with the
  stipend), under any runner of messages meeting `P`; the caller pushes 1 when the callee's frame
  ends with no error and 0 otherwise, writes its output to the output range, takes it as the return
  data, and its state and substate are the ones the callee left (EthLib's `Logic.callValue`).
  Nothing is assumed of the callee: it may reenter the caller, so the rule says nothing of the
  state after the call beyond the callee's frame, which a run's table records.

Named hypotheses: the callee's code is in the state and is no EIP-7702 delegation, and the frame
is below the greatest depth (a frame of a call at depth below 1024 is, `hdepth`).
-/

namespace SolidCore.Refinement.Solar.AssembleCallValue

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- The price of CALL with value before the gas it passes on: the access, the value, a new
account, and the growth of memory. -/
def priceV (st : State.TransactionState) (ss : Substate) (msize : Nat) (to v i isz o osz : U256) :
    Nat :=
  (callBaseCost .fusaka (decide (toAddressMasked to ∉ ss.accessedAddresses)) +
      callNewAccountCost .fusaka st (toAddressMasked to) v + callValueCost .fusaka v) +
    (extendMemory msize [(i, isz), (o, osz)]).cost

/-- **CALL with value short of its price fails or halts the frame.** -/
theorem callValue_oog {evm : Evm .fusaka Nat} {g a v i isz o osz : U256} {rest : List U256}
    {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok calleeCode)
    (hdel : delegatedAddress calleeCode = none)
    (hgas : evm.gas < priceV evm.state evm.substate evm.memory.size a v i isz o osz) :
    StepFails (callStep .call evm) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  simp only [priceV] at hcode hgas
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost .fusaka (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : gas < E + (extendMemory memory.size [(i, isz), (o, osz)]).cost := by
    rw [← hE]
    simpa [callNewAccountCost, callValueCost, hv', show ¬ Fork.fusaka ≥ .glamsterdam by decide,
      show Fork.spuriousDragon ≤ Fork.fusaka by decide] using hgas
  have hle : E ≤ (messageCallGas .fusaka v g.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost E).cost := by
    simp [messageCallGas]
  have hlt : gas < (messageCallGas .fusaka v g.toNat gas
      (extendMemory memory.size [(i, isz), (o, osz)]).cost E).cost +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost := by omega
  unfold StepFails
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, show Fork.berlin ≤ Fork.fusaka by decide,
    checkGas, show ¬ Fork.fusaka ≥ .glamsterdam by decide, accessDelegation, accountCode,
    recordAccountRead, hcode, hdel, show Fork.pectra ≤ Fork.fusaka by decide,
    show Fork.tangerineWhistle ≤ Fork.fusaka by decide,
    show Fork.spuriousDragon ≤ Fork.fusaka by decide, Except.mapError, callExtraGas,
    callNewAccountCost, callValueCost, hv', payCall, chargeGas, GasMeter.charge, keepReads, hE, hlt,
    GasMeter.gasLeft,
    exceptionalHalt, EvmError.aborts]


/-- The gas CALL with value passes on and its full price, EIP-150 at the frame's gas `g`. -/
abbrev mcgV (g : Nat) (st : State.TransactionState) (ss : Substate) (msize : Nat)
    (asked to v i isz o osz : U256) : MessageCallGas :=
  messageCallGas .fusaka v asked.toNat g (extendMemory msize [(i, isz), (o, osz)]).cost
    (callBaseCost .fusaka (decide (toAddressMasked to ∉ ss.accessedAddresses)) +
      callNewAccountCost .fusaka st (toAddressMasked to) v + callValueCost .fusaka v)

/-- **CALL with value in a run that succeeds**: the frame had its price, and the run goes on with
no message when the current account lacks the value, or from the frame after the callee's message
otherwise, under any runner of messages meeting `P`. -/
theorem callValue_back {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {asked to v i isz o osz : U256} {rest : List U256} {evm : Evm .fusaka Nat}
    {calleeCode : ByteArray}
    (hat : At code msg pc (asked :: to :: v :: i :: isz :: o :: osz :: rest) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hv : v ≠ 0)
    (hstatic : msg.isStatic = false)
    (hcode : st.getCode (st.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : delegatedAddress calleeCode = none) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    priceV st ss M.size to v i isz o osz ≤ g ∧
    (((st.getAccount msg.currentTarget).balance < v ∧
      ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
        At code msg (pc + 1) (0 :: rest)
          (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
          (g - ((mcgV g st ss M.size asked to v i isz o osz).cost +
            (extendMemory M.size [(i, isz), (o, osz)]).cost) +
            (mcgV g st ss M.size asked to v i isz o osz).subCall)
          ((st.recordAccountRead (toAddressMasked to)).recordAccountRead msg.currentTarget)
          { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked to) }
          .empty m ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin) ∨
    (v ≤ (st.getAccount msg.currentTarget).balance ∧
      ∃ (caller : Evm .fusaka Nat) (m : Message .fusaka) (child after : Evm .fusaka Nat)
        (within' : GasMeter.gasHeld after.gas ≤ bound),
        P caller m child ∧ child.gas ≤ m.gas ∧
        caller.state = (st.recordAccountRead (toAddressMasked to)).recordAccountRead
          msg.currentTarget ∧
        caller.substate = { ss with
          accessedAddresses := ss.accessedAddresses.insert (toAddressMasked to) } ∧
        m.gas = (mcgV g st ss M.size asked to v i isz o osz).subCall ∧
        m.caller = msg.currentTarget ∧ m.currentTarget = toAddressMasked to ∧
        m.code = calleeCode ∧
        m.data = memoryReadBytes (memoryExtend M
          (extendMemory M.size [(i, isz), (o, osz)]).expandBy) i.toNat isz.toNat ∧
        m.value = v ∧ m.isStatic = false ∧
        At code msg (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
            o.toNat (child.output.extract 0 (min osz.toNat child.output.size)))
          (g - ((mcgV g st ss M.size asked to v i isz o osz).cost +
            (extendMemory M.size [(i, isz), (o, osz)]).cost) + child.gas)
          (incorporateChild .fusaka caller child).state
          (incorporateChild .fusaka caller child).substate child.output after ∧
        runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)) := by
  have hat0 := hat
  obtain ⟨hc, hj, hm, hpc, hst, hmem, hgas, hrunning, herr, hout, hs, hss, hrd⟩ := hat0
  have hlt' : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
  have decoded : Op.ofByte .fusaka (evm.code[evm.pc]'hlt') = some .call := by
    have he : evm.code[evm.pc]'hlt' = code[pc]'hlt := by subst hc hpc; rfl
    rw [he, hbyte]
    exact ofByte_of_decode rfl (Fork.frontier_le _)
  have hstep : step .fusaka evm = callStep .call evm :=
    step_of_messageInstruction hlt' decoded instruction_call messageInstruction_call
  have hg : priceV st ss M.size to v i isz o osz ≤ g := by
    refine Nat.le_of_not_lt fun hlow => ?_
    have fails := callValue_oog (evm := evm) hst hv (by rw [hs]; exact hcode) hdel
      (by rw [hs, hss, hmem, hgas]; exact hlow)
    exact error_ne_none_of_stepFails hrunning (by rw [hstep]; exact fails) hrun hok
  refine ⟨hg, ?_⟩
  rcases Nat.lt_or_ge (st.getAccount msg.currentTarget).balance.toNat v.toNat with hb | hb
  · -- The current account lacks the value: no message.
    have hbal : (st.getAccount msg.currentTarget).balance < v := BitVec.lt_def.mpr hb
    obtain ⟨m, hr, hq⟩ := callValueLow (fork := .fusaka) (cold := _) (by decide) (by decide) hlt
      hbyte hv hstatic hbal hcode (fun _ => hdel) rfl hg evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact .inl ⟨hbal, m, _, hq, hrun⟩
  · have hbal : v ≤ (st.getAccount msg.currentTarget).balance := BitVec.le_def.mpr hb
    have H := callValue (fork := .fusaka) (callee := P) (asked := asked) (rest := rest)
      (returnData := rd)
      (cold := _) (by decide) (by decide) hlt hbyte hv hstatic hbal hcode (fun _ => hdel) hdepth rfl hg
    obtain ⟨after, hr, hq⟩ := H bound runChild meets evm hat within
    have within' := Nat.le_trans (hr.gasHeld_le StepBy.gasHeld_le) within
    have hrun' := hrun
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hr within] at hrun'
    rcases hq with ⟨caller, m, child, hk, hcg, c1, c2, m1, m2, m3, -, -, m6, m7, m8, -, -, m11,
      hat'⟩ | aborted
    · exact .inr ⟨hbal, caller, m, child, after, within', hk, hcg, c1, c2, m1, m2, m3, m6, m7, m8,
        m11, hat', hrun'⟩
    · obtain ⟨e, he, -⟩ := runFrame_of_abortsBy meets.aborts aborted within'
      rw [he] at hrun'
      cases hrun'

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValue.callValue_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callValue_back

end SolidCore.Refinement.Solar.AssembleCallValue

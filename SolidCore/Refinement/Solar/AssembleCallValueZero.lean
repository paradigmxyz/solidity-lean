import SolidCore.Refinement.Solar.AssembleCall

/-!
# CALL with no value at the frame's own gas, from a run that succeeds

`call0_back`: `AssembleCall.staticcall_back` for CALL with value 0 in a frame that may change the
state, as UniswapV2Factory's call to the new pair's `initialize` is: a CALL step in a run that ends
with no error read the callee's code (and its delegate's for an EIP-7702 delegation,
`call0_routes_of_ok`), had the gas for its access, the route and the growth of memory, and the run
goes on from the frame after the callee's frame ended (EthLib's `Logic.callKindRoute` for
`.call`), under any runner of messages meeting `P`. The message is not static and sends no value;
nothing is assumed of the callee, which may reenter the caller, so the state after the call is
the callee frame's.
-/

namespace SolidCore.Refinement.Solar.AssembleCallValueZero

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.AssembleCall
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- The pops of CALL's (with value 0) operands. -/
theorem pop_call0 {evm : Evm .fusaka Nat} {g a i isz o osz : U256} {rest : List U256}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest) :
    ∃ stack : Stack, stack.val = rest ∧
      popCallOperands .call evm =
        .ok (⟨g, toAddressMasked a, 0, i, isz, o, osz⟩, { evm with stack }) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  exact ⟨_, rfl, rfl⟩


/-- **A CALL step with value 0 that does not fail reads the callee's code and follows a route**: the
state holds the code of the callee and, for an EIP-7702 delegation, of its delegate. So a run that
succeeds needs no assumption on the state at its calls. -/
theorem call0_routes_of_ok {evm : Evm .fusaka Nat} {g a i isz o osz : U256} {rest : List U256}
    (hst : evm.stack.val = g :: a :: 0 :: i :: isz :: o :: osz :: rest)
    (hnf : ¬ StepFails (callStep .call evm)) :
    ∃ cc route, evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok cc ∧
      Routes .fusaka evm.state cc route := by
  obtain ⟨stack, -, hpop⟩ := pop_call0 hst
  have key : ∀ (hx : ∀ E : Evm .fusaka Nat, E.state = evm.state.recordAccountRead (toAddressMasked a) →
      ∀ known, ∃ err, accessDelegation E (toAddressMasked a) known = .error err),
      StepFails (callStep .call evm) := by
    intro hx
    simp only [callStep, hpop, bind, Except.bind, accessAddress, checkGas, recordAccountRead,
      show ¬ (Fork.fusaka ≥ .glamsterdam) by decide, false_and, ite_false,
      show Fork.fusaka ≥ Fork.berlin by decide, ite_true, pure, Except.pure]
    exact fails_keepReads_bind (hx _ rfl _)
  cases hc : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash with
  | error x =>
    exact absurd (key fun E hE known => accessDelegation_err1 (by
      intro cc; rw [hE]; simp [hc])) hnf
  | ok cc =>
    cases hd : delegatedAddress cc with
    | none => exact ⟨cc, none, rfl, fun _ => hd⟩
    | some d =>
      cases hc2 : evm.state.getCode (evm.state.getAccount d).codeHash with
      | ok c' => exact ⟨cc, some (d, c'), rfl, by decide, hd, hc2⟩
      | error x =>
        exact absurd (key fun E hE known => accessDelegation_err2 (cc := cc) (d := d)
          (by rw [hE]; simpa using hc) hd (by intro c'; rw [hE]; simp [hc2])) hnf


/-- **CALL with value 0 in a run that succeeds**, at the frame's own gas: the state held the callee's
code (and its delegate's, `Routes`), the gas paid for the access, the route and the growth of memory,
and the run goes on from the frame after the callee's frame ended. -/
theorem call0_back {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {rest : List U256}
    {evm : Evm .fusaka Nat}
    (hat : At code msg pc (asked :: addr :: 0 :: inOff :: inSize :: outOff :: outSize :: rest) M g st ss
      rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (calleeCode : ByteArray) (route : Route),
      st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode ∧
      Routes .fusaka st calleeCode route ∧
    (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100) +
        routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route +
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g ∧
    ∃ (caller : Evm .fusaka Nat) (m : Message .fusaka) (child after : Evm .fusaka Nat)
      (within' : GasMeter.gasHeld after.gas ≤ bound) (g' : Nat),
      P caller m child ∧ child.gas ≤ m.gas ∧
      caller.state = (routeState (st.recordAccountRead (toAddressMasked addr)) route).recordAccountRead
        msg.currentTarget ∧
      caller.substate = routeSub { ss with
        accessedAddresses := ss.accessedAddresses.insert (toAddressMasked addr) } route ∧
      m.isStatic = false ∧ m.value = 0 ∧ m.code = routeCode calleeCode route ∧
      m.currentTarget = toAddressMasked addr ∧ m.target = some (toAddressMasked addr) ∧
      m.data = memoryReadBytes (memoryExtend M
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy) inOff.toNat
        inSize.toNat ∧
      m.codeAddress = some (routeAddr (toAddressMasked addr) route) ∧
      m.disablePrecompiles = route.isSome ∧
      m.gas = (messageCallGas .fusaka 0 asked.toNat g
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost
        ((if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100) +
          routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route)).subCall ∧
      g' + (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100) +
        routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route +
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g ∧
      At code msg (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite (memoryExtend M
            (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
          outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size)))
        g' (incorporateChild .fusaka caller child).state
        (incorporateChild .fusaka caller child).substate child.output after ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin := by
  have hat0 := hat
  obtain ⟨hc, hv, hm, hpc, hst, hmem, hgas, hrunning, -, -, hst', hss, -⟩ := hat0
  have hlt' : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
  have decoded : Op.ofByte .fusaka (evm.code[evm.pc]'hlt') = some .call := by
    have he : evm.code[evm.pc]'hlt' = code[pc]'hlt := by subst hc hpc; rfl
    rw [he, hbyte]
    exact ofByte_of_decode rfl (by decide)
  have hstep : step .fusaka evm = callStep .call evm :=
    step_of_messageInstruction hlt' decoded instruction_call
      messageInstruction_call
  have hnf : ¬ StepFails (callStep .call evm) := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun hok
  obtain ⟨calleeCode, route, hcode, hroute⟩ := call0_routes_of_ok hst hnf
  rw [hst'] at hcode hroute
  refine ⟨calleeCode, route, hcode, hroute, ?_⟩
  have hcost := callBaseCost_of_berlin (fork := .fusaka) (by decide) (by decide)
    (decide (toAddressMasked addr ∉ ss.accessedAddresses))
  generalize hcold : decide (toAddressMasked addr ∉ ss.accessedAddresses) = cold at hcost
  generalize hdc : routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route = dc
  by_cases hg : (if cold then 2600 else 100) + dc +
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g
  · refine ⟨hg, ?_⟩
    have H := (callKindRoute (fork := .fusaka) (kind := .call) (callee := P)
      (asked := asked) (rest := rest) (returnData := rd) (gas := g) (memory := M) (substate := ss)
      (inputStart := inOff) (inputSize := inSize) (outputStart := outOff) (outputSize := outSize)
      (by decide) hlt hbyte (ofByte_of_decode rfl (by decide)) instruction_call
      messageInstruction_call hcode hroute hdepth
      (by rw [← hcold] at hcost; rw [hcost, hcold, hdc]; exact hg)).toUnder
    obtain ⟨after, hr, hq⟩ := H bound runChild meets evm hat within
    have within' := Nat.le_trans (hr.gasHeld_le StepBy.gasHeld_le) within
    have hrun' := hrun
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hr within] at hrun'
    rcases hq with ⟨caller, m, child, ⟨s1, s2, m1, -, -, mt, mtg, mca, mc, mdp, md, mv, -, -, ms, -, -⟩,
      hk, hcg, hat'⟩ | aborted
    · rw [← hcold] at hcost
      rw [hcost, hdc, hcold] at m1 hat'
      obtain ⟨hc1, hc2⟩ := staticcall_gas (asked := asked.toNat)
        (memc := (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost)
        (extra := (if cold then 2600 else 100) + dc) (g := g) (by omega)
      refine ⟨caller, m, child, after, within', _, hk, hcg, s1, s2, by rw [ms, hstatic]; decide,
        by simpa using mv, mc, by simpa using mt, by simpa using mtg, md, mca, mdp, m1, ?_, hat', hrun'⟩
      rw [m1] at hcg
      rw [hc1]
      omega
    · obtain ⟨e, he, -⟩ := runFrame_of_abortsBy meets.aborts aborted within'
      rw [he] at hrun'
      cases hrun'
  · exfalso
    have fails : StepFails (step .fusaka evm) := by
      rw [hstep]
      refine callStep_fails_of_routes (route := route) (by decide) (a := addr) (i := inOff)
        (isz := inSize) (o := outOff) (osz := outSize) (g := asked) (rest := rest)
        (by rw [hst]; rfl) (by rw [hst']; exact hcode) (by rw [hst']; exact hroute) ?_
      rw [callBaseCost_of_berlin (by decide) (by decide), hgas, hmem, hss, hcold, hdc]
      omega
    exact error_ne_none_of_stepFails hrunning fails hrun hok

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValueZero.call0_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call0_back

end SolidCore.Refinement.Solar.AssembleCallValueZero

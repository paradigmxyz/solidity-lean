import SolidCore.Refinement.Solar.AssembleCut
import EthLib.Execution.Proofs.Evm.Call.StaticMessage
import EthLib.Execution.Proofs.Evm.Logic.CallSteps

/-!
# EVM IR to bytecode: STATICCALL at the frame's own gas

What a STATICCALL does in a run of EthLib that succeeds, at the gas the frame has, under the runner
of messages the interpreter uses, so that the answers of a run's oracle to the call (its success,
its output and the storage after it) are what the actual callee frame gave.

* `StaticKept`: the frame that ends a static message to code keeps the account, the storage and
  the transient storage of every address. `meets_static` proves that the interpreter's runner of
  messages (`processRunner`) meets it, from EthLib's `processMessage_sameOutside_static`: this is
  the connection of the oracle's storage answer to the actual execution, for every callee code and
  however deep its own calls go.
* `staticcall_back`: a STATICCALL in a run that succeeds had the gas for its access and the growth
  of memory (a frame short of it fails, `callStep_fails_of_routes`), and the run goes on from the
  frame after the call: the flag of the callee frame's success, memory with its output written to
  the output range, its output as the return data, at most the gas before less the access and the
  growth of memory (the callee gets less than the call costs, EIP-150), and the state the callee
  left, which `StaticKept` relates to the caller's.

Nothing is assumed of the callee's code: a STATICCALL step that does not fail has read the code of
the callee, and of its delegate for an EIP-7702 delegation (`staticcall_routes_of_ok`), so the
run's success gives the code and the route, and `staticcall_back` follows EthLib's `callKindRoute`
along it, delegated callees included.
-/

namespace SolidCore.Refinement.Solar.AssembleCall

open SolarTV SolarTV.Machine SolidCore.Refinement
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- The frame that ends a static message to code keeps every address's account, storage and
transient storage (up to the records of reads). -/
def StaticKept (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  StaticMessage caller.state m → State.TransactionState.SameOutside [] caller.state child.state

/-- **The interpreter's runner of messages keeps the state across static messages.** -/
theorem meets_static (bound : Nat) :
    Meets (bound := bound) StaticKept (processRunner .fusaka (Meter := Nat) bound) := by
  refine ⟨fun caller m lt ended h hs => ?_, (meets_process .fusaka bound).aborts⟩
  unfold processRunner at h
  split at h
  · exact processMessage_sameOutside_static (by decide) hs h
  · rename_i hnone
    have := hs.2.1
    rw [hnone] at this
    cases this

/-- The price of a STATICCALL with no value: what it passes on and its access, and what it passes
on is at most the gas left after the access and the growth of memory (EIP-150). -/
theorem staticcall_gas {asked g memc extra : Nat} (h : extra + memc ≤ g) :
    (messageCallGas .fusaka 0 asked g memc extra).cost =
        (messageCallGas .fusaka 0 asked g memc extra).subCall + extra ∧
      (messageCallGas .fusaka 0 asked g memc extra).subCall + extra + memc ≤ g := by
  unfold messageCallGas maxMessageCallGas
  simp only [ite_true, Nat.add_zero, show Fork.fusaka ≥ .tangerineWhistle by decide, h, and_self,
    ite_true]
  constructor
  · trivial
  · have := Nat.min_le_right asked (g - memc - extra - (g - memc - extra) / 64)
    omega

/-! ## The callee's code, from the run -/

/-- The pops of STATICCALL's operands. -/
theorem pop_static {evm : Evm .fusaka Nat} {g a i isz o osz : U256} {rest : List U256}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest) :
    ∃ stack : Stack, stack.val = rest ∧
      popCallOperands .staticcall evm =
        .ok (⟨g, toAddressMasked a, 0, i, isz, o, osz⟩, { evm with stack }) := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  exact ⟨_, rfl, rfl⟩

/-- The rest of an instruction that errors makes the step fail. -/
theorem fails_keepReads {evm : Evm .fusaka Nat} {e : EvmError} :
    StepFails (keepReads evm StepResult.next (.error e : Except EvmError (StepResult .fusaka Nat))) := by
  unfold keepReads
  dsimp only
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl, rfl, by simp [exceptionalHalt]⟩

/-- The rest of an instruction that starts with an error makes the step fail. -/
theorem fails_keepReads_bind {α : Type} {E : Evm .fusaka Nat} {x : Except EvmError α}
    {f : α → Except EvmError (StepResult .fusaka Nat)} (hx : ∃ e, x = .error e) :
    StepFails (keepReads E StepResult.next (x >>= f)) := by
  obtain ⟨e, rfl⟩ := hx
  exact fails_keepReads

/-- The access to the callee fails when the state holds no code for it. -/
theorem accessDelegation_err1 {e : Evm .fusaka Nat} {addr : Address} {known : Nat}
    (h : ∀ cc, e.state.getCode (e.state.getAccount addr).codeHash ≠ .ok cc) :
    ∃ err, accessDelegation e addr known = .error err := by
  unfold accessDelegation accountCode
  cases hc : e.state.getCode (e.state.getAccount addr).codeHash with
  | error x => exact ⟨.state x, by simp [Except.mapError, bind, Except.bind]⟩
  | ok cc => exact absurd hc (h cc)

/-- The access to the callee fails when its code delegates to an account whose code the state
does not hold. -/
theorem accessDelegation_err2 {e : Evm .fusaka Nat} {addr d : Address} {known : Nat} {cc : ByteArray}
    (hc : e.state.getCode (e.state.getAccount addr).codeHash = .ok cc)
    (hd : delegatedAddress cc = some d)
    (h : ∀ c', e.state.getCode (e.state.getAccount d).codeHash ≠ .ok c') :
    ∃ err, accessDelegation e addr known = .error err := by
  unfold accessDelegation
  cases hc2 : e.state.getCode (e.state.getAccount d).codeHash with
  | error x =>
    refine ⟨.state x, ?_⟩
    simp [accountCode, Except.mapError, hc, hc2, hd, bind, Except.bind, accessAddress, checkGas,
      recordAccountRead, show Fork.fusaka ≥ Fork.pectra by decide, show Fork.berlin ≤ Fork.fusaka by decide,
      show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, pure, Except.pure]
  | ok c' => exact absurd hc2 (h c')

/-- **A STATICCALL step that does not fail reads the callee's code and follows a route**: the
state holds the code of the callee and, for an EIP-7702 delegation, of its delegate. So a run that
succeeds needs no assumption on the state at its calls. -/
theorem staticcall_routes_of_ok {evm : Evm .fusaka Nat} {g a i isz o osz : U256} {rest : List U256}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest)
    (hnf : ¬ StepFails (callStep .staticcall evm)) :
    ∃ cc route, evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok cc ∧
      Routes .fusaka evm.state cc route := by
  obtain ⟨stack, -, hpop⟩ := pop_static hst
  have key : ∀ (hx : ∀ E : Evm .fusaka Nat, E.state = evm.state.recordAccountRead (toAddressMasked a) →
      ∀ known, ∃ err, accessDelegation E (toAddressMasked a) known = .error err),
      StepFails (callStep .staticcall evm) := by
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

/-- **STATICCALL in a run that succeeds**, at the frame's own gas: the state held the callee's code
(and its delegate's, `Routes`), the gas paid for the access, the route and the growth of memory,
and the run goes on from the frame after the callee's frame ended. -/
theorem staticcall_back {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {rest : List U256}
    {evm : Evm .fusaka Nat}
    (hat : At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: rest) M g st ss
      rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
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
      m.isStatic = true ∧ m.value = 0 ∧ m.code = routeCode calleeCode route ∧
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
  have decoded : Op.ofByte .fusaka (evm.code[evm.pc]'hlt') = some .staticcall := by
    have he : evm.code[evm.pc]'hlt' = code[pc]'hlt := by subst hc hpc; rfl
    rw [he, hbyte]
    exact ofByte_of_decode rfl (by decide)
  have hstep : step .fusaka evm = callStep .staticcall evm :=
    step_of_messageInstruction hlt' decoded instruction_staticcall
      (messageInstruction_staticcall (by decide))
  have hnf : ¬ StepFails (callStep .staticcall evm) := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun hok
  obtain ⟨calleeCode, route, hcode, hroute⟩ := staticcall_routes_of_ok hst hnf
  rw [hst'] at hcode hroute
  refine ⟨calleeCode, route, hcode, hroute, ?_⟩
  have hcost := callBaseCost_of_berlin (fork := .fusaka) (by decide) (by decide)
    (decide (toAddressMasked addr ∉ ss.accessedAddresses))
  generalize hcold : decide (toAddressMasked addr ∉ ss.accessedAddresses) = cold at hcost
  generalize hdc : routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route = dc
  by_cases hg : (if cold then 2600 else 100) + dc +
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g
  · refine ⟨hg, ?_⟩
    have H := (callKindRoute (fork := .fusaka) (kind := .staticcall) (callee := P)
      (asked := asked) (rest := rest) (returnData := rd) (gas := g) (memory := M) (substate := ss)
      (inputStart := inOff) (inputSize := inSize) (outputStart := outOff) (outputSize := outSize)
      (by decide) hlt hbyte (ofByte_of_decode rfl (by decide)) instruction_staticcall
      (messageInstruction_staticcall (by decide)) hcode hroute hdepth
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
      refine ⟨caller, m, child, after, within', _, hk, hcg, s1, s2, by simpa using ms,
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

/-- info: 'SolidCore.Refinement.Solar.AssembleCall.meets_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_static

/-- info: 'SolidCore.Refinement.Solar.AssembleCall.staticcall_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_back

/-! ## STATICCALL in SolarTV at any ranges -/

section Effect

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop

/-- `AssembleEffects.memRel_expand2` at any ranges whose words SolarTV counts (`memRel_expandW`). -/
theorem memRel_expand2W {m : Mem} {M : ByteArray} {o1 s1 o2 s2 : Word} (hm : MemRel m M)
    (hb1 : s1 = 0 ∨ (o1.toNat + s1.toNat + 31) / 32 < 2 ^ 251)
    (hb2 : s2 = 0 ∨ (o2.toNat + s2.toNat + 31) / 32 < 2 ^ 251) :
    MemRel ((m.expand o1.toNat s1.toNat).expand o2.toNat s2.toNat)
      (memoryExtend M (extendMemory M.size [(o1, s1), (o2, s2)]).expandBy) := by
  have h1 := memRel_expandW hm hb1
  have h2 := memRel_expandW h1 hb2
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  refine ⟨?_, fun i => ?_⟩
  · rw [← h2.1]
    simp only [size_memoryExtend, extendMemory_cons_expandBy hmod (o1, s1) [(o2, s2)]]
    omega
  · rw [byteAt_memoryExtend]
    have := h2.2 i
    rw [byteAt_memoryExtend, byteAt_memoryExtend] at this
    rw [this]

/-- **STATICCALL in SolarTV at any ranges** whose words SolarTV counts, under an oracle that answers
the call as the callee's frame `child` ended: `AssembleEffects.staticcall_effect` without its
bound of `2 ^ 32` on the ranges, so at any offset a run that succeeds pays for. -/
theorem staticcall_effectW {o : Oracle} {call : Call} {s : State} {M : ByteArray}
    {gas addr inOff inSize outOff outSize : Word} {child : Evm .fusaka Nat}
    (hm : MemRel s.memory M)
    (hb1 : inSize = 0 ∨ (inOff.toNat + inSize.toNat + 31) / 32 < 2 ^ 251)
    (hb2 : outSize = 0 ∨ (outOff.toNat + outSize.toNat + 31) / 32 < 2 ^ 251)
    (hflag : callFlag o (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]) = if child.error.isNone then 1 else 0)
    (hrd : RdRel o (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]) child.output) :
    ∃ s', Effect.apply o call (.call .staticcall) [gas, addr, inOff, inSize, outOff, outSize] s =
        some (some (if child.error.isNone then 1 else 0), s') ∧
      s'.storage = s.storage ∧ s'.transient = s.transient ∧ RdRel o s'.world child.output ∧
      s'.world = s.world ++ [.call .staticcall [gas, addr]
        (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
          inOff.toNat inSize.toNat) s.storage s.transient] ∧
      MemRel s'.memory (memoryWrite (memoryExtend M
          (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
        outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size))) := by
  have he := memRel_expand2W hm hb1 hb2
  refine ⟨called o .staticcall s ((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat) outOff outSize (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Effect.apply, CallKind.shape, hflag]
  · rfl
  · rfl
  · exact hrd
  · rfl
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

end Effect

/-- info: 'SolidCore.Refinement.Solar.AssembleCall.staticcall_effectW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_effectW

/-! ## The state after a STATICCALL -/

section State

open EthLib.Execution.State

/-- **The state after a STATICCALL is the caller's**, at every address (account, storage and
transient storage), under a runner keeping static state: the message is static, has a target, sends
no value, and its code, when it has any, is the callee account's (`getCode` of the empty hash is
empty). -/
theorem staticcall_state {st : State.TransactionState} {msg : Message .fusaka} {addr : U256}
    {calleeCode : ByteArray} {route : Route} {caller child : Evm .fusaka Nat} {m : Message .fusaka}
    (hcode : st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode)
    (hroute : Routes .fusaka st calleeCode route)
    (hk : StaticKept caller m child)
    (hcs : caller.state = (routeState (st.recordAccountRead (toAddressMasked addr)) route).recordAccountRead
      msg.currentTarget)
    (hms : m.isStatic = true) (hmv : m.value = 0) (hmc : m.code = routeCode calleeCode route)
    (hmt : m.currentTarget = toAddressMasked addr) (htg : m.target = some (toAddressMasked addr)) :
    TransactionState.SameOutside [] st (incorporateChild .fusaka caller child).state := by
  have hsm : StaticMessage caller.state m := by
    refine ⟨hms, by rw [htg]; rfl, fun hsz he => ?_, fun _ hv => absurd hmv hv⟩
    rw [hcs, hmt] at he
    rcases route with _ | ⟨d, c'⟩
    · simp only [routeState, TransactionState.getAccount_recordAccountRead] at he
      rw [he] at hcode
      simp only [TransactionState.getCode, ite_true, Except.ok.injEq] at hcode
      rw [hmc, routeCode, ← hcode] at hsz
      exact hsz rfl
    · simp only [routeState, TransactionState.getAccount_recordAccountRead] at he
      rw [he] at hcode
      simp only [TransactionState.getCode, ite_true, Except.ok.injEq] at hcode
      have hdel := hroute.2.1
      rw [← hcode] at hdel
      simp only [delegatedAddress, isValidDelegation] at hdel
      obtain ⟨⟨h0, -⟩, -⟩ := hdel
  have h1 : TransactionState.SameOutside [] st caller.state := by
    rw [hcs]
    rcases route with _ | ⟨d, c'⟩
    · exact (TransactionState.sameOutside_recordAccountRead st _).trans
        (TransactionState.sameOutside_recordAccountRead _ _)
    · exact ((TransactionState.sameOutside_recordAccountRead st _).trans
        (TransactionState.sameOutside_recordAccountRead _ _)).trans
        (TransactionState.sameOutside_recordAccountRead _ _)
  have h2 := h1.trans (hk hsm)
  have hst : (incorporateChild .fusaka caller child).state = child.state := by
    unfold incorporateChild
    split <;> rfl
  rw [hst]
  simpa using h2

end State

/-- info: 'SolidCore.Refinement.Solar.AssembleCall.staticcall_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_state

end SolidCore.Refinement.Solar.AssembleCall

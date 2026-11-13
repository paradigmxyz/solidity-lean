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

The callee's code must be in the state and be no EIP-7702 delegation (`hcode`, `hdel`); a
delegated callee takes EthLib's `callKindRoute` and is not covered here.
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

/-- **STATICCALL in a run that succeeds**, at the frame's own gas. -/
theorem staticcall_back {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {rest : List U256} {calleeCode : ByteArray}
    {evm : Evm .fusaka Nat}
    (hat : At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: rest) M g st ss
      rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hcode : st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode)
    (hdel : delegatedAddress calleeCode = none) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100) +
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g ∧
    ∃ (caller : Evm .fusaka Nat) (m : Message .fusaka) (child after : Evm .fusaka Nat)
      (within' : GasMeter.gasHeld after.gas ≤ bound) (g' : Nat),
      P caller m child ∧ child.gas ≤ m.gas ∧
      caller.state = (st.recordAccountRead (toAddressMasked addr)).recordAccountRead
        msg.currentTarget ∧
      caller.substate = { ss with
        accessedAddresses := ss.accessedAddresses.insert (toAddressMasked addr) } ∧
      m.isStatic = true ∧ m.value = 0 ∧ m.code = calleeCode ∧
      m.currentTarget = toAddressMasked addr ∧ m.target = some (toAddressMasked addr) ∧
      m.data = memoryReadBytes (memoryExtend M
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy) inOff.toNat
        inSize.toNat ∧
      g' + (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100) +
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g ∧
      At code msg (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite (memoryExtend M
            (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
          outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size)))
        g' (incorporateChild .fusaka caller child).state
        (incorporateChild .fusaka caller child).substate child.output after ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin := by
  generalize hcold : decide (toAddressMasked addr ∉ ss.accessedAddresses) = cold
  by_cases hg : (if cold then 2600 else 100) +
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g
  · refine ⟨hg, ?_⟩
    have H := staticcallWith (fork := .fusaka) (by decide) (by decide) (callee := P)
      (asked := asked) (rest := rest) (returnData := rd) hlt hbyte hcode (fun _ => hdel) hdepth
      hcold hg
    obtain ⟨after, hr, hq⟩ := H bound runChild meets evm hat within
    have within' := Nat.le_trans (hr.gasHeld_le StepBy.gasHeld_le) within
    have hrun' := hrun
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hr within] at hrun'
    rcases hq with ⟨caller, m, child, hk, hcg, hcs, hcsub, hmg, -, hmt, htg, -, hmc, hmd, hmv, -,
      hms, hat'⟩ | aborted
    · obtain ⟨hc1, hc2⟩ := staticcall_gas (asked := asked.toNat)
        (memc := (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost)
        (extra := if cold then 2600 else 100) (g := g) (by omega)
      refine ⟨caller, m, child, after, within', _, hk, hcg, hcs, hcsub, hms, hmv, hmc, hmt, htg, hmd,
        ?_, hat', hrun'⟩
      rw [hmg] at hcg
      rw [hc1]
      omega
    · obtain ⟨e, he, -⟩ := runFrame_of_abortsBy meets.aborts aborted within'
      rw [he] at hrun'
      cases hrun'
  · exfalso
    obtain ⟨hc, hv, hm, hpc, hst, hmem, hgas, hrunning, -, -, hst', hss, -⟩ := hat
    have hlt' : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
    have decoded : Op.ofByte .fusaka (evm.code[evm.pc]'hlt') = some .staticcall := by
      have he : evm.code[evm.pc]'hlt' = code[pc]'hlt := by subst hc hpc; rfl
      rw [he, hbyte]
      exact ofByte_of_decode rfl (by decide)
    have hstep : step .fusaka evm = callStep .staticcall evm :=
      step_of_messageInstruction hlt' decoded instruction_staticcall
        (messageInstruction_staticcall (by decide))
    have fails : StepFails (step .fusaka evm) := by
      rw [hstep]
      refine callStep_fails_of_routes (route := none) (by decide) (a := addr) (i := inOff)
        (isz := inSize) (o := outOff) (osz := outSize) (g := asked) (rest := rest)
        (by rw [hst]; rfl) (by rw [hst']; exact hcode) (fun _ => hdel) ?_
      rw [callBaseCost_of_berlin (by decide) (by decide), hgas, hmem, hss, hcold]
      simp only [routeCost, Nat.add_zero]
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

/-! ## Runs whose messages keep the state across static calls -/

section Runs

open SolarTV.Machine SolidCore.Refinement.Final SolidCore.Refinement.Solar.Assemble
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open EthLib.Execution.State

/-- A runner that keeps the state across static messages meets the assumption that always holds. -/
theorem Meets.weaken {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (h : Meets StaticKept runChild) : Meets (fun _ _ _ => True) runChild :=
  ⟨fun _ _ _ _ _ => trivial, h.aborts⟩

section BlocksS

variable {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
  (O : RunTable → Oracle)

/-- **One block of the simulation, read back from a run that succeeds**, as AssembleRun.Advances
but under every runner of messages that keeps the state across static messages (StaticKept): when the loop runs the frame `evm` to a frame `fin` with no error, the table grows to `T'`
and every oracle of a table extending `T'` runs the block from `x` to the same `r`: an end `fin`
shows (`Post`), or the next block state, related (`E T'`) to a frame with a lower measure that the
loop runs to `fin` too. -/
def AdvancesS (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets StaticKept runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none →
      ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

/-- **A run of EthLib that ends with no error is SolarTV's**, for every table extending the last
one the run grew. -/
theorem run_of_advancesS {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → AdvancesS blk O E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets StaticKept runChild) :
    ∀ (n : Nat) (T : RunTable) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none →
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
        run_of_advancesS adv meets n T' y after within' fin hE' (by omega) hrun' hok
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [iterate, hstep T'' (hle2.trans h), hk]⟩

end BlocksS

/-- A block that advances under every runner advances under every runner keeping static state. -/
theorem AdvancesS.of_advances {σ : Type} {blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ)}
    {O : RunTable → Oracle} {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    {T : RunTable} {x : σ} {evm : Evm .fusaka Nat} (h : AssembleRun.Advances blk O E Post meas T x evm) :
    AdvancesS blk O E Post meas T x evm :=
  fun bound runChild meets => h bound runChild (Meets.weaken meets)


open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at the given gas, run by run, from a block simulation**: when every frame
related to a block state (`E`, from the substate the frame started with) advances (`Advances`) to
an end SolarTV's halt shows (`PostL`) or to the next block, and the frame a call starts with is
related to SolarTV's initial state, then the oracle of the run's table makes every result of the
bytecode on the call the EVM IR's or a failure that changes nothing. -/
theorem within_of_advancesS {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesS (fun o => block o call p) O (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, Within (evmirSem (O T)) (ethLibWith gas) p code (· = call) := by
  by_cases hs : ∃ obs, Target.runWith gas code call = some obs ∧ obs.success = true
  swap
  · refine ⟨{}, fun call' hc obs hrun => Or.inr ?_⟩
    subst hc
    have hf : obs.success = false := by
      cases h : obs.success
      · rfl
      · exact absurd ⟨obs, hrun, h⟩ hs
    exact ⟨hf, Target.runWith_failure hrun hf⟩
  obtain ⟨obs, hrun, hsucc⟩ := hs
  suffices H : ∃ T, (evmirSem (O T)).run p call = some obs by
    obtain ⟨T, hT⟩ := H
    refine ⟨T, fun call' hc obs' hrun' => Or.inl ?_⟩
    subst hc
    change Target.runWith gas code call' = some obs' at hrun'
    rw [hrun] at hrun'
    cases hrun'
    exact hT
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hsucc
  obtain ⟨st', ss', within, hcases, hmove, hrf⟩ :=
    AssembleRun.processMessage_ok' (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  have R := AssembleLoop.rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advancesS (fun o => block o call p) O (adv ss')
    (meets_static _) _ {} _ _ within evm (start st' ss' R) (Nat.lt_succ_self _) hrf hok
  obtain ⟨k, hk⟩ := hit T (RunTable.Le.refl T)
  refine ⟨T, ?_⟩
  have hres : (evmirSem (O T)).run p call = some (observe call sF halt) := by
    change (SolarTV.EVM.Program.layer.result (O T) p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨k, hk⟩]
    rfl
  rw [hres]
  set msg := Final.Target.messageWith gas code call with hmsg
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := hpost
  have hss' : ss'.logs.toList = [] := by
    by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
    · rw [(hmove htr).2]
      simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
    · rw [(hcases htr).2]
      simp [Substate.empty]
  have hlogs := logs_of_match hL2
  have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
  have herr' : evm.error = errorOf (observe call sF halt) := herr
  have hout' : evm.output.toList.map (·.toNat) = (observe call sF halt).output := hout
  have hst' : (observe call sF halt).success = true →
      evm.substate.logs = ssF.logs ∧ ∀ slot,
        (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
          (observe call sF halt).storage slot :=
    fun h => ⟨hlogsF, hst h⟩
  have hfail : (observe call sF halt).success = false →
      (observe call sF halt).logs = [] ∧
      (observe call sF halt).storage = slotValue call.storage := by
    cases halt <;> simp [observe]
  have hok2 : (observe call sF halt).success = true →
      (observe call sF halt).logs = logs sF := by
    cases halt <;> simp [observe]
  clear herr hout hst hres hit hk
  generalize observe call sF halt = X at *
  have hsucc' : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  symm
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc' hout' hfail hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc', hout', ?_, ?_⟩
    · rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        exact (hst' hs).2 slot

/-- info: 'SolidCore.Refinement.Solar.AssembleCall.within_of_advancesS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms within_of_advancesS

end Runs

/-! ## The state after a STATICCALL -/

section State

open EthLib.Execution.State

/-- **The state after a STATICCALL is the caller's**, at every address (account, storage and
transient storage), under a runner keeping static state: the message is static, has a target, sends
no value, and its code, when it has any, is the callee account's (`getCode` of the empty hash is
empty). -/
theorem staticcall_state {st : State.TransactionState} {msg : Message .fusaka} {addr : U256}
    {calleeCode : ByteArray} {caller child : Evm .fusaka Nat} {m : Message .fusaka}
    (hcode : st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode)
    (hk : StaticKept caller m child)
    (hcs : caller.state = (st.recordAccountRead (toAddressMasked addr)).recordAccountRead
      msg.currentTarget)
    (hms : m.isStatic = true) (hmv : m.value = 0) (hmc : m.code = calleeCode)
    (hmt : m.currentTarget = toAddressMasked addr) (htg : m.target = some (toAddressMasked addr)) :
    TransactionState.SameOutside [] st (incorporateChild .fusaka caller child).state := by
  have hsm : StaticMessage caller.state m := by
    refine ⟨hms, by rw [htg]; rfl, fun hsz he => ?_, fun _ hv => absurd hmv hv⟩
    rw [hcs, hmt] at he
    simp only [TransactionState.getAccount_recordAccountRead] at he
    rw [he] at hcode
    simp only [TransactionState.getCode, ite_true, Except.ok.injEq] at hcode
    rw [hmc, ← hcode] at hsz
    exact hsz rfl
  have h1 : TransactionState.SameOutside [] st caller.state := by
    rw [hcs]
    exact (TransactionState.sameOutside_recordAccountRead st _).trans (TransactionState.sameOutside_recordAccountRead _ _)
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

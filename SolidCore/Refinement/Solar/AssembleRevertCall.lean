import SolidCore.Refinement.Solar.AssembleRevertCut
import SolidCore.Refinement.Solar.AssembleCallSeg

/-!
# Code with STATICCALLs, with the revert data related

`AssembleCallSeg.segS` reads each segment of code with STATICCALLs back from a run that succeeds and
rules REVERT out (`AssembleDyn.revert_false`). As `AssembleRevertCut` does for the checker with GAS,
this file reads them back from a run that ends with no error or reverts (`AssembleRevertCut.OkR`):
the STATICCALL at the frame's gas (`staticcall_backR`, `staticcall_cutR`) rules out a failing call
step by `error_ne_none_of_stepFailsR` (a step that fails at an opcode that is no REVERT ends no run
with the revert error, `RevertErr.step_good`), and REVERT shows the program's revert with its data.

* `segSR`, `advances_checkCSR`, `within_of_advancesQR`, `runs_of_checkCBR`: the per-run theorem
  for every program `AssembleCut.checkCB` accepts, with `AssembleLoop.WithinR`, under the named
  hypotheses `AssembleCallSeg.StaticRunner` and `CalleesRunE`: `AssembleCallSeg.CalleesRun` for
  the runs that end with no error or revert, stated of the frame the message runs.
-/

namespace SolidCore.Refinement.Solar.AssembleRevertCall

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Witness SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolidCore.Refinement.Solar.AssembleCall SolidCore.Refinement.Solar.AssembleCallWorld
open SolidCore.Refinement.Solar.AssembleCallCut SolidCore.Refinement.Solar.AssembleDyn
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Solar.AssembleCallSeg SolidCore.Refinement.Solar.AssembleRevertCut

/-- **A step that fails at an opcode that is no REVERT ends no run that succeeds or reverts.** -/
theorem error_ne_none_of_stepFailsR {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {low s : Evm .fusaka Nat} (running : low.running = true) (fails : StepFails (step .fusaka low))
    {within : GasMeter.gasHeld low.gas ≤ bound}
    (hs : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild low within = .ok s)
    (hok : OkR s) (herr : low.error = none) {op : Op}
    (hop : ∃ h : low.pc < low.code.size, Op.ofByte .fusaka low.code[low.pc] = some op)
    (hne : op ≠ .revert) : False := by
  have good := RevertErr.step_good (fork := .fusaka) low
  rcases fails with ⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩
  · have hne' := good.1 e he
    cases ab : e.aborts
    · rw [runFrame_of_step_eq_error running he ab] at hs
      cases hs
      rcases hok with h | h
      · simp [exceptionalHalt] at h
      · simp only [exceptionalHalt, Option.some.injEq] at h
        exact hne' h
    · rw [runFrame_of_step_eq_abort running he ab] at hs
      cases hs
  · rw [runFrame_of_step_eq_next running hb, runFrame_of_running_eq_false hbr] at hs
    cases hs
    rcases hok with h | h
    · exact hbe h
    · rcases good.2 _ hb h with h' | ⟨hlt, hop'⟩
      · rw [herr] at h'; cases h'
      · obtain ⟨hlt2, hop2⟩ := hop
        rw [hop2] at hop'
        exact hne (Option.some.inj hop')

section Dyn

variable {rd : ByteArray}

/-- **STATICCALL in a run that succeeds**, at the frame's own gas: the state held the callee's code
(and its delegate's, `Routes`), the gas paid for the access, the route and the growth of memory,
and the run goes on from the frame after the callee's frame ended. -/
theorem staticcall_backR {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
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
    (hok : OkR fin) :
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
  have herr0 : evm.error = none := hat.2.2.2.2.2.2.2.2.1
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
    error_ne_none_of_stepFailsR hrunning (by rw [hstep]; exact hf) hrun hok herr0 ⟨hlt', decoded⟩ (by decide)
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
    exact error_ne_none_of_stepFailsR hrunning fails hrun hok herr0 ⟨hlt', decoded⟩ (by decide)

/-- **A STATICCALL to code, read back from a run that succeeds**, at the frame's own gas: the run's
table grows by the callee frame's flag and output, and under the oracle of every extension of it,
SolarTV's STATICCALL pushes that flag and leaves that return data, and the frame after it relates to
SolarTV's state as a block entry does (memory, storage, logs, the budget of memory and gas). -/
theorem staticcall_cutR {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {Tr : List U256}
    {s : State} {evm : Evm .fusaka Nat}
    (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hat : At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: Tr) M g st ss
      rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hPok : ∀ c m ch, P c m ch → StaticOk c m ch)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin)
    (hto : toCode .staticcall (addr.toNat % 2 ^ 160) 0 = true ∨
      PreOk P st ss M g asked addr inOff inSize outOff outSize)
    (hoks : T.oks.length = (machineCalls s.world).length)
    (houts : T.outs.length = (machineCalls s.world).length)
    (hgr : gasReads s.world ≤ T.gases.length) :
    ∃ (ok : Bool) (out : ByteArray) (s' : State) (M' : ByteArray) (g' : Nat)
      (st' : State.TransactionState) (ss' : Substate) (m : Evm .fusaka Nat)
      (within' : GasMeter.gasHeld m.gas ≤ bound),
      (∀ T'', ({ T with oks := T.oks ++ [ok], outs := T.outs ++ [out] } : RunTable).Le T'' →
        Effect.apply (OS codes T'') call (.call .staticcall)
            [asked, addr, inOff, inSize, outOff, outSize] s =
          some (some (if ok then 1 else 0), s') ∧ RdRel (OS codes T'') s'.world out) ∧
      (∃ ev, s'.world = s.world ++ [ev] ∧ sent [ev] = 1 ∧ gasReads [ev] = 0 ∧
        (machineCalls [ev]).length = 1) ∧
      MemRel s'.memory M' ∧ Rel msg ss0 st' ss' s' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) ((if ok then 1 else 0) :: Tr) M' g' st' ss' out m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨calleeCode, route, hcode, hroute, hg, caller, mm, child, after, within', g', hPP, -, hcs,
    hcsub, hms, hmv, hmc, hmt, htg, hmd, hmca, hmdp, hmgas, hg', hat', hrun'⟩ :=
    staticcall_backR hat hlt hbyte hdepth meets within hrun hok
  have hP := hPok _ _ _ hPP
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hb1, hb2, hbud, hfit⟩ := budget_grow2 (pre := (if decide (toAddressMasked addr ∉
    ss.accessedAddresses) then 2600 else 100) +
      routeCost .fusaka (ss.accessedAddresses.insert (toAddressMasked addr)) route) hmod hb hG
    (by omega)
  -- The table with the call's flag and output.
  let T1 : RunTable := { T with oks := T.oks ++ [child.error.isNone], outs := T.outs ++ [child.output] }
  have hle1 : T.Le T1 := ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _⟩
  let ev : Event := .call .staticcall [asked, addr]
    (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
      inOff.toNat inSize.toNat) s.storage s.transient
  have hev : ∀ T'', T1.Le T'' →
      callFlag (OS codes T'') (s.world ++ [ev]) = (if child.error.isNone then 1 else 0) ∧
        RdRel (OS codes T'') (s.world ++ [ev]) child.output := by
    intro T'' hle
    have hok' : T''.oks.getD (machineCalls s.world).length false = child.error.isNone := by
      rw [getD_of_prefix hle.1 (by simp [T1, hoks])]
      simp [T1, hoks]
    have hout' : T''.outs.getD (machineCalls s.world).length .empty = child.output := by
      rw [getD_of_prefix hle.2.1 (by simp [T1, houts])]
      simp [T1, houts]
    have hresp : tabResp T''.oks T''.outs (machineCalls s.world).length .staticcall
        (addr.toNat % 2 ^ 160) 0
        ((((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
          inOff.toNat inSize.toNat).map BitVec.toNat) = (child.error.isNone, child.output) := by
      rcases hto with hto | ⟨h1, hag, hER, hnd, hg3⟩
      · simp only [tabResp, hto, ite_true]
        rw [hok', hout']
      · -- ECRECOVER: the source's answer, which the callee frame matches.
        have htc : toCode .staticcall (addr.toNat % 2 ^ 160) 0 = false := by rw [h1]; decide
        simp only [tabResp, htc, Bool.false_eq_true, ite_false]
        have hrn : route = none := by
          rcases route with _ | ⟨d, c'⟩
          · rfl
          · have := hroute.2.1
            rw [hnd _ hcode] at this
            cases this
        subst hrn
        have hmsg : AssembleCallPre.EcrecoverMsg mm := by
          refine ⟨by rw [htg]; rfl, ?_, by simpa using hmdp, hmv, ?_⟩
          · have h1' : (toAddressMasked addr).toU256.toNat = 1 := by
              rw [toNat_toU256_masked]; exact h1
            simp only [precompileAddress, hmca, routeAddr, h1']
            decide
          · rw [hmgas]
            simpa [routeCost] using hg3
        have hin : (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
            outSize.toNat).read inOff.toNat inSize.toNat).map BitVec.toNat =
            SolidCore.Solidity.Source.byteArrayToBytes mm.data := by
          rw [hmd, ← read_eq2 hm]
          rfl
        rw [h1, hin]
        exact AssembleCallPre.ecrecover_answer hag (hER _ _ _ hPP) hmsg
    obtain ⟨hf, hr⟩ := OS_ans codes T'' s.world asked addr
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient _ _ hresp hP.2.2
    refine ⟨hf, ?_⟩
    have := hr [] rfl
    rw [List.append_nil] at this
    exact this
  -- SolarTV's STATICCALL under the table's oracle.
  obtain ⟨s', happ, hsto, htr, hrd, hw, hmem'⟩ := staticcall_effectW (o := OS codes T1) (call := call)
    (gas := asked) (addr := addr) (child := child) hm hb1 hb2 (hev T1 (RunTable.Le.refl _)).1
    (hev T1 (RunTable.Le.refl _)).2
  -- Under every extension it runs the same.
  have hsame : ∀ T'', T1.Le T'' →
      Effect.apply (OS codes T'') call (.call .staticcall)
          [asked, addr, inOff, inSize, outOff, outSize] s =
        Effect.apply (OS codes T1) call (.call .staticcall)
          [asked, addr, inOff, inSize, outOff, outSize] s := by
    intro T'' hle
    have hmc1 : (machineCalls (s.world ++ [ev])).length = (machineCalls s.world).length + 1 := by
      rw [machineCalls_static]
      simp
    obtain ⟨henv, hres⟩ := OS_le (codes := codes) hle (w := s.world ++ [ev])
      (by simp [T1, hmc1, hoks]) (by simp [T1, hmc1, houts]) (by simp [T1]) (by simp [T1])
      (by simp [T1, ev]; omega)
    have hflag : callFlag (OS codes T'') (s.world ++ [ev]) = callFlag (OS codes T1) (s.world ++ [ev]) := by
      simp only [callFlag, hres]
    have hbyte : returndataByte (OS codes T'') (s.world ++ [ev]) =
        returndataByte (OS codes T1) (s.world ++ [ev]) := by
      funext i
      simp only [returndataByte]
      rw [henv]
    simp only [ev] at henv hflag hbyte
    simp only [Effect.apply, CallKind.shape, called, returndataSize, hflag, henv, hbyte]
  refine ⟨child.error.isNone, child.output, s', _, g', (incorporateChild .fusaka caller child).state,
    (incorporateChild .fusaka caller child).substate, after, within', fun T'' hle => ?_,
    ⟨ev, hw, by simp [ev], by simp [ev], by simp [ev, machineCalls]⟩, hmem', ?_, ?_,
    by omega, ?_, hrun'⟩
  · rw [hsame T'' hle, happ]
    refine ⟨by cases child.error.isNone <;> rfl, ?_⟩
    rw [hw]
    exact (hev T'' hle).2
  · -- Storage and the account are the caller's; the logs are the frame's, with no log of the callee.
    have hso := staticcall_state hcode hroute hP.1 hcs hms hmv hmc hmt htg
    refine ⟨fun k => ?_, ?_, ?_⟩
    · rw [(hso msg.currentTarget (List.not_mem_nil)).2.1, hsto]
      exact R.storage k
    · rw [(hso msg.currentTarget (List.not_mem_nil)).1]
      exact R.account
    · obtain ⟨L, hL1, hL2⟩ := R.logs
      refine ⟨L, ?_, ?_⟩
      · have hlogs : (incorporateChild .fusaka caller child).substate.logs.toList = ss.logs.toList := by
          unfold incorporateChild
          split
          · rename_i hn
            have h0 := hP.2.1 hms (by simpa using hn)
            rcases route with _ | ⟨d, c'⟩ <;> simp [Array.toList_append, h0, hcsub, routeSub]
          · rcases route with _ | ⟨d, c'⟩ <;> simp [hcsub, routeSub]
        rw [hlogs, hL1]
      · rw [hw, List.filter_append]
        simpa [ev, isLogE] using hL2
  · unfold MemBudget
    rw [size_memoryWrite_of_fit, size_memoryExtend]
    · omega
    · intro h
      simp only [ByteArray.size_extract] at h ⊢
      have hz : outSize ≠ 0 := by
        intro hz
        simp [hz] at h
      have := hfit hz
      rw [size_memoryExtend]
      have := Nat.min_le_left outSize.toNat child.output.size
      omega
  · simpa using hat'

/-- **RETURNDATASIZE in a run that succeeds**: the frame had the gas for it, and the run goes on
from the frame after it, with the size of its return data pushed. -/
theorem rds_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {evm : Evm .fusaka Nat} (hat : At code msg pc T M g st ss rd evm) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3d) (hstack : T.length < STACK_LIMIT) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    2 ≤ g ∧ ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) (BitVec.ofNat 256 rd.size :: T) M (g - 2) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 2 ≤ g
  · obtain ⟨m, hr, hm⟩ := returndatasize_rule hlt hbyte hg hstack evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc T M g st ss rd) (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, -, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .returndatasize := by
        rw [hbyte]
        exact ofByte_of_decode rfl (by decide)
      rw [step_of_instruction hlt decoded rfl]
      simp [readFrame, chargeGas, GasMeter.charge, hgas, OPCODE_RETURNDATASIZE, BASE,
        show g < 2 by omega, bind, Except.bind]
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **RETURNDATACOPY in a run that succeeds**: the range was within the return data, the frame had
the gas for the copy and the growth of memory, and the run goes on from the frame after it. -/
theorem rdc_backR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    off.toNat + sz.toNat ≤ rd.size ∧
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat (memoryReadBytes rd off.toNat sz.toNat))
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  have decoded : Op.ofByte .fusaka (0x3e : UInt8) = some .returndatacopy :=
    ofByte_of_decode rfl (by decide)
  by_cases hg : 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g
  · by_cases hfit : off.toNat + sz.toNat ≤ rd.size
    · obtain ⟨m, hr, hm⟩ := returndatacopy_rule hlt hbyte hfit hg evm hat
      have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
      rw [this] at hrun
      exact ⟨hfit, hg, m, _, hm, hrun⟩
    · exfalso
      have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss rd)
          (Faulted .outOfBoundsRead st ss) := by
        refine At.fault rfl fun e hat' => ?_
        obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -, -, -, -, -, hrd⟩ := hat'
        subst hcode hpc
        rw [step_of_instruction hlt (by rw [hbyte]; exact decoded) AssembleCallSeg.instruction_returndatacopy]
        have hpaid : GasMeter.charge e.gas (OPCODE_RETURNDATACOPY_BASE +
            OPCODE_RETURNDATACOPY_PER_WORD * wordCount sz.toNat +
            (extendMemory e.memory.size [(d, sz)]).cost) = .ok (g - (3 + 3 * wordCount sz.toNat +
              (extendMemory M.size [(d, sz)]).cost)) := by
          rw [hmem, hgas, show OPCODE_RETURNDATACOPY_BASE = 3 from rfl,
            show OPCODE_RETURNDATACOPY_PER_WORD = 3 from rfl]
          exact charge_nat hg
        rw [(returndatacopyStep_eq_error_iff hst hpaid).2 (by rw [hrd]; omega)]
        rfl
      obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
      rw [runFrame_of_reaches hr hstop within] at hrun
      cases hrun
      rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      rw [step_of_instruction hlt (by rw [hbyte]; exact decoded) AssembleCallSeg.instruction_returndatacopy]
      have hlt' : g < 3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost :=
        Nat.lt_of_not_le hg
      have hc : GasMeter.charge e.gas (OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD *
          wordCount sz.toNat + (extendMemory e.memory.size [(d, sz)]).cost) = .error .outOfGas := by
        rw [hgas, hmem, show OPCODE_RETURNDATACOPY_BASE = 3 from rfl,
          show OPCODE_RETURNDATACOPY_PER_WORD = 3 from rfl]
        simp only [GasMeter.charge]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hlt')]
      rw [returndatacopyStep_oog hst hc]
      rfl
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rcases hok with hok | hok <;> rw [hf.2.1] at hok <;> cases hok

/-- **RETURNDATACOPY of any range, in a run that succeeds**: with the budget below `2 ^ 300` and an
oracle that answers the frame's return data, SolarTV's copy agrees with EthLib's memory after it,
the budget holds at the gas left, and the run goes on. -/
theorem rdc_dynR {code : ByteArray} {msg : Message .fusaka} {o : Oracle} {w : List Event}
    {pc : Nat} {d off sz : Word} {T : List Word} {M : ByteArray} {g G : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} {m0 : SolarTV.Machine.Mem}
    (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300) (hrdr : RdRel o w rd)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : OkR fin) :
    off.toNat + sz.toNat ≤ rd.size ∧
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => returndataByte o w (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hfit0, hg, m, within', hat', hrun'⟩ := rdc_backR hat hlt hbyte within hrun hok
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
  refine ⟨hfit0, _, _, m, within', ?_, ?_, by omega, hat', hrun'⟩
  · have he := memRel_expandW hm hbound
    rw [← write_expand]
    refine memRel_write he hfit (size_memoryReadBytes hfit0) (fun i hi => ?_)
    rw [byteAt_memoryReadBytes hfit0, if_pos hi]
    exact (hrdr.2 (off.toNat + i) (by omega)).symm
  · refine MemBudget.grow hmod hb hg ?_
    rw [size_memoryWrite_of_fit, size_memoryExtend]
    intro h
    rw [size_memoryReadBytes hfit0] at h ⊢
    exact hfit h

end Dyn

set_option maxRecDepth 8000 in
/-- **`AssembleCut.seg` with STATICCALLs**: the rest of a block from an instruction, read back from
a run that succeeds, under the oracle of the run's table of GAS reads and static calls. -/
theorem segSR {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobT p c code) (codes : SolidCore.Solidity.Shared.Account.BytesMap) (hcr : c.creates = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    {b : Nat} (hb : b < p.blocks.length) {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {fin : Evm .fusaka Nat} (hok : OkR fin) {G0 : Nat} (hG0 : G0 < 2 ^ 256)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hPok : ∀ c m ch, P c m ch → StaticOk c m ch)
    (hcal : CalleesOk code msg P bound runChild fin) :
    ∀ (n : Nat) (is : List Assemble.Instr) (h : Nat) (known : Known) (ty : List Ty) (k : Nat)
      (S Tw : List Word) (s : State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate) (rd : ByteArray) (T : RunTable) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound),
      is.length < n → blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S Tw →
      Seg (bytesOf code) c.offset pc
        (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size →
      S.length + k ≤ 1000 → M.size ≤ c.top → MemRel s.memory M → Rel msg ss0 st ss s →
      At code msg pc Tw M g st ss rd evm → T.gases.length = gasReads s.world →
      TabInv T s.world → (∀ T'', T.Le T'' → RdRel (OS codes T'') s.world rd) →
      MemBudget G0 M g →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      ∃ T' r, T.Le T' ∧
        (∀ T'', T'.Le T'' → SolarTV.EVM.Program.exec (OS codes T'') call b is S s = r) ∧
        (∀ res, r = .inl res → PostL call msg.currentTarget ss0 res.2 res.1 fin) ∧
        (∀ y, r = .inr y → (y.1 ≤ p.blocks.length ∧
          (y.1 < p.blocks.length → c.need y.1 ≤ y.2.1.length ∧ y.2.1.length ≤ maxH mx y.1) ∧
          (y.1 = b + 1 ∨ isTarget p c y.1 = true)) ∧
          ∃ (after : Evm .fusaka Nat) (within' : GasMeter.gasHeld after.gas ≤ bound),
            EntC p c mx code msg ss0 y after ∧ T'.gases.length = gasReads y.2.2.world ∧
            TabInv T' y.2.2.world ∧
            (∀ T'', T'.Le T'' → RdRel (OS codes T'') y.2.2.world after.returnData) ∧ after.gas ≤ g ∧
            memoryGasCost after.memory.size + after.gas ≤ G0 ∧
            runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, is, h, known, ty, k, S, Tw, s, pc, M, g, st, ss, rd, T, evm, within, hn, hokC, hh, hu, hk,
      hR, hseg, hstk, htop, hmem, R, hat, hTg, hs0, hrdr, hB, hrun => by
    have hge : evm.gas = g := hat.2.2.2.2.2.2.1
    -- The segment with gas to spare for it alone: `K` more than the frame holds.
    generalize hK : 22100 * k + memoryGasCost c.top = K
    have hp := hat.addGas K
    have I : InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1)
        (p.blocks.drop (b + 1))) k 0 pc S s M (g + K) :=
      ⟨hseg, hstk, by simp only [Nat.add_zero]; omega, htop, hmem⟩
    have hsim := exec_simC (mx := mx) G (o := OS codes T) hdata hvalue hstatic hself hcaller
      (OS_ok codes c T).1 hbenv htx (OS_ok codes c T).2 b hb 0 (G0 + K) rd is h known ty S Tw k s pc M
      (g + K) st ss hokC hh hu hk hR I R (by unfold MemBudget at *; omega)
    have hcnt := (execC_agree (Agree.refl (OS codes T) (gasReads s.world) (sent s.world)) call b is S s
      le_rfl le_rfl).2
    have hex : ∀ T'', T.Le T'' → SolarTV.EVM.Program.exec (OS codes T'') call b is S s =
        match execC (OS codes T) call b is S s with
        | .done r => r
        | .cut i rest S' s' => SolarTV.EVM.Program.exec (OS codes T'') call b (i :: rest) S' s' :=
      fun T'' hle => exec_OS codes hle (by omega) hs0
    generalize hr : execC (OS codes T) call b is S s = r at hsim hcnt hex
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
          E'.le_top, E'.mem, R', hatm⟩, ?_, ?_, ?_, by omega,
          by rw [hatm.2.2.2.2.2.1]; unfold MemBudget at hB'; omega, hrm⟩
        · dsimp only; omega
        · exact TabInv.of_seg hc1.2 (execC_calls _ _ _ is S s s' (by rw [hr]; rfl)) hs0
        · intro T'' hle
          rw [hatm.2.2.2.2.2.2.2.2.2.2.2.2]
          exact rdRel_world codes (execC_calls _ _ _ is S s s' (by rw [hr]; rfl)) (hrdr T'' hle)
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
      have hmc := execC_calls (OS codes T) call b is S s s' (by rw [hr]; rfl)
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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself hcaller hbenv
          htx hb hok hG0 hdepth meets hPok hcal n rest (h' + 1) [] (some false :: ty') (k' - 1)
          (BitVec.ofNat 256 (m.gas - 2) :: S') (BitVec.ofNat 256 (m.gas - 2) :: T')
          { s' with world := s'.world ++ [.read "gas"] } (pc' + 1) M' (m.gas - 2) st' ss' rd T1 m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
          I'.mem ⟨R'.storage, R'.account, logsRel_read _ R'.logs⟩ hat2
          (by simp [T1]; omega) (TabInv.read (TabInv.of_seg hc1.2 hmc hs0))
          (fun T3 hle => rdRel_world codes (by rw [machineCalls_read, hmc]) (hrdr T3 (hle1.trans hle)))
          (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, r, hle1.trans hle2, fun T'' hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T'' (hle1.trans (hle2.trans hle))]
          show SolarTV.EVM.Program.exec (OS codes T'') call b (.effect .gas 0 :: rest) S' s' = r
          rw [exec_gasS codes (hv T'' (hle2.trans hle)) (by omega)]
          exact hex2 T'' hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest h' [] (some false :: ty'.drop 1) (k' - 1)
          (s'.memory.load x.toNat :: S'') (s'.memory.load x.toNat :: Tr)
          { s' with memory := s'.memory.expand x.toNat 32 } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (TabInv.of_seg hc1.2 hmc hs0) (fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.op .load :: rest) _ s' = r
          rw [exec_loadC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩
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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 2) [] (ty'.drop 2) (k' - 1) S'' Tr
          { s' with memory := s'.memory.store x.toNat y } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (TabInv.of_seg hc1.2 hmc hs0) (fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.op .store :: rest) _ s' = r
          rw [exec_storeC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨-, hkec⟩ := (OS_ok codes c T).1 henv
        rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hat2
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 1) [] (some false :: ty'.drop 2) (k' - 1)
          ((OS codes T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S'')
          ((OS codes T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: Tr)
          { s' with memory := s'.memory.expand x.toNat y.toNat } (pc' + 1) _ _ st' ss' rd T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (TabInv.of_seg hc1.2 hmc hs0) (fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.effect .keccak256 2 :: rest) _ s' = r
          rw [exec_keccakC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2', r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) (ss0 := ss0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - (tops.length + 2)) [] (ty'.drop (tops.length + 2))
          (k' - 1) S2 T2
          ⟨s'.memory.expand x.toNat y.toNat, s'.storage, s'.transient,
            s'.world ++ [.log tops ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩
          (pc' + 1) _ _ st' { ss' with logs := ss'.logs.push ⟨msg.currentTarget,
            tops.map U256.toBeBytes, memoryReadBytes (memoryExtend M' (extendMemory M'.size
              [(x, y)]).expandBy) x.toNat y.toNat⟩ } rd T m2 within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2
          ⟨R'.storage, R'.account, ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy)
                x.toNat y.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, read_eq I'.mem⟩⟩⟩ hat2
          (by show T.gases.length = gasReads (s'.world ++ [_]); rw [AssembleCut.gasReads_log, hc1.1]; exact hTg)
          (TabInv.log (TabInv.of_seg hc1.2 hmc hs0))
          (fun T3 hle => rdRel_world codes (by rw [machineCalls_log, hmc]) (hrdr T3 hle)) hb2 hrun2
        refine ⟨T2', r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b
            (.effect (.log tops.length) (tops.length + 2) :: rest) _ s' = r
          rw [exec_logC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) (ss0 := ss0) G codes (hcr := hcr) hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 3) [] (ty'.drop 3) (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => SolarTV.Machine.calldataByte call (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (TabInv.of_seg hc1.2 hmc hs0) (fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.effect .calldatacopy 3 :: rest) _ s' = r
          rw [exec_cdcC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩
      · -- STATICCALL to code at the frame's gas: the callee frame's flag and output join the table.
        obtain rfl := isScI_eq hsci
        obtain ⟨-, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_sc hok2
        have hs := I'.seg
        rw [lowerInstrs_sc, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, S''⟩⟩⟩⟩⟩⟩
        all_goals (first | (simp at hh2; omega) | skip)
        rcases T' with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, Tr⟩⟩⟩⟩⟩⟩
        all_goals (first | (simp at hL; done) | skip)
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 6) S'' Tr := by simpa using SR.drop 6 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        have hco := hcal hatm hlt hcode hrm
        obtain ⟨hi1, hi2, hi3⟩ := hs0
        obtain ⟨ok, out, s2, M2, g2, st2, ss2, m2, within2, happ, ⟨ev, hw, hev1, hev2, hev3⟩, hmem2,
          R2, hb2, hg2, hat2, hrun2⟩ := staticcall_cutR codes T I'.mem R' hmB (by omega) hatm hlt hcode
            hdepth meets hPok within1 hrm hok hco (by rw [hmc, hi2]) (by rw [hmc, hi2, hi3])
            (by rw [hc1.1]; omega)
        let T1 : RunTable := { T with oks := T.oks ++ [ok], outs := T.outs ++ [out] }
        have hle1 : T.Le T1 := ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_refl _⟩
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        have hinv : TabInv T1 s2.world := by
          refine ⟨?_, ?_, ?_⟩
          · rw [hw, AssembleCallSeg.sent_append, hev1, hc1.2, hi1]
            simp [T1]
          · rw [hw, AssembleCallSeg.machineCalls_append, List.length_append, hev3, hmc, hi2]
            simp [T1]
          · simp [T1, hi3]
        have hTg1 : T1.gases.length = gasReads s2.world := by
          rw [hw, AssembleCallSeg.gasReads_append, hev2, hc1.1]
          simpa [T1] using hTg
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic
          hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 5) []
          (some false :: ty'.drop 6) (k' - 1) ((if ok then 1 else 0) :: S'')
          ((if ok then 1 else 0) :: Tr) s2 (pc' + 1) M2 g2 st2 ss2 out T1 m2 within2 (by omega) hok3
          (by simp; omega) (by simp; omega) (KR.nil _) (SR.cons (τ := some false) rfl hR'')
          hseg' (by simp; omega) hsz hmem2 R2 hat2 hTg1 hinv (fun T3 hle => (happ T3 hle).2) hb2 hrun2
        refine ⟨T2, r, hle1.trans hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle1.trans (hle2.trans hle))]
          show SolarTV.EVM.Program.exec (OS codes T3) call b
            (.effect (.call .staticcall) 6 :: rest) _ s' = r
          rw [exec_scC (happ T3 (hle2.trans hle)).1 (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩
      · -- RETURNDATASIZE at the frame's gas: the size of the frame's return data, the table's.
        obtain rfl := isRdsI_eq hrdi
        obtain ⟨-, hk1, hok3⟩ := blockOkC_rds hok2
        have hs := I'.seg
        rw [lowerInstrs_rds, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        obtain ⟨h2, m2, within2, hat2, hrun2⟩ :=
          rds_backR hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
        have hrd' : ∀ T3, T.Le T3 → RdRel (OS codes T3) s'.world rd :=
          fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)
        have hv : ∀ T3, T.Le T3 →
            (OS codes T3).env "returndatasize" s'.world [] = BitVec.ofNat 256 rd.size := by
          intro T3 hle
          have h1 := (hrd' T3 hle).1
          simp only [returndataSize] at h1
          have hlt' : rd.size < 2 ^ 256 := by rw [← h1]; exact BitVec.isLt _
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt hlt']
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic
          hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' + 1) [] (some false :: ty')
          (k' - 1) (BitVec.ofNat 256 rd.size :: S') (BitVec.ofNat 256 rd.size :: T') s' (pc' + 1) M'
          (m.gas - 2) st' ss' rd T m2 within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
          I'.mem R' hat2 (by rw [hc1.1]; exact hTg) (TabInv.of_seg hc1.2 hmc hs0) hrd'
          (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.effect .returndatasize 0 :: rest) S' s' = r
          rw [exec_rdsC (hv T3 (hle2.trans hle)) (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩
      · -- RETURNDATACOPY at the frame's gas, of any range within the return data.
        obtain rfl := isRdcI_eq hrdci
        obtain ⟨-, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_rdc hok2
        have hs := I'.seg
        rw [lowerInstrs_rdc, List.cons_append] at hs
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
        have hrd' : ∀ T3, T.Le T3 → RdRel (OS codes T3) s'.world rd :=
          fun T3 hle => rdRel_world codes hmc (hrdr T3 hle)
        obtain ⟨hfit, M2, g2, m2, within2, hmem2, hb2, hg2, hat2, hrun2⟩ :=
          rdc_dynR I'.mem hmB (by omega) (hrd' T (RunTable.Le.refl T)) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        have hext : ∀ T3, T.Le T3 → returndataByte (OS codes T3) s'.world =
            returndataByte (OS codes T) s'.world := by
          intro T3 hle
          funext i
          simp only [returndataByte]
          rw [OS_env_ext codes hle (by rw [hmc, hs0.2.1]) (by rw [hmc, hs0.2.1, hs0.2.2])
            (by rw [hc1.1]; omega) (by decide)]
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segSR (G0 := G0) G codes (hcr := hcr) hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 3) [] (ty'.drop 3)
          (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => returndataByte (OS codes T) s'.world (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd
          T m2 within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by rw [hc1.1]; exact hTg) (TabInv.of_seg hc1.2 hmc hs0) hrd' hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (OS codes T3) call b (.effect .returndatacopy 3 :: rest) _ s' = r
          rw [exec_rdcC (by rw [(hrd' T3 (hle2.trans hle)).1]; exact hfit) (by omega),
            hext T3 (hle2.trans hle)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, hrdy, by omega, hbud, hra⟩
      · -- CALL, CREATE2 and CODECOPY: only a certificate that says the program creates lets the
        -- checker cut there.
        obtain rfl := isCallI_eq hcalli
        exact absurd (blockOkC_call hok2).2.1 (by simp [hcr])
      · obtain rfl := isC2I_eq hc2i
        exact absurd (blockOkC_c2 hok2).2.1 (by simp [hcr])
      · obtain rfl := isCcI_eq hcci
        exact absurd (blockOkC_cc hok2).2.1 (by simp [hcr])

section BlocksQ

variable {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
  (O : RunTable → Oracle)

/-- **One block of the simulation, read back from a run that succeeds**, as
`AssembleCall.AdvancesS` under every runner of messages meeting `P`, for the runs to a frame `fin`
that meet the hypothesis `Q`. -/
def AdvancesQR (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets P runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      OkR fin → Q bound runChild fin →
      ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

/-- A run of EthLib that ends with no error and meets the hypothesis is SolarTV's, for every table
extending the last one the run grew. -/
theorem run_of_advancesQR {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop}
    {Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop}
    {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → AdvancesQR blk O P Q E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets P runChild) :
    ∀ (n : Nat) (T : RunTable) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      OkR fin → Q bound runChild fin →
      ∃ T' res, T.Le T' ∧
        (∀ T'', T'.Le T'' → ∃ k, SolarTV.Machine.iterate (blk (O T'')) k x = some res) ∧
        Post res fin
  | 0, _, _, _, _, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, T, x, evm, within, fin, hE, hm, hrun, hok, hq => by
    obtain ⟨T', r, hle, hstep, hinl, hinr⟩ :=
      adv T x evm hE bound runChild meets within fin hrun hok hq
    cases r with
    | inl res =>
      exact ⟨T', res, hle, fun T'' h => ⟨1, by simp [SolarTV.Machine.iterate, hstep T'' h]⟩,
        hinl res rfl⟩
    | inr y =>
      obtain ⟨after, within', hE', hm', hrun'⟩ := hinr y rfl
      obtain ⟨T2, res, hle2, hit, hpost⟩ :=
        run_of_advancesQR adv meets n T' y after within' fin hE' (by omega) hrun' hok hq
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [SolarTV.Machine.iterate, hstep T'' (hle2.trans h), hk]⟩

end BlocksQ

/-- **A block of code with loops, GAS and STATICCALLs, read back from a run that succeeds.** -/
theorem advances_checkCSR {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobC p c mx code) (codes : SolidCore.Solidity.Shared.Account.BytesMap) (hcr : c.creates = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntS codes p c mx code msg ss0 T0 x evm) :
    AdvancesQR (fun o => SolarTV.EVM.Program.block o call p) (OS codes) StaticOkE
      (CalleesOk code msg StaticOkE)
      (EntS codes p c mx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p c e.gas y.1) T0 x evm := by
  intro bound runChild meets within fin hrun hok hcal
  obtain ⟨b, S, s⟩ := x
  obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hrdr, hbud⟩ := hE
  simp only at hle hneed hR hseg hmem R hTg hs0 hrdr
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
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := segSR (G0 := msg.gas) G.toGlobT codes (hcr := hcr) hdata hvalue hstatic hself hcaller
      hbenv htx hb hok hgas hdepth meets (fun _ _ _ h => h.1) hcal (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss rd T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) (KR.nil _) hR hseg1 (by omega) htop hmem R hat1 hTg hs0
      (by rw [← hat.2.2.2.2.2.2.2.2.2.2.2.2]; exact hrdr)
      (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨T', r, hle', fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T'' h]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj⟩, after, within', hE', hT', hs', hrdy', hga, hbud', hra⟩ := hnext _ hy
      refine ⟨after, within', ⟨hE', hT', hs', hrdy', hbud'⟩, ?_, hra⟩
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


open EthLib.Execution.State in
/-- **Named hypothesis on a run**: `AssembleCallSeg.CalleesRun` for every run of the message's frame
that ends with no error or reverts (`CalleesOk` at each of its STATICCALLs). -/
def CalleesRunE (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ (st' : TransactionState) (ss' : Substate)
    (within : GasMeter.gasHeld (startFrame (Final.Target.messageWith gas code call) st' ss'
      (Final.Target.messageWith gas code call).gas).gas ≤ (Final.Target.messageWith gas code call).gas)
    (fr : Evm .fusaka Nat),
    runFrame (step .fusaka) (step_decreases .fusaka) (Final.Target.messageWith gas code call).gas
      (processRunner .fusaka (Final.Target.messageWith gas code call).gas)
      (startFrame (Final.Target.messageWith gas code call) st' ss'
        (Final.Target.messageWith gas code call).gas) within = .ok fr → OkR fr →
    CalleesOk code (Final.Target.messageWith gas code call) StaticOkE gas
      (processRunner .fusaka (Meter := Nat) gas) fr

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **`AssembleCallSeg.within_of_advancesQ` with the revert data related.** -/
theorem within_of_advancesQR {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (hP : Meets P (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas))
    (hQ : ∀ (st' : EthLib.Execution.State.TransactionState) (ss' : Substate)
      (within : GasMeter.gasHeld (startFrame (Final.Target.messageWith gas code call) st' ss'
        (Final.Target.messageWith gas code call).gas).gas ≤
          (Final.Target.messageWith gas code call).gas) (fr : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) (Final.Target.messageWith gas code call).gas
        (processRunner .fusaka (Final.Target.messageWith gas code call).gas)
        (startFrame (Final.Target.messageWith gas code call) st' ss'
          (Final.Target.messageWith gas code call).gas) within = .ok fr → OkR fr →
      Q _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas) fr)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesQR (fun o => block o call p) O P Q (E ss0)
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
  · obtain ⟨T, hT⟩ := within_of_advancesQ O P Q E meas hP
      (fun r hr he => by
        obtain ⟨st', ss', within, -, -, hrf⟩ := AssembleRun.processMessage_ok'
          (message := Final.Target.messageWith gas code call) (evm := r)
          (precompileAddress_message code call) hr he
        exact hQ st' ss' within r.1 hrf (.inl he))
      start (fun ss0 T x evm h b rc m w f hr he hq => adv ss0 T x evm h b rc m w f hr (.inl he) hq)
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
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advancesQR (fun o => block o call p) O (adv ss')
    hP _ {} _ _ within fr (start st' ss' R) (Nat.lt_succ_self _) hrf (.inr hfrrev)
    (hQ st' ss' within fr hrf (.inr hfrrev))
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

/-- **EVM IR to bytecode, run by run, for code with loops, GAS, memory at any offset and
STATICCALLs to code, with the revert data related**: for every program the checker without the
no-call gate accepts, at every gas below `2 ^ 256` and every call whose run meets the named
hypotheses, the oracle of the run's table makes every result of the bytecode the EVM IR's (a
revert with its data among them), unless the run halted exceptionally. -/
theorem runs_of_checkCBR {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCB p code c mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) (hP : StaticRunner gas)
    (hQ : CalleesRunE gas code call) :
    ∃ T, WithinR (evmirSem (OS codes T)) gas p code (· = call) := by
  obtain ⟨G, hseg, hneed0⟩ := globC_of_checkC hc
  refine within_of_advancesQR (OS codes) StaticOkE
    (CalleesOk code (Final.Target.messageWith gas code call) StaticOkE)
    (fun ss0 => EntS codes p c mx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p c e.gas y.1) (staticOkE_of gas hP) hQ (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkCSR G codes (hcr := checkCB_creates hc) rfl
      (by simp [Final.Target.messageWith, SolidCore.Refinement.Target.message]) rfl rfl rfl rfl rfl
      hgas (by show 0 + 1 ≤ 1024; decide) T x evm hE)
  refine ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hneed0], by simp⟩,
    SR.nil c _, by rw [List.drop_zero]; exact hseg, by simp, memRel_initial, R, ?_⟩, rfl,
    ⟨rfl, rfl, rfl⟩, fun T'' _ => rdRel_nil codes T'', ?_⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertCall.runs_of_checkCBR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runs_of_checkCBR

end SolidCore.Refinement.Solar.AssembleRevertCall

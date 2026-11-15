import SolidCore.Refinement.Solar.AssembleCallValueSeg
import SolidCore.Refinement.Solar.AssembleCallValueZero

/-!
# CALL with no value as a cut of a run, at the frame's own gas

`call0_cut` is `AssembleCallValueSeg.callValue_cut` for a CALL that sends no value, as UniswapV2Factory's
call to the new pair's `initialize` is: from a run that succeeds, the CALL read the callee's code (and its
delegate's, `AssembleCallValueZero.call0_back`, so nothing is assumed of the callee's code or route), had
the gas for its access, the route and the growth of memory, and the run goes on from the frame after
the callee's frame ended. The run's table grows by the flag, the return data and the storage of the
frame's account after the call (a reentrant callee may have changed it), and under the oracle of every
extension of it SolarTV's CALL does the same (`call_answers`, for any call with its value word).

Named: `AssembleCallValueSeg.CallOk` of the frame that ends the call's message, asked only of messages to
this callee with this input, no value and not static.
-/

namespace SolidCore.Refinement.Solar.AssembleCallValueZeroSeg

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCallValueEffect SolidCore.Refinement.Solar.AssembleCallValueSeg
open SolidCore.Refinement.Solar.AssembleCreateSeg SolidCore.Refinement.Solar.AssembleCall
open SolidCore.Refinement.Solar.AssembleCallValueZero
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- **SolarTV's CALL under every extension of a table with the call's answers**: it pushes the flag,
writes the output to the output range, takes it as the return data and leaves the table's storage. -/
theorem call_answers {base : Oracle} {T : RunTable} {call : Call} {s : State} {M : ByteArray}
    {gas addr value inOff inSize outOff outSize : Word} (hm : MemRel s.memory M)
    (hb1 : inSize = 0 ∨ (inOff.toNat + inSize.toNat + 31) / 32 < 2 ^ 251)
    (hb2 : outSize = 0 ∨ (outOff.toNat + outSize.toNat + 31) / 32 < 2 ^ 251)
    (hsent : sent (callWorld s gas addr value inOff inSize outOff outSize) = T.oks.length + 1)
    (houts : T.outs.length = T.oks.length) (hst : T.stores.length = T.oks.length)
    (htr : T.transients.length = T.oks.length)
    (ok : Bool) (out : ByteArray) (sto : Word → Word) (hsz : out.size < 2 ^ 256) :
    ∃ s', (∀ T'', (pushCall T ok out sto).Le T'' →
        Effect.apply (tableOracle base T'') call (.call .call)
            [gas, addr, value, inOff, inSize, outOff, outSize] s =
          some (some (if ok then 1 else 0), s') ∧ RdRel (tableOracle base T'') s'.world out) ∧
      s'.storage = sto ∧ s'.world = callWorld s gas addr value inOff inSize outOff outSize ∧
      MemRel s'.memory (memoryWrite (memoryExtend M
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
        outOff.toNat (out.extract 0 (min outSize.toNat out.size))) := by
  have hsame : ∀ T'', (pushCall T ok out sto).Le T'' →
      Effect.apply (tableOracle base T'') call (.call .call)
          [gas, addr, value, inOff, inSize, outOff, outSize] s =
        Effect.apply (tableOracle base (pushCall T ok out sto)) call (.call .call)
          [gas, addr, value, inOff, inSize, outOff, outSize] s := by
    intro T'' hle
    obtain ⟨r1, o1, s1, t1⟩ := table_call (base := base) hsent houts hst htr hle
    obtain ⟨r2, o2, s2, t2⟩ := table_call (base := base) hsent houts hst htr
      (RunTable.Le.refl (pushCall T ok out sto))
    have hrds : returndataSize (tableOracle base T'') (callWorld s gas addr value inOff inSize outOff outSize) =
        returndataSize (tableOracle base (pushCall T ok out sto))
          (callWorld s gas addr value inOff inSize outOff outSize) := by
      rw [returndataSize_table, returndataSize_table, o1, o2]
    have hrdb : returndataByte (tableOracle base T'') (callWorld s gas addr value inOff inSize outOff outSize) =
        returndataByte (tableOracle base (pushCall T ok out sto))
          (callWorld s gas addr value inOff inSize outOff outSize) := by
      funext j
      simp only [returndataByte, tableOracle, o1, o2]
      simp
    have hflag : callFlag (tableOracle base T'') (callWorld s gas addr value inOff inSize outOff outSize) =
        callFlag (tableOracle base (pushCall T ok out sto))
          (callWorld s gas addr value inOff inSize outOff outSize) := by
      simp only [callFlag, r1, r2]
    simp only [callWorld] at hrds hrdb hflag s1 s2 t1 t2
    simp only [Effect.apply, CallKind.shape, called, hflag, hrds, hrdb, s1, s2, t1, t2]
  obtain ⟨r2, o2, s2, -⟩ := table_call (base := base) (ok := ok) (out := out) (sto := sto) hsent
    houts hst htr (RunTable.Le.refl _)
  have hrd2 : RdRel (tableOracle base (pushCall T ok out sto))
      (callWorld s gas addr value inOff inSize outOff outSize) out := by
    have := rdRel_table base (pushCall T ok out sto)
      (callWorld s gas addr value inOff inSize outOff outSize) (by rw [o2]; exact hsz)
    rwa [o2] at this
  obtain ⟨s', happ, hsto, hw, hmem⟩ := call_effectO (o := tableOracle base (pushCall T ok out sto))
    (call := call) (ok := ok) hm hb1 hb2 (by simp only [callFlag, r2]; cases ok <;> simp) hrd2
  refine ⟨s', fun T'' hle => ⟨by rw [hsame T'' hle, happ], ?_⟩, by rw [hsto, s2], hw, hmem⟩
  obtain ⟨-, o1, -, -⟩ := table_call (base := base) hsent houts hst htr hle
  have := rdRel_table base T'' (callWorld s gas addr value inOff inSize outOff outSize)
    (by rw [o1]; exact hsz)
  rw [o1] at this
  rw [hw]
  exact this

/-- **CALL with no value as a cut of a run that succeeds.** -/
theorem call0_cut {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : U256} {Tr : List U256} {s : State}
    {evm : Evm .fusaka Nat} (base : Oracle) (T : RunTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hat : At code msg pc (asked :: addr :: 0 :: inOff :: inSize :: outOff :: outSize :: Tr) M g st
      ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hq : ∀ caller m child, P caller m child → m.currentTarget = toAddressMasked addr →
      m.value = 0 → m.isStatic = false →
      m.data = memoryReadBytes (memoryExtend M
        (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy) inOff.toNat inSize.toNat →
      CallOk msg child)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none)
    (hoks : T.oks.length = sent s.world) (houts : T.outs.length = sent s.world)
    (hsts : T.stores.length = sent s.world) (htrs : T.transients.length = sent s.world) :
    ∃ (ok : Bool) (out : ByteArray) (s' : State) (st' : State.TransactionState) (ss' : Substate)
      (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      (∀ T'', (pushCall T ok out (storeOf st' msg.currentTarget)).Le T'' →
        Effect.apply (tableOracle base T'') call (.call .call)
            [asked, addr, 0, inOff, inSize, outOff, outSize] s =
          some (some (if ok then 1 else 0), s') ∧ RdRel (tableOracle base T'') s'.world out) ∧
      s'.world = callWorld s asked addr 0 inOff inSize outOff outSize ∧
      MemRel s'.memory M' ∧ Rel msg ss0 st' ss' s' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) ((if ok then 1 else 0) :: Tr) M' g' st' ss' out m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨calleeCode, route, -, -, hgp, caller, mm, child, after, within', g', hP, -, -, hcsub, hms,
    hmv, -, hmt, -, hmd, -, -, -, hg', hat', hrun'⟩ :=
    call0_back hat hlt hbyte hstatic hdepth meets within hrun hok
  obtain ⟨hb1, hb2, hbud, hfit⟩ := AssembleCallCut.budget_grow2 hmod hb hG hgp
  obtain ⟨hacc, hlogs, hout⟩ := hq caller mm child hP hmt hmv hms hmd
  have hsent : sent (callWorld s asked addr 0 inOff inSize outOff outSize) = T.oks.length + 1 := by
    simp [callWorld, hoks]
  obtain ⟨s', hall, hsto, hw, hmem⟩ := call_answers (base := base) (call := call) hm hb1 hb2 hsent
    (by omega) (by omega) (by omega) child.error.isNone child.output
    (storeOf (incorporateChild .fusaka caller child).state msg.currentTarget) hout
  refine ⟨child.error.isNone, child.output, s', _, _, _, g', after, within', hall, hw, hmem,
    ⟨fun k => by rw [hsto]; rfl, ?_, ?_⟩, ?_, by omega, hat', hrun'⟩
  · rw [incorporateChild_state]
    exact hacc
  · have hl : (incorporateChild .fusaka caller child).substate.logs.toList = ss.logs.toList := by
      unfold incorporateChild
      split
      · rename_i hn
        have h0 := hlogs (by simpa using hn)
        rcases route with _ | ⟨d, c'⟩ <;> simp [Array.toList_append, h0, hcsub, routeSub]
      · rcases route with _ | ⟨d, c'⟩ <;> simp [hcsub, routeSub]
    obtain ⟨L, h1, h2⟩ := R.logs
    refine ⟨L, by rw [hl, h1], ?_⟩
    rw [hw, callWorld, List.filter_append]
    simpa [isLogE] using h2
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

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValueZeroSeg.call0_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call0_cut

end SolidCore.Refinement.Solar.AssembleCallValueZeroSeg

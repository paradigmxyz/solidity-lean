import SolidCore.Refinement.Solar.AssembleCallValue
import SolidCore.Refinement.Solar.AssembleCallCut
import SolidCore.Refinement.Solar.AssembleCreateSeg

/-!
# CALL with value as a cut of a run, at the frame's own gas

`callValue_cut` is the step the checker's segments take at a CALL that sends a nonzero value: from a
run of the bytecode that succeeds, the CALL had its price (`AssembleCallValue.callValue_back`: EIP-2929
access, 9000 for the value, 25000 for a dead callee, the growth of memory, EIP-150 forwarding with the
stipend) and the run goes on from the frame after it. The run's table (`RunOracle.RunTable`) grows by
the call's success flag, its return data and the storage of the frame's account after it (a callee
may reenter the frame and change it), and under the oracle of every extension of it
(`RunOracle.tableOracle`) SolarTV's CALL pushes the same flag, writes the same output, takes the same
return data and leaves that storage: every relation of a block entry holds again.

When the frame lacks the value there is no message: 0 pushed, no return data, the stipend given back.

Named, as for STATICCALL (`AssembleCallSeg.CalleesOk`): the callee's code is in the state and is no
EIP-7702 delegation (`callValue_back`'s premises), and `CallOk` of the frame that ends this call's message
(asked only of the message this step sends, with its input, value and gas, from the caller state the
step leaves): the frame's account still exists after it, a call that succeeds adds no log (SolarTV's
world records only the frame's own logs), and its output has fewer than `2 ^ 256` bytes.
-/

namespace SolidCore.Refinement.Solar.AssembleCallValueSeg

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCallValue SolidCore.Refinement.Solar.AssembleCallValueEffect
open SolidCore.Refinement.Solar.AssembleCreateSeg SolidCore.Refinement.Solar.AssembleCall
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- **CALL with value in SolarTV**, for any flag and return data the oracle answers. -/
theorem call_effectO {o : Oracle} {call : Call} {s : State} {M : ByteArray}
    {gas addr value inOff inSize outOff outSize : Word} {ok : Bool} {out : ByteArray}
    (hm : MemRel s.memory M)
    (hb1 : inSize = 0 ∨ (inOff.toNat + inSize.toNat + 31) / 32 < 2 ^ 251)
    (hb2 : outSize = 0 ∨ (outOff.toNat + outSize.toNat + 31) / 32 < 2 ^ 251)
    (hflag : callFlag o (callWorld s gas addr value inOff inSize outOff outSize) = if ok then 1 else 0)
    (hrd : RdRel o (callWorld s gas addr value inOff inSize outOff outSize) out) :
    ∃ s', Effect.apply o call (.call .call) [gas, addr, value, inOff, inSize, outOff, outSize] s =
        some (some (if ok then 1 else 0), s') ∧
      s'.storage = o.storageAfter (callWorld s gas addr value inOff inSize outOff outSize) ∧
      s'.world = callWorld s gas addr value inOff inSize outOff outSize ∧
      MemRel s'.memory (memoryWrite (memoryExtend M
          (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
        outOff.toNat (out.extract 0 (min outSize.toNat out.size))) := by
  have he := memRel_expand2W hm hb1 hb2
  refine ⟨called o .call s ((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat) outOff outSize (callWorld s gas addr value inOff inSize outOff outSize),
    ?_, rfl, rfl, ?_⟩
  · simp only [Effect.apply, CallKind.shape, hflag]
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
      have := Nat.min_le_left outSize.toNat out.size
      omega
    · simp [ByteArray.size_extract]
    · rw [byteAt_extract, Nat.zero_add, if_pos (by omega)]
      exact (hrd.2 i (by omega)).symm

/-- The table with one more message: its flag, return data and the storage after it. -/
def pushCall (T : RunTable) (ok : Bool) (out : ByteArray) (sto : Word → Word) : RunTable :=
  { T with
    oks := T.oks ++ [ok]
    outs := T.outs ++ [out]
    stores := T.stores ++ [sto]
    transients := T.transients ++ [fun _ => 0] }

theorem le_pushCall (T : RunTable) (ok : Bool) (out : ByteArray) (sto : Word → Word) :
    T.Le (pushCall T ok out sto) :=
  ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_append _ _, List.prefix_append _ _,
    List.prefix_refl _⟩

/-- **What every extension of the table answers at the world with the call**: the flag, the return
data, the storage and transient storage of the call's entry. -/
theorem table_call {base : Oracle} {T T'' : RunTable} {w : List Event} {ok : Bool} {out : ByteArray}
    {sto : Word → Word} (hsent : sent w = T.oks.length + 1) (houts : T.outs.length = T.oks.length)
    (hst : T.stores.length = T.oks.length) (htr : T.transients.length = T.oks.length)
    (hle : (pushCall T ok out sto).Le T'') :
    (tableOracle base T'').result w = (if ok then 1 else 0) ∧ T''.out w = out ∧
      (tableOracle base T'').storageAfter w = sto ∧
      (tableOracle base T'').transientAfter w = fun _ => 0 := by
  have h1 : T''.oks.getD T.oks.length false = ok := by
    rw [AssembleRun.getD_of_prefix hle.1 (by simp [pushCall])]
    simp [pushCall]
  have h2 : T''.outs.getD T.oks.length .empty = out := by
    rw [AssembleRun.getD_of_prefix hle.2.1 (by simp [pushCall, houts])]
    simp [pushCall, houts]
  have h3 : ∀ d, T''.stores.getD T.oks.length d = sto := by
    intro d
    rw [AssembleRun.getD_of_prefix hle.2.2.1 (by simp [pushCall, hst])]
    simp [pushCall, hst]
  have h4 : ∀ d, T''.transients.getD T.oks.length d = fun _ => 0 := by
    intro d
    rw [AssembleRun.getD_of_prefix hle.2.2.2.1 (by simp [pushCall, htr])]
    simp [pushCall, htr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tableOracle, hsent, Nat.add_sub_cancel, h1, ne_eq, Nat.add_one_ne_zero,
      not_false_eq_true, true_and]
    all_goals (cases ok <;> simp)
  · simp only [RunTable.out, hsent, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, h2]
  · simp only [tableOracle, hsent, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, h3]
  · simp only [tableOracle, hsent, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, h4]

/-- The price paid for the access, the value, a new account and the gas passed on covers the gas the
callee gets back, with its stipend: the frame ends the call with at most its gas less the growth of
memory. -/
theorem gas_after_le {g : Nat} {st : State.TransactionState} {ss : Substate} {msize : Nat}
    {asked dst v i isz o osz : U256} (hv : v ≠ 0) (hp : priceV st ss msize dst v i isz o osz ≤ g)
    {c : Nat} (hc : c ≤ (mcgV g st ss msize asked dst v i isz o osz).subCall) :
    g - ((mcgV g st ss msize asked dst v i isz o osz).cost +
      (extendMemory msize [(i, isz), (o, osz)]).cost) + c ≤
      g - (extendMemory msize [(i, isz), (o, osz)]).cost := by
  have hs := stipend_lt_callValueCost (fork := .fusaka) hv
  have hm : ∀ x, maxMessageCallGas x ≤ x := fun x => by unfold maxMessageCallGas; omega
  unfold priceV at hp
  unfold mcgV messageCallGas at hc ⊢
  simp only [hv, ite_false] at hc ⊢
  simp only [CALL_STIPEND] at hs hc
  split_ifs at hc ⊢ with hif
  · have := hm (g - (extendMemory msize [(i, isz), (o, osz)]).cost -
      (callBaseCost .fusaka (decide (toAddressMasked dst ∉ ss.accessedAddresses)) +
        callNewAccountCost .fusaka st (toAddressMasked dst) v + callValueCost .fusaka v))
    have := Nat.min_le_right asked.toNat (maxMessageCallGas (g - (extendMemory msize
      [(i, isz), (o, osz)]).cost - (callBaseCost .fusaka (decide (toAddressMasked dst ∉
        ss.accessedAddresses)) + callNewAccountCost .fusaka st (toAddressMasked dst) v +
        callValueCost .fusaka v)))
    omega
  · exfalso
    apply hif
    exact ⟨by decide, by omega⟩

/-- **Named hypothesis on the frame that ends a call's message**: the caller's account still exists
after it, a call that succeeds adds no log, and its output has fewer than `2 ^ 256` bytes. -/
def CallOk (msg : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  (child.state.getAccountOptional msg.currentTarget).isSome = true ∧
    (child.error.isNone = true → child.substate.logs.toList = []) ∧ child.output.size < 2 ^ 256

/-- A call event writes no log. -/
theorem logsRel_call {a : Address} {ss0 ss : Substate} {w : List Event} (k : SolarTV.Machine.CallKind)
    (ops : List Word) (c : List Memory.Byte) (sto tr : Word → Word) (h : LogsRel a ss0 ss w) :
    LogsRel a ss0 ss (w ++ [.call k ops c sto tr]) := by
  obtain ⟨L, h1, h2⟩ := h
  refine ⟨L, h1, ?_⟩
  rw [List.filter_append]
  simpa [isLogE] using h2

/-- **CALL with value as a cut of a run that succeeds.** -/
theorem callValue_cut {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {asked dst v i isz o osz : U256} {Tr : List U256} {s : State} {evm : Evm .fusaka Nat}
    (base : Oracle) (T : RunTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 300)
    (hat : At code msg pc (asked :: dst :: v :: i :: isz :: o :: osz :: Tr) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hv : v ≠ 0)
    (hstatic : msg.isStatic = false) {calleeCode : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked dst)).codeHash = .ok calleeCode)
    (hdel : delegatedAddress calleeCode = none) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hq : ∀ caller m child, P caller m child →
      caller.state = (st.recordAccountRead (toAddressMasked dst)).recordAccountRead msg.currentTarget →
      m.gas = (mcgV g st ss M.size asked dst v i isz o osz).subCall →
      m.caller = msg.currentTarget → m.currentTarget = toAddressMasked dst →
      m.data = memoryReadBytes (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
        i.toNat isz.toNat → m.value = v → CallOk msg child)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none)
    (hoks : T.oks.length = sent s.world) (houts : T.outs.length = sent s.world)
    (hsts : T.stores.length = sent s.world) (htrs : T.transients.length = sent s.world) :
    ∃ (ok : Bool) (out : ByteArray) (s' : State) (st' : State.TransactionState) (ss' : Substate)
      (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      (∀ T'', (pushCall T ok out (storeOf st' msg.currentTarget)).Le T'' →
        Effect.apply (tableOracle base T'') call (.call .call) [asked, dst, v, i, isz, o, osz] s =
            some (some (if ok then 1 else 0), s') ∧ RdRel (tableOracle base T'') s'.world out) ∧
      s'.world = callWorld s asked dst v i isz o osz ∧
      MemRel s'.memory M' ∧ Rel msg ss0 st' ss' s' ∧ MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) ((if ok then 1 else 0) :: Tr) M' g' st' ss' out m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hp, hcase⟩ := callValue_back hat hlt hbyte hv hstatic hcode hdel hdepth meets within hrun hok
  have hp' : (callBaseCost .fusaka (decide (toAddressMasked dst ∉ ss.accessedAddresses)) +
      callNewAccountCost .fusaka st (toAddressMasked dst) v + callValueCost .fusaka v) +
      (extendMemory M.size [(i, isz), (o, osz)]).cost ≤ g := hp
  obtain ⟨hb1, hb2, hbud, hfit⟩ := AssembleCallCut.budget_grow2 hmod hb hG hp'
  have hbud0 : MemBudget G (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
      (g - (extendMemory M.size [(i, isz), (o, osz)]).cost) := by
    have hc := extendMemory_cost M.size [(i, isz), (o, osz)]
    rw [ceil32_of_mod hmod] at hc
    have hmono := memoryGasCost_mono
      (Nat.le_add_right M.size (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
    unfold MemBudget at hb ⊢
    rw [size_memoryExtend]
    omega
  -- The world with the call, and what every extension of a table with it answers there.
  have hsent : sent (callWorld s asked dst v i isz o osz) = T.oks.length + 1 := by
    simp [callWorld, hoks]
  have hsame : ∀ (ok : Bool) (out : ByteArray) (sto : Word → Word) T'',
      (pushCall T ok out sto).Le T'' →
      Effect.apply (tableOracle base T'') call (.call .call) [asked, dst, v, i, isz, o, osz] s =
        Effect.apply (tableOracle base (pushCall T ok out sto)) call (.call .call)
          [asked, dst, v, i, isz, o, osz] s := by
    intro ok out sto T'' hle
    obtain ⟨r1, o1, s1, t1⟩ := table_call (base := base) hsent (by omega) (by omega) (by omega) hle
    obtain ⟨r2, o2, s2, t2⟩ := table_call (base := base) hsent (by omega) (by omega) (by omega)
      (RunTable.Le.refl (pushCall T ok out sto))
    have hrds : returndataSize (tableOracle base T'') (callWorld s asked dst v i isz o osz) =
        returndataSize (tableOracle base (pushCall T ok out sto)) (callWorld s asked dst v i isz o osz) := by
      rw [returndataSize_table, returndataSize_table, o1, o2]
    have hrdb : returndataByte (tableOracle base T'') (callWorld s asked dst v i isz o osz) =
        returndataByte (tableOracle base (pushCall T ok out sto)) (callWorld s asked dst v i isz o osz) := by
      funext j
      simp only [returndataByte, tableOracle, o1, o2]
      simp
    have hflag : callFlag (tableOracle base T'') (callWorld s asked dst v i isz o osz) =
        callFlag (tableOracle base (pushCall T ok out sto)) (callWorld s asked dst v i isz o osz) := by
      simp only [callFlag, r1, r2]
    simp only [callWorld] at hrds hrdb hflag s1 s2 t1 t2
    simp only [Effect.apply, CallKind.shape, called, hflag, hrds, hrdb, s1, s2, t1, t2]
  -- SolarTV's CALL under the table with the call's answers.
  have heff : ∀ (ok : Bool) (out : ByteArray) (sto : Word → Word), out.size < 2 ^ 256 →
      ∃ s', (∀ T'', (pushCall T ok out sto).Le T'' →
        Effect.apply (tableOracle base T'') call (.call .call) [asked, dst, v, i, isz, o, osz] s =
            some (some (if ok then 1 else 0), s') ∧ RdRel (tableOracle base T'') s'.world out) ∧
        s'.storage = sto ∧ s'.world = callWorld s asked dst v i isz o osz ∧
        MemRel s'.memory (memoryWrite (memoryExtend M
          (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
          o.toNat (out.extract 0 (min osz.toNat out.size))) := by
    intro ok out sto hsz
    obtain ⟨r2, o2, s2, -⟩ := table_call (base := base) (ok := ok) (out := out) (sto := sto) hsent
      (by omega) (by omega) (by omega) (RunTable.Le.refl _)
    have hrd2 : RdRel (tableOracle base (pushCall T ok out sto)) (callWorld s asked dst v i isz o osz) out := by
      have := rdRel_table base (pushCall T ok out sto) (callWorld s asked dst v i isz o osz) (by rw [o2]; exact hsz)
      rwa [o2] at this
    obtain ⟨s', happ, hsto, hw, hmem⟩ := call_effectO (o := tableOracle base (pushCall T ok out sto))
      (call := call) (ok := ok) hm hb1 hb2 (by simp only [callFlag, r2]; cases ok <;> simp) hrd2
    refine ⟨s', fun T'' hle => ⟨by rw [hsame ok out sto T'' hle, happ], ?_⟩, by rw [hsto, s2], hw, hmem⟩
    obtain ⟨-, o1, -, -⟩ := table_call (base := base) hsent (by omega) (by omega) (by omega) hle
    have := rdRel_table base T'' (callWorld s asked dst v i isz o osz) (by rw [o1]; exact hsz)
    rw [o1] at this
    rw [hw]
    exact this
  rcases hcase with ⟨-, m, within', hat', hrun'⟩ |
    ⟨-, caller, mm, child, after, within', hP, hcg, hcs, hcsub, hmg, hmc, hmt, -, hmd, hmv, -,
      hat', hrun'⟩
  · -- The frame lacks the value: no message.
    obtain ⟨s', hall, hsto, hw, hmem⟩ := heff false .empty
      (storeOf ((st.recordAccountRead (toAddressMasked dst)).recordAccountRead msg.currentTarget)
        msg.currentTarget) (by simp)
    have hw0 : memoryWrite (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
        o.toNat (ByteArray.empty.extract 0 (min osz.toNat ByteArray.empty.size)) =
        memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy := by
      simp [memoryWrite, ByteArray.size_extract]
    rw [hw0] at hmem
    refine ⟨false, .empty, s', _, { ss with
        accessedAddresses := ss.accessedAddresses.insert (toAddressMasked dst) }, _,
      g - ((mcgV g st ss M.size asked dst v i isz o osz).cost +
        (extendMemory M.size [(i, isz), (o, osz)]).cost) +
        (mcgV g st ss M.size asked dst v i isz o osz).subCall, m, within',
      hall, hw, hmem, ⟨fun k => by rw [hsto]; rfl, by simpa using R.account, ?_⟩,
      MemBudget.spend hbud0 (gas_after_le (asked := asked) hv hp le_rfl),
      le_trans (gas_after_le (asked := asked) hv hp le_rfl) (Nat.sub_le _ _),
      by simpa using hat', hrun'⟩
    rw [hw]
    exact logsRel_call _ _ _ _ _ R.logs
  · -- The callee ran.
    obtain ⟨hacc, hlogs, hout⟩ := hq caller mm child hP hcs hmg hmc hmt hmd hmv
    obtain ⟨s', hall, hsto, hw, hmem⟩ := heff child.error.isNone child.output
      (storeOf (incorporateChild .fusaka caller child).state msg.currentTarget) hout
    have hg2 := gas_after_le (asked := asked) hv hp (c := child.gas) (by rw [← hmg]; exact hcg)
    refine ⟨child.error.isNone, child.output, s', _, _, _,
      g - ((mcgV g st ss M.size asked dst v i isz o osz).cost +
        (extendMemory M.size [(i, isz), (o, osz)]).cost) + child.gas, after, within',
      hall, hw, hmem, ⟨fun k => by rw [hsto]; rfl, ?_, ?_⟩, ?_, by omega, hat', hrun'⟩
    · rw [incorporateChild_state]
      exact hacc
    · have hl : (incorporateChild .fusaka caller child).substate.logs.toList = ss.logs.toList := by
        unfold incorporateChild
        split
        · rename_i hn
          simp [Array.toList_append, hcsub, hlogs (by simpa using hn)]
        · simp [hcsub]
      obtain ⟨L, h1, h2⟩ := R.logs
      refine ⟨L, by rw [hl, h1], ?_⟩
      rw [hw, callWorld, List.filter_append]
      simpa [isLogE] using h2
    · unfold MemBudget
      rw [size_memoryWrite_of_fit, size_memoryExtend]
      · unfold MemBudget at hbud0
        rw [size_memoryExtend] at hbud0
        omega
      · intro h
        simp only [ByteArray.size_extract] at h ⊢
        have hz : osz ≠ 0 := by
          intro hz
          simp [hz] at h
        have := hfit hz
        rw [size_memoryExtend]
        have := Nat.min_le_left osz.toNat child.output.size
        omega

/-- info: 'SolidCore.Refinement.Solar.AssembleCallValueSeg.callValue_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callValue_cut

end SolidCore.Refinement.Solar.AssembleCallValueSeg

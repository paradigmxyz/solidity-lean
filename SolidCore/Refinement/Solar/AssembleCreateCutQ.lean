import SolidCore.Refinement.Solar.AssembleCreateSegOracle

/-!
# CALL and CREATE2 cuts from what the run gives the callee's frame

`AssembleCallValueZeroSeg.call0_cut`, `AssembleCallValueSeg.callValue_cut` and `AssembleCreateSeg.create2_cut`
ask of every frame the runner of messages may return (`P caller m child`, with a few fields of the
message) that it keep the frame's account, add no log when it succeeds and have an output below
`2 ^ 256` bytes, over every caller state: too much, since some state gives the callee code that logs.
The versions here ask it only of the frames the runner returns from the caller state the instruction
makes out of the frame's own state, for the code the callee runs there (`Call0Q`, `CallVQ`,
`Create2Q`), which a run that calls and creates only contracts that do not log meets.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateCutQ

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCreateSeg SolidCore.Refinement.Solar.AssembleCall
open SolidCore.Refinement.Solar.AssembleCallValue SolidCore.Refinement.Solar.AssembleCallValueEffect
open SolidCore.Refinement.Solar.AssembleCallValueZero SolidCore.Refinement.Solar.AssembleCallValueSeg
open SolidCore.Refinement.Solar.AssembleCallValueZeroSeg SolidCore.Refinement.Solar.AssembleCreate
open SolidCore.Refinement.Solar.AssembleCreateBack
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-- **What a run gives a CALL with no value**: every frame the runner returns for its message (to the
callee, with its data), from the caller state the CALL makes out of the frame's state `st` and for
the code the callee runs, keeps the frame's account, adds no log when it succeeds and has an output
below `2 ^ 256` bytes (`CallOk`). -/
def Call0Q (msg : Message .fusaka) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (st : State.TransactionState) (M : ByteArray) (addr inOff inSize outOff outSize : U256) : Prop :=
  ∀ caller m child, P caller m child → m.currentTarget = toAddressMasked addr → m.value = 0 →
    m.isStatic = false →
    m.data = memoryReadBytes (memoryExtend M
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy) inOff.toNat inSize.toNat →
    (∃ calleeCode route, st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode ∧
      caller.state = (routeState (st.recordAccountRead (toAddressMasked addr)) route).recordAccountRead
        msg.currentTarget ∧ m.code = routeCode calleeCode route) →
    CallOk msg child

/-- **What a run gives a CALL with value** to a callee whose code is `calleeCode`, as `Call0Q`. -/
def CallVQ (msg : Message .fusaka) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (g : Nat) (st : State.TransactionState) (ss : Substate) (M : ByteArray)
    (asked dst v i isz o osz : U256) (calleeCode : ByteArray) : Prop :=
  ∀ caller m child, P caller m child →
    caller.state = (st.recordAccountRead (toAddressMasked dst)).recordAccountRead msg.currentTarget →
    m.gas = (mcgV g st ss M.size asked dst v i isz o osz).subCall →
    m.caller = msg.currentTarget → m.currentTarget = toAddressMasked dst → m.code = calleeCode →
    m.data = memoryReadBytes (memoryExtend M (extendMemory M.size [(i, isz), (o, osz)]).expandBy)
      i.toNat isz.toNat → m.value = v → CallOk msg child

/-- **What a run gives a CREATE2**: every frame the runner returns for the creation's message (its
init code, at its address), from the caller state the creation makes out of `st`, keeps the frame's
account, adds no log when it succeeds and has revert data below `2 ^ 256` bytes (`CreateOk`). -/
def Create2Q (msg : Message .fusaka) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (g : Nat) (st : State.TransactionState) (M : ByteArray) (value start size salt : U256) : Prop :=
  ∀ caller m child, P caller m child →
    ((st.recordAccountRead msg.currentTarget).recordAccountRead (create2Address msg.currentTarget salt
      (memoryReadBytes (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat
        size.toNat))).incrementNonce .fusaka msg.currentTarget = .ok caller.state →
    m.caller = msg.currentTarget →
    m.currentTarget = create2Address msg.currentTarget salt (memoryReadBytes (memoryExtend M
      (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat) →
    m.code = memoryReadBytes (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
      start.toNat size.toNat → m.value = value →
    m.gas = createMessageGas .fusaka (g - cost2 M.size start size) → CreateOk msg child

/-- **CREATE2 as a cut of a run that succeeds**: the creation had the gas for its price, and the run
goes on from the frame after it, pushing the word `r` (the EIP-1014 address on success, 0 otherwise),
with return data `out` and the storage of the frame's account after it. Under the oracle of every
extension of the table with these answers, SolarTV's CREATE2 pushes `r`, leaves `out` and that storage,
and every relation of a block entry holds again, at no more gas than the frame had. -/
theorem create2_cutQ {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {value start size salt : U256} {Tr : List U256} {s : State} {evm : Evm .fusaka Nat}
    (o : Oracle) (A : CreateTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 256)
    (hat : At code msg pc (value :: start :: size :: salt :: Tr) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf5) (hstatic : msg.isStatic = false)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hq : Create2Q msg P g st M value start size salt)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none)
    (hA : A.addrs.length = creates s.world) (hAo : A.outs.length = creates s.world)
    (hAs : A.stores.length = creates s.world) :
    ∃ (r : Word) (out : ByteArray) (st' : State.TransactionState) (ss' : Substate) (M' : ByteArray)
      (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      (∀ A'', (A.push r out (storeOf st' msg.currentTarget)).Le A'' →
        Effect.apply (createOracle o A'') call .create2 [value, start, size, salt] s =
            some (some r, postCreate o s (storeOf st' msg.currentTarget) value start size salt) ∧
          RdRel (createOracle o A'') (createWorld s value start size salt) out) ∧
      MemRel (postCreate o s (storeOf st' msg.currentTarget) value start size salt).memory M' ∧
      Rel msg ss0 st' ss' (postCreate o s (storeOf st' msg.currentTarget) value start size salt) ∧
      MemBudget G M' g' ∧ g' ≤ g ∧
      At code msg (pc + 1) (r :: Tr) M' g' st' ss' out m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  obtain ⟨hg, -, hcase⟩ := create2_back hat hmod hlt hbyte hstatic meets within hrun hok
  have hg' : createBaseCost .fusaka + OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
      initCodeCost size.toNat + (extendMemory M.size [(start, size)]).cost ≤ g := hg
  have hbnd : size = 0 ∨ (start.toNat + size.toNat + 31) / 32 < 2 ^ 251 := by
    by_cases hz : size = 0
    · exact .inl hz
    · have := AssembleCodeCopy.size_le_of_budget hmod hz hb hG hg'
      exact .inr (by omega)
  have hm1 := memRel_expandW hm hbnd
  have hb1 : MemBudget G (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
      (g - cost2 M.size start size) :=
    MemBudget.grow hmod hb hg' (size_memoryExtend _ _)
  rcases hcase with ⟨-, m, within', hat', hrun'⟩ |
    ⟨-, -, -, -, st', m, within', hinc, hat', hrun'⟩ |
    ⟨-, -, -, -, caller, mm, child, after, within', hP, hcg, hinc2, hcsub, hmg, hmc, hmt, hmcode, hmv, -,
      hat', hrun'⟩
  · -- No message: 0 pushed, no return data.
    refine ⟨0, .empty, _, ss, memoryExtend M (extendMemory M.size [(start, size)]).expandBy,
      g - cost2 M.size start size, m, within', fun A'' hle =>
      create2_apply hA hAo hAs hle (by simp) (by simp), hm1, ⟨fun k => rfl, ?_, ?_⟩, hb1,
      by omega, hat', hrun'⟩
    · simpa using R.account
    · exact logsRel_create _ _ _ _ R.logs
  · -- A collision: 0 pushed, the creator's nonce grows.
    refine ⟨0, .empty, st', { ss with
        accessedAddresses := ss.accessedAddresses.insert (create2Address msg.currentTarget salt
          (memoryReadBytes (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
            start.toNat size.toNat)) },
      memoryExtend M (extendMemory M.size [(start, size)]).expandBy,
      g - cost2 M.size start size - createMessageGas .fusaka (g - cost2 M.size start size), m,
      within', fun A'' hle =>
      create2_apply hA hAo hAs hle (by simp) (by simp), hm1,
      ⟨fun k => rfl, account_incrementNonce hinc, logsRel_create _ _ _ _ R.logs⟩,
      MemBudget.spend hb1 (by omega), by omega, hat', hrun'⟩
  · -- The init code ran as a callee.
    obtain ⟨hacc, hlogs, hfit⟩ := hq caller mm child hP hinc2 hmc hmt hmcode hmv hmg
    have hle1 := createMessageGas_le (g - cost2 M.size start size)
    have hgas : g - cost2 M.size start size - createMessageGas .fusaka (g - cost2 M.size start size) +
        child.gas ≤ g - cost2 M.size start size := by omega
    refine ⟨if child.error.isNone then (create2Address msg.currentTarget salt (memoryReadBytes
        (memoryExtend M (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat)).toU256
        else 0, if child.error.isNone then .empty else child.output, _, _,
      memoryExtend M (extendMemory M.size [(start, size)]).expandBy,
      g - cost2 M.size start size - createMessageGas .fusaka (g - cost2 M.size start size) +
        child.gas, after, within',
      fun A'' hle => create2_apply hA hAo hAs hle ?_ ?_, hm1, ⟨fun k => rfl, ?_, ?_⟩,
      MemBudget.spend hb1 hgas, by omega, hat', hrun'⟩
    · split
      · exact toU256_lt _
      · simp
    · split
      · simp
      · exact hfit
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
      simp only [postCreate, createWorld, List.filter_append]
      simpa [isLogE] using h2

/-- **CALL with value as a cut of a run that succeeds**, from what the run gives the frame its
message ends with (`CallVQ`, at the caller state and callee code the CALL makes). -/
theorem callValue_cutQ {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
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
    (hq : CallVQ msg P g st ss M asked dst v i isz o osz calleeCode)
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
    ⟨-, caller, mm, child, after, within', hP, hcg, hcs, hcsub, hmg, hmc, hmt, hmcode, hmd, hmv, -,
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
    obtain ⟨hacc, hlogs, hout⟩ := hq caller mm child hP hcs hmg hmc hmt hmcode hmd hmv
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

/-- **CALL with no value as a cut of a run that succeeds**, from what the run gives the frame its
message ends with (`Call0Q`, at the caller state and code the CALL makes). -/
theorem call0_cutQ {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
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
    (hq : Call0Q msg P st M addr inOff inSize outOff outSize)
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
  obtain ⟨calleeCode, route, hgc, -, hgp, caller, mm, child, after, within', g', hP, -, hcst, hcsub, hms,
    hmv, hmc, hmt, -, hmd, -, -, -, hg', hat', hrun'⟩ :=
    call0_back hat hlt hbyte hstatic hdepth meets within hrun hok
  obtain ⟨hb1, hb2, hbud, hfit⟩ := AssembleCallCut.budget_grow2 hmod hb hG hgp
  obtain ⟨hacc, hlogs, hout⟩ := hq caller mm child hP hmt hmv hms hmd ⟨calleeCode, route, hgc, hcst, hmc⟩
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


/-- info: 'SolidCore.Refinement.Solar.AssembleCreateCutQ.call0_cutQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms call0_cutQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateCutQ.callValue_cutQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms callValue_cutQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateCutQ.create2_cutQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_cutQ

end SolidCore.Refinement.Solar.AssembleCreateCutQ

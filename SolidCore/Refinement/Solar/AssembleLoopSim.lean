import SolidCore.Refinement.Solar.AssembleLoop

/-!
# EVM IR to bytecode, for code with loops: the simulation of a block

`Assemble.exec_sim` over the steps from frames monotone in gas (`HoareG`, `SpecG`), for the
checker of code with loops: from a block's instructions, EthLib's interpreter runs as SolarTV
does, to a halt or to the next block, reached with the gas for the reserve `R` (the items of the
blocks the run enters after it) and at most its highest entry stack. A jump goes to a labelled
block and a fall to the next one, which the run's measure of gas needs (`AssembleLoopRun`).
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Rules over steps monotone in gas -/

section G

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- A frame at or past the end of its code stops as STOP does, at no price. -/
theorem stop_of_size_leG (hle : code.size ≤ pc) :
    SpecG fork (At code message pc stack memory gas state substate returnData)
      (Halted false .empty gas state substate) := by
  apply Triple.of_step
  rintro evm ⟨hcode, -, -, hpc, -, -, hg, hrun, herr, hout, hs, hss, -⟩
  refine ⟨_, ⟨.next hrun (step_of_size_le (by rw [hcode, hpc]; exact hle)), ?_⟩, rfl, rfl, herr,
    hout, hg, hs, hss⟩
  rintro k low rfl
  have hl : low.code.size ≤ low.pc := by
    have h1 : (addGas k low).code = low.code := rfl
    have h2 : (addGas k low).pc = low.pc := rfl
    rw [← h1, ← h2, hcode, hpc]; exact hle
  rw [step_of_size_le hl, step_of_size_le (show (addGas k low).code.size ≤ (addGas k low).pc from hl)]
  exact .inr ⟨_, rfl, rfl⟩

/-- `Logic.sstore_of_account` over steps monotone in gas. -/
theorem sstore_of_accountG (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {key new : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreCost fork (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true) :
    ∃ state' : State.TransactionState,
      state'.getStorage message.currentTarget (U256.toBeBytes key) = new ∧
      (∀ other slot, other ≠ message.currentTarget ∨ slot ≠ U256.toBeBytes key →
        state'.getStorage other slot = state.getStorage other slot) ∧
      state'.getStorageOriginal = state.getStorageOriginal ∧
      (∀ other, state'.getAccountOptional other = state.getAccountOptional other) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) ∧
      state'.parent = state.parent ∧
      HoareG fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
        (At code message (pc + 1) rest memory
          (gas - sstoreCost fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
          state'
          { substate with
            accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
              ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
                (U256.toBeBytes key))
            refundCounter := substate.refundCounter + sstoreRefund fork
              (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
              (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) := by
  -- Recording the read keeps the account, so the write succeeds.
  obtain ⟨state', hset⟩ := State.TransactionState.exists_setStorage (U256.toBeBytes key) new
    (tx := state.recordStorageRead message.currentTarget (U256.toBeBytes key))
    (by rw [(State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) default).1]; exact hacc)
  refine ⟨state', State.TransactionState.getStorage_setStorage_self hset, fun other slot hne => ?_,
    ?_, fun other => ?_, fun codeHash => ?_,
    by rw [State.TransactionState.parent_setStorage hset]; rfl,
    sstoreG hfork hglam hlt hbyte hstatic hcold hstipend hgas hset⟩
  · rw [State.TransactionState.getStorage_setStorage_of_ne hset hne]
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.1
  · rw [State.TransactionState.getStorageOriginal_setStorage hset]
    funext other slot
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.2.1
  · rw [State.TransactionState.getAccountOptional_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ other _
      (U256.toBeBytes key) default).1
  · rw [State.TransactionState.getCode_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) codeHash).2.2.2.1

/-- RETURN shows §X§ when §X§ succeeds with the bytes it reads, the logs are §ss§'s and the
storage is §X§'s. -/
theorem return_postSG {X : Observable} {ss : Substate} {code : ByteArray} {message : Message fork}
    {pc : Nat} {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = true)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output)
    (hlogs : substate.logs = ss.logs)
    (hstore : ∀ slot, (state.getStorage (Target.address selfAddress)
      (Target.storageKey slot)).toNat = X.storage slot) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (PostS X ss) :=
  SpecG.consequence (Logic.returnG hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, hst, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, by rw [hss, hlogs],
        fun _ slot => by rw [hst]; exact hstore slot⟩)

/-- REVERT shows §X§ when §X§ fails with the bytes it reads and the logs are §ss§'s. -/
theorem revert_postSG {X : Observable} {ss : Substate} {code : ByteArray} {message : Message fork}
    {pc : Nat} {start size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
    (hfork : .byzantium ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0xfd)
    (hgas : (extendMemory memory.size [(start, size)]).cost ≤ gas) (hs : X.success = false)
    (hout : (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).toList.map (·.toNat) = X.output)
    (hlogs : substate.logs = ss.logs) :
    SpecG fork (At code message pc (start :: size :: rest) memory gas state substate returnData)
      (PostS X ss) :=
  SpecG.consequence (Logic.revertG hfork hlt hbyte hgas) (fun _ h => h)
    (fun _ ⟨_, herr, hout', _, _, hss⟩ =>
      ⟨by rw [herr]; simp [errorOf, hs], by rw [hout']; exact hout, by rw [hss, hlogs],
        fun h => by rw [hs] at h; cases h⟩)

end G

/-! ## MLOAD -/

/-- A fold of bytes into a word, as SolarTV's load does it, is EthLib's number of the bytes. -/
theorem foldl_bytes : ∀ (l : List UInt8) (a : Nat),
    l.foldl (fun (acc : BitVec 256) (b : UInt8) => (acc <<< 8) ||| b.toBitVec.setWidth 256)
        (BitVec.ofNat 256 a) =
      BitVec.ofNat 256 (l.foldl (fun acc b => acc * 256 + b.toNat) a)
  | [], _ => rfl
  | u :: l, a => by
    simp only [List.foldl_cons]
    have hu : u.toBitVec.setWidth 256 = BitVec.ofNat 256 u.toNat := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
    rw [hu, shl_or_ofNat _ _ u.toNat_lt, foldl_bytes l]

open SolarTV.Machine in
/-- MLOAD in SolarTV is EthLib's. -/
theorem load_eq {m : Mem} {M : ByteArray} {o : Word} (hm : MemRel m M) :
    loadWord (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat 32)
      0 32 = m.load o.toNat := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hext := size_memoryExtend_extendMemory' (memory := M) (start := o) (length := 32) hmod
    (by decide)
  have hfit : o.toNat + 32 ≤
      (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy).size := by
    rw [hext, show (32 : Word).toNat = 32 from rfl]
    exact Nat.le_trans (le_ceil32 _) (Nat.le_max_right _ _)
  have h1 : (List.range 32).map (fun i => byteAt (memoryReadBytes
      (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat 32) (0 + i)) =
      (List.range 32).map (fun i => byteAt M (o.toNat + i)) := by
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [byteAt_memoryReadBytes hfit, ite_eq_left (by omega), byteAt_memoryExtend, Nat.zero_add]
  have h2 : (List.range 32).map (fun i => m.bytes (o.toNat + i)) =
      ((List.range 32).map (fun i => byteAt M (o.toNat + i))).map UInt8.toBitVec := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact (hm.2 _).symm
  unfold loadWord bufferRead bytesToNat Mem.load Mem.read
  rw [h1, h2]
  conv_rhs => rw [List.foldl_map]
  rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_bytes]


open SolarTV.EVM.Program in
theorem exec_load {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {b : Nat}
    {rest : List Assemble.Instr} {x : Word} {S : List Word} {s : SolarTV.Machine.State}
    (h : S.length < 1024) :
    exec o call b (.op .load :: rest) (x :: S) s =
      exec o call b rest (s.memory.load x.toNat :: S) { s with memory := s.memory.expand x.toNat 32 } := by
  have h1 : ¬ 1024 < S.length + 1 := by omega
  simp [exec, stepOp, h1]

/-! ## The simulation of a block -/

set_option hygiene false in
/-- The bound of the stack in lockstep with the height of the check. -/
local macro "hu_tac" : tactic => `(tactic| first | omega | (simp at hu ⊢; omega) | (simp; omega))

/-- What a block's instructions from `pc` give: a halt EthLib's frame shows, or the next block,
reached by EthLib with its stack related at the block's types, at most its highest entry stack,
with gas for the reserve `R`, and by a jump to a labelled block or a fall into the next one. -/
def SimOutL (p : Program) (c : Cert) (mx : List Nat) (code : ByteArray) (call : SolarTV.Call)
    (msg : Message .fusaka) (ss0 : Substate) (st : State.TransactionState) (ss : Substate)
    (b R pc : Nat) (T : List Word) (M : ByteArray) (g : Nat) :
    (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State) →
      Prop
  | .inl (halt, s') =>
    SpecG .fusaka (At code msg pc T M g st ss .empty) (PostL call msg.currentTarget ss0 s' halt)
  | .inr (t, S', s') => (t ≤ p.blocks.length ∧
      (t < p.blocks.length → c.need t ≤ S'.length ∧ S'.length ≤ maxH mx t) ∧
      (t = b + 1 ∨ isTarget p c t = true)) ∧
      ∃ pc' T' M' g' st' ss', HoareG .fusaka (At code msg pc T M g st ss .empty)
        (At code msg pc' T' M' g' st' ss' .empty) ∧ SR c (c.entry t) S' T' ∧
        EntryL c code call (lowerFrom p c t (p.blocks.drop t)) R pc' s' M' g' ∧
        Rel msg ss0 st' ss' s'

theorem SimOutL.pre {p : Program} {c : Cert} {mx : List Nat} {code : ByteArray} {call : SolarTV.Call}
    {msg : Message .fusaka} {ss0 : Substate} {st st1 : State.TransactionState} {ss ss1 : Substate}
    {b R pc pc1 : Nat} {T T1 : List Word} {M M1 : ByteArray} {g g1 : Nat}
    {r : (SolarTV.Machine.Halt × SolarTV.Machine.State) ⊕ (Nat × List Word × SolarTV.Machine.State)}
    (h : HoareG .fusaka (At code msg pc T M g st ss .empty) (At code msg pc1 T1 M1 g1 st1 ss1 .empty))
    (h1 : SimOutL p c mx code call msg ss0 st1 ss1 b R pc1 T1 M1 g1 r) :
    SimOutL p c mx code call msg ss0 st ss b R pc T M g r := by
  match r, h1 with
  | .inl (_, _), hspec => exact SpecG.seq h hspec
  | .inr (_, _, _), ⟨hneed, pc', T', M', g', st', ss', hh, hR, hinv, hrel⟩ =>
    exact ⟨hneed, pc', T', M', g', st', ss', Triple.seq h hh, hR, hinv, hrel⟩

theorem blockStepL_stack {p : Program} {c : Cert} {mx : List Nat} {bb : Nat} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h k : Nat} {known : List Word} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    (hd : ∀ i, op ≠ .dup i) (hs : ∀ i, op ≠ .swap i) (hp : op ≠ .pop) :
    blockStepL p c mx bb ok h known ty k (.op (.stack op)) =
      match stackNeed op with
      | some (need, d) => decide (1 ≤ k) && decide (need ≤ h) && isData ty need &&
          ok (h + d).toNat [] (some false :: ty.drop need) (k - 1)
      | none => false := by
  cases op <;> first | rfl | exact absurd rfl (hne _) | exact absurd rfl (hd _) |
    exact absurd rfl (hs _) | exact absurd rfl hp


/-- `stack_sim` for `blockStepL`, with the heights of the check and the stack in lockstep. -/
theorem stack_simL {p : Program} {c : Cert} {mx : List Nat} {bb : Nat} {ok : Nat → List Word → List Ty → Nat → Bool}
    {h k : Nat} {known : List Word} {ty : List Ty} {op : SolarTV.EVM.Op} (hne : ∀ v, op ≠ .push v)
    {ctx : SolarTV.EVM.Context} {S T : List Word}
    (hok : blockStepL p c mx bb ok h known ty k (.op (.stack op)) = true) (hh : h ≤ S.length)
    (hk : known <+: S) (hR : SR c ty S T) :
    1 ≤ k ∧ ∃ byte, opByte op = some byte ∧ ∃ h' ty' S' T',
      SolarTV.EVM.step ctx op S = some S' ∧ SolarTV.EVM.step ctx op T = some T' ∧
      SR c ty' S' T' ∧ h' ≤ S'.length ∧ S'.length ≤ S.length + 1 ∧ S'.length + h = h' + S.length ∧
      ∃ known', known' <+: S' ∧ ok h' known' ty' (k - 1) = true := by
  have hL := hR.length
  by_cases hd : ∃ i, op = .dup i
  · obtain ⟨i, rfl⟩ := hd
    simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x80 + i.val, by simp [opByte, h16], h + 1, _, _, _, ?_, ?_, SR.dup hR hiS hiT, by simp; omega, by simp, by simp; omega, _,
      dupKnown_prefix hk hiS, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hs : ∃ i, op = .swap i
  · obtain ⟨i, rfl⟩ := hs
    simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, h16⟩, hi⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    simp only [List.length_cons] at hh hL
    have hiS : i.val < S.length := by omega
    have hiT : i.val < T.length := by omega
    refine ⟨hk1, 0x90 + i.val, by simp [opByte, h16], h, _, _, _, ?_, ?_, SR.swap hR hiS hiT, by simp; omega, by simp, by simp; omega, [],
      List.nil_prefix, hok⟩
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiS]
    · simp [SolarTV.EVM.step, List.getElem?_eq_getElem hiT]
  by_cases hp : op = .pop
  · subst hp
    simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk1, h1⟩, hok⟩ := hok
    rcases S with _ | ⟨a, S⟩
    · simp at hh; omega
    rcases T with _ | ⟨b, T⟩
    · simp at hL
    refine ⟨hk1, _, rfl, h - 1, _, _, _, rfl, rfl, (SR.uncons.1 hR).2, by simp at hh; omega,
      by simp only [List.length_cons]; omega, by simp at hh ⊢; omega, [], List.nil_prefix, hok⟩
  have hd' : ∀ i, op ≠ .dup i := fun i e => hd ⟨i, e⟩
  have hs' : ∀ i, op ≠ .swap i := fun i e => hs ⟨i, e⟩
  rw [blockStepL_stack hne hd' hs' hp] at hok
  split at hok
  · rename_i need d hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hk1, hneed⟩, hdata⟩, hok⟩ := hok
    obtain ⟨byte, hbyte⟩ := opByte_of_stackNeed hn
    have hS' : ∃ S', SolarTV.EVM.step ctx op S = some S' := by
      cases op <;> simp only [stackNeed, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hn
      all_goals try first
        | exact absurd rfl (hd' _)
        | exact absurd rfl (hs' _)
        | exact absurd rfl hp
      all_goals obtain ⟨rfl, -⟩ := hn
      all_goals rcases S with _ | ⟨a, _ | ⟨b, S⟩⟩ <;> simp_all [SolarTV.EVM.step] <;> omega
    obtain ⟨S', hstep⟩ := hS'
    obtain ⟨v, rfl, hstepT⟩ := step_data hn hd' hs' hp hstep (hR.data hdata) hL
    have hd1 : (need : Int) + d = 1 := by
      cases op <;> simp [stackNeed] at hn <;>
        first | omega | exact absurd rfl (hd' _) | exact absurd rfl (hs' _) | exact absurd rfl hp
    refine ⟨hk1, byte, hbyte, (h + d).toNat, _, _, _, hstep, hstepT,
      SR.cons (τ := some false) rfl (SR.drop need hR), ?_, ?_, ?_, [], List.nil_prefix, hok⟩
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
    · simp only [List.length_cons, List.length_drop]; omega
  · cases hok


open SolarTV.EVM.Program in
/-- EthLib runs the code of a block's instructions from the offset of the next one as SolarTV
runs them, over steps monotone in gas, with gas for the reserve `R` beyond the block. -/
theorem exec_simL {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray} (G : GlobL p c mx code)
    {o : SolarTV.Machine.Oracle} {call : SolarTV.Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress) (ho : c.env = true → OracleOk o)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (he : c.reads = true → EnvOk o)
    (b : Nat) (hb : b < p.blocks.length) (Rv : Nat) :
    ∀ (is : List Assemble.Instr) (h : Nat) (known : List Word) (ty : List Ty) (S T : List Word) (k : Nat)
      (s : SolarTV.Machine.State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate),
      blockOkL p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → known <+: S → SR c ty S T →
      InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) k Rv
        pc S s M g → Rel msg ss0 st ss s →
      SimOutL p c mx code call msg ss0 st ss b Rv pc T M g (exec o call b is S s)
  | [], h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, _, hR, I, R => by
    simp only [blockOkL, fallOkL, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have I2 := I.entry
    simp only [lowerInstrs, List.nil_append] at I2
    simp only [exec, SimOutL]
    exact ⟨⟨by omega, fun ht => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
      Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I2, R⟩
  | i :: rest, h, known, ty, S, T, k, s, pc, M, g, st, ss, hok, hh, hu, hk, hR, I, R => by
    have hL := hR.length
    have hctx : (⟨BitVec.ofNat 256 msg.data.size, o.env "returndatasize" s.world []⟩ :
        SolarTV.EVM.Context) = context o call s := by rw [hdata]; rfl
    cases hT : turnedElse c b i rest with
    | some e =>
      -- A turned branch: ISZERO; PUSH e; JUMPI, falling into the next block.
      obtain ⟨rfl, rfl⟩ := turnedElse_some hT
      simp only [blockOkL, hT, jumpOkL, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨hk3, h1⟩, hdat⟩, ⟨⟨⟨hen, hetgt⟩, hneed⟩, hety⟩, hcost⟩, ⟨hfall, hfty⟩, hcost'⟩ := hok
      simp only [lowerInstrs, hT, List.cons_append, List.nil_append] at I
      rcases S with _ | ⟨cond, S'⟩
      · simp at hh; omega
      rcases T with _ | ⟨cond', T'⟩
      · simp at hL
      obtain rfl := (SR.head hR hdat).symm
      have hR' := (SR.uncons.1 hR).2
      simp only [List.length_cons] at hL
      obtain ⟨n0, hd0, hs0⟩ := I.seg.head
      obtain ⟨n1, hd1, hs1⟩ := hs0.head
      obtain ⟨n2, hd2, hseg⟩ := hs1.head
      simp only [Item.expected] at hd0 hd1 hd2
      obtain ⟨hlt0, hcode0, rfl⟩ := op_item hd0
      obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
      have hS := I.stack; have hG := I.gas
      simp only [List.length_cons] at hS hh hu
      obtain ⟨g0, hg0, hisz⟩ := stack_ruleG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
        (op := .iszero) (stack := cond :: T') (next := EvmRules.Evm.iszero cond :: T')
        (r := o.env "returndatasize" s.world []) rfl hlt0 hcode0 rfl (by omega)
        (by simp only [List.length_cons]; omega)
      obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss)
        (gas := g0) (stack := EvmRules.Evm.iszero cond :: T') hd1 (by omega)
        (by simp only [List.length_cons]; omega)
      by_cases hc : cond = 0
      · -- The condition is zero: ISZERO gives one and the code jumps to the else block.
        subst hc
        have hoff := toNat_offset (G.target e hen hetgt).2.1 G.size_lt
        have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) iszero_zero
          (by rw [hoff]; exact (G.target e hen hetgt).1)
        rw [hoff] at hj
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega,
          show ¬ S'.length + 1 > 1024 by omega, ite_false, ite_true, SimOutL]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr hetgt⟩, c.offset e, T', M, g1 - 10, st,
          ss, Triple.seq hisz (Triple.seq hpush hj), SR.le hety hR',
          I.target G hen hetgt (m := 3) (by omega) (by omega), R⟩
      · -- The condition is not zero: ISZERO gives zero and the code falls into the next block.
        have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
          (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset e))
          (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) (iszero_nonzero hc)
        simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
          hc, SimOutL]
        refine ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, _, T', M, g1 - 10, st, ss,
          Triple.seq hisz (Triple.seq hpush hj), SR.le hfty hR',
          ⟨hseg, ?_, I.le_top, I.mem⟩, R⟩
        have := I.gas
        omega
    | none =>
      by_cases hD : dropped p b i rest = true
      · rcases dropped_true hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hn⟩
        · -- A jump to the next block, left out: the code falls into it.
          simp only [blockOkL, hT, hD, ite_true, fallOkL, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hok
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hS := I.stack
          simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutL]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, by simp⟩, pc, T, M, g, st, ss,
            Triple.of_imp fun _ h => h, SR.le hok.1.2 hR, I.entry, R⟩
        · -- The last block's STOP, left out: the code ends.
          simp only [lowerInstrs, hT, hD, ite_true, List.nil_append] at I
          have hseg := I.seg
          rw [lowerFrom_nil p c (by omega)] at hseg
          have hpc := hseg.nil_end
          simp only [exec, SimOutL]
          exact SpecG.consequence (stop_of_size_leG (by omega))
            (fun _ h => h) fun evm h => postL_stop R hself evm h
      have hD' : dropped p b i rest = false := by simpa using hD
      have hok' : blockStepL p c mx b (fun h known ty k => blockOkL p c mx b h known ty k rest) h known ty k i =
          true := by
        simpa only [blockOkL, hT, hD', Bool.false_eq_true, ite_false] using hok
      have I' : InvL c code call (lowerInstr i ++ (lowerInstrs p c b rest ++
          lowerFrom p c (b + 1) (p.blocks.drop (b + 1)))) k Rv pc S s M g := by
        simpa only [lowerInstrs, hT, hD', Bool.false_eq_true, ite_false, List.append_assoc] using I
      clear hok hD hD' hT
      have IH := exec_simL (o := o) (ss0 := ss0) G hdata hvalue hstatic hself hcaller ho hbenv htx he b hb Rv rest
      rcases i with mop | ⟨e, ar⟩ | t | t | t | _ | _ | _ | _ | _ | _ | _
      · rcases mop with sop | _ | _ | _ | _ | _ | _
        · by_cases hpush : ∃ v, sop = .push v
          · obtain ⟨v, rfl⟩ := hpush
            simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
            simp only [lowerInstr, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hd (by omega) (by omega)
            have hv : BitVec.ofNat 256 v.toNat = v := by simp
            rw [hv] at hpush
            rw [exec_stack (next := v :: S) rfl (by omega) (by simp; omega)]
            exact SimOutL.pre hpush (IH (h + 1) (v :: known.take 1) _ (v :: S) (v :: T) (k - 1) s next M g1
              st ss hok'.2 (by simp; omega) (by hu_tac)
              ((List.prefix_cons_inj v).2 ((List.take_prefix 1 known).trans hk))
              (SR.cons (τ := some false) rfl hR) (I'.next hok'.1 hseg (by simp) (by omega)) R)
          · have hne : ∀ v, sop ≠ .push v := fun v he => hpush ⟨v, he⟩
            obtain ⟨hk1, byte, hbyte, h', ty', S', T', hstep, hstepT, hR', hh', hlen', hlock, known', hkn,
              hok⟩ := stack_simL (ctx := context o call s) hne hok' hh hk hR
            rw [lowerInstr_stack hne, hbyte] at I'
            simp only [Option.getD_some, List.singleton_append] at I'
            obtain ⟨next, hd, hseg⟩ := I'.seg.head
            simp only [Item.expected] at hd
            obtain ⟨hlt, hcode, rfl⟩ := op_item hd
            rw [← hctx] at hstepT
            have hS := I'.stack; have hG := I'.gas
            obtain ⟨g1, hg1, hrule⟩ := stack_ruleG (M := M) (st := st) (ss := ss) (gas := g)
              (stack := T) hbyte hlt hcode hstepT (by omega) (by omega)
            rw [exec_stack hstep (by omega) (by omega)]
            exact SimOutL.pre hrule (IH h' known' ty' S' T' (k - 1) s (pc + 1) M g1 st ss hok (by omega) (by hu_tac)
              hkn hR' (I'.next hk1 hseg (by omega) (by omega)) R)
        · -- MLOAD.
          rcases known with _ | ⟨ow, known'⟩
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨hk1, h1⟩, hin⟩, hdat⟩, hok'⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := 32) hmod G.top_mod I'.le_top
            (Or.inr hin)
          have hbound : (32 : Word) = 0 ∨ ow.toNat + (32 : Word).toNat ≤ 2 ^ 32 :=
            Or.inr (by have := G.top_le; exact Nat.le_trans hin this)
          have hrule := Logic.mloadG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (start := ow) (rest := T') (gas := g) hlt hcode (by omega)
          rw [load_eq I'.mem] at hrule
          rw [exec_load (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, 32)]).expandBy
          refine SimOutL.pre hrule (IH h [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok' (by simp; omega)
            (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl (by simpa using hR'))
            ⟨hseg, by simp; omega, ?_, by rw [hM']; omega, memRel_expand I'.mem hbound⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- MSTORE.
          rcases known with _ | ⟨ow, known'⟩
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨hk1, h2⟩, hin⟩, hdat⟩, hok'⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨v, S'⟩⟩
          · simp at hh; omega
          · simp at hh; omega
          rcases T with _ | ⟨x', _ | ⟨v', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := 32) hmod G.top_mod I'.le_top
            (Or.inr hin)
          obtain ⟨hmem', hsize⟩ := memRel_store (o := ow) (v := v) I'.mem (by have := G.top_le; omega)
          have hext := size_memoryExtend_extendMemory' (memory := M) (start := ow) (length := 32)
            hmod (by decide)
          rw [size_memoryExtend] at hext
          have h32 : (32 : U256).toNat = 32 := rfl
          rw [h32] at hext
          have hM' : (memoryWrite (memoryExtend M (extendMemory M.size [(ow, 32)]).expandBy)
              ow.toNat (wordBytes v)).size = M.size + (extendMemory M.size [(ow, 32)]).expandBy := by
            rw [hsize, hext]
          rw [exec_store (by omega)]
          refine SimOutL.pre (Logic.mstoreG (start := ow) (value := v) (rest := T') (memory := M)
            (gas := g) hlt hcode (by omega)) (IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) _ _ st ss hok'
            (by omega) (by hu_tac) (List.nil_prefix) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega, hmem'⟩
            ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
      · rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n | _ | name | _
        all_goals try (simp [blockStepL] at hok'; done)
        · -- SLOAD.
          rcases ar with _ | _ | ar
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect1 (w := s.storage x) rfl (by omega)]
          have hrule := Logic.sloadG (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (key := x) (rest := T') (gas := g) (by decide) hlt hcode rfl
            (by split <;> omega)
          rw [R.storage x] at hrule
          refine SimOutL.pre hrule ?_
          have hreads := fun k : Word => State.TransactionState.recordStorageRead_reads st
            msg.currentTarget msg.currentTarget (U256.toBeBytes x) (U256.toBeBytes k) default
          refine IH h [] _ _ _ (k - 1) s (pc + 1) M _ _ _ hok (by simp; omega) (by hu_tac) (List.nil_prefix)
            (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by split <;> omega))
            ⟨fun k => ?_, ?_, R.logs⟩
          · rw [(hreads k).2.1]
            exact R.storage k
          · rw [(hreads x).1]
            exact R.account
        · -- SSTORE.
          rcases ar with _ | _ | _ | ar
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h2⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨v, S'⟩⟩
          · simp at hh; omega
          · simp at hh; omega
          rcases T with _ | ⟨x', _ | ⟨v', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect2 (s' := { s with storage := SolarTV.Machine.update s.storage x v }) rfl
            (by omega)]
          have hcost := sstoreCost_le (st.getStorageOriginal msg.currentTarget (U256.toBeBytes x))
            (st.getStorage msg.currentTarget (U256.toBeBytes x)) v
            (decide (U256.toBeBytes x ∉ ss.accessedStorageKeys.getD msg.currentTarget ∅))
          obtain ⟨st', hnew, hothers, -, hacc, -, -, hrule⟩ := sstore_of_accountG
            (message := msg) (memory := M) (state := st) (substate := ss) (returnData := .empty)
            (key := x) (new := v) (rest := T') (gas := g) (by decide) (by decide) hlt hcode hstatic
            rfl (by simp only [CALL_STIPEND]; omega) (by omega) R.account
          refine SimOutL.pre hrule ?_
          refine IH (h - 2) [] _ S' T' (k - 1) _ (pc + 1) M _ _ _ hok (by omega) (by hu_tac) (List.nil_prefix)
            hR' ?_ ⟨fun k => ?_, by rw [hacc]; exact R.account, R.logs⟩
          · exact ⟨hseg, by omega, by omega, I'.le_top, I'.mem⟩
          by_cases hk : k = x
          · subst hk
            rw [hnew]
            simp [SolarTV.Machine.update]
          · rw [hothers _ _ (Or.inr fun he => hk (U256.toBeBytes_inj he)), R.storage k]
            simp [SolarTV.Machine.update, hk]
        · -- CALLDATALOAD.
          rcases ar with _ | _ | ar
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hk1, h1⟩, hdat⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, S'⟩
          · simp at hh; omega
          rcases T with _ | ⟨x', T'⟩
          · simp at hL
          obtain rfl := (SR.head hR hdat).symm
          have hR' := (SR.uncons.1 hR).2
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          rw [exec_effect1 (w := SolarTV.Machine.calldataWord call x) rfl (by omega)]
          have hrule := Logic.calldataloadG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (start := x) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [hdata, ← calldataWord_eq] at hrule
          exact SimOutL.pre hrule (IH h [] _ _ _ (k - 1) s (pc + 1) M (g - 3) st ss hok (by simp; omega) (by hu_tac)
            (List.nil_prefix) (SR.cons (τ := some false) rfl (by simpa using hR')) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLDATASIZE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 call.calldata.size) rfl (by omega)]
          have hrule := Logic.calldatasizeG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hdata] at hrule
          exact SimOutL.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLVALUE.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 call.callvalue) rfl (by omega)]
          have hrule := Logic.callvalueG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hvalue] at hrule
          exact SimOutL.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- CALLER.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨henv, hk1⟩, hok⟩ := hok'
          obtain ⟨hoc, -⟩ := ho henv
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := o.caller.setWidth 256) rfl (by omega)]
          have hrule := Logic.callerG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hcaller, ← hoc] at hrule
          exact SimOutL.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- ADDRESS.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨hk1, hok⟩ := hok'
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 SolarTV.environment.callee) rfl (by omega)]
          have hrule := Logic.addressG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (stack := T) (gas := g) hlt hcode (by omega)
            (by unfold STACK_LIMIT; omega)
          rw [hself, address_word] at hrule
          exact SimOutL.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
        · -- LOGn.
          rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          simp only [blockStepL, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨⟨hn4, rfl⟩, hk1⟩, hnh⟩, hdat⟩, hin⟩, hlc⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨y, S1⟩⟩
          · simp at hk
          · simp at hk
          obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
          rcases T with _ | ⟨x', _ | ⟨y', T1⟩⟩
          · simp at hL
          · simp at hL
          simp only [List.length_cons] at hh hL hu
          obtain ⟨tops, S2, rfl, hlen⟩ : ∃ tops S2, S1 = tops ++ S2 ∧ tops.length = n :=
            ⟨S1.take n, S1.drop n, (List.take_append_drop n S1).symm, by simp; omega⟩
          obtain ⟨tops', T2, rfl, hlen'⟩ : ∃ tops' T2, T1 = tops' ++ T2 ∧ tops'.length = n :=
            ⟨T1.take n, T1.drop n, (List.take_append_drop n T1).symm, by simp; omega⟩
          subst hlen
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.cons.injEq, List.take_left' hlen',
            List.take_left' rfl] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          have hR' : SR c (ty.drop (tops.length + 2)) S2 T2 := by
            simpa using SR.drop (tops.length + 2) hR
          simp only [lowerInstr, hn4, ite_true, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons, List.length_append] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          have hrule := Logic.logG (n := ⟨tops.length, by omega⟩) (message := msg) (memory := M)
            (state := st) (substate := ss) (returnData := .empty) (start := ow) (size := sw)
            (words := tops) (rest := T2) (gas := g) rfl hlt hcode (decode_log ⟨tops.length, by omega⟩) hstatic
            (show logCost tops.length sw + (extendMemory M.size [(ow, sw)]).cost ≤ g by omega)
          dsimp only at hrule
          rw [exec_log (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          obtain ⟨L, hL1, hL2⟩ := R.logs
          refine SimOutL.pre hrule (IH (h - (tops.length + 2)) [] _ S2 T2 (k - 1) _ (pc + 1) _ _ st _
            hok (by omega) (by hu_tac) (List.nil_prefix) hR' ⟨hseg, by omega, ?_, by rw [hM']; omega,
            memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, ?_⟩)
          · rw [hM']; omega
          · refine ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy)
                ow.toNat sw.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, ?_⟩⟩
            exact read_eq I'.mem
        · -- KECCAK256.
          rcases ar with _ | _ | _ | ar
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          rotate_left
          · simp [blockStepL] at hok'
          rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
          · simp [blockStepL] at hok'
          · simp [blockStepL] at hok'
          simp only [blockStepL, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨henv, hk1⟩, h2⟩, hdat⟩, hin⟩, hkc⟩, hok⟩ := hok'
          rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
          · simp at hk
          · simp at hk
          obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
          obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
          rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
          · simp at hL
          · simp at hL
          have htake := hR.data hdat
          simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
          obtain ⟨rfl, rfl, -⟩ := htake
          have hR' : SR c (ty.drop 2) S' T' := by simpa using SR.drop 2 hR
          simp only [lowerInstr, List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          simp only [List.length_cons] at hS hG hh hL hu
          have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
          obtain ⟨hle, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
            (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
          have hbound : sw = 0 ∨ ow.toNat + sw.toNat ≤ 2 ^ 32 :=
            hin.imp (fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
              (fun h0 => by have := G.top_le; omega)
          obtain ⟨-, hkec⟩ := ho henv
          have hrule := Logic.keccak256G (message := msg) (memory := M) (state := st) (substate := ss)
            (returnData := .empty) (start := ow) (size := sw) (rest := T') (gas := g) hlt hcode
            (by omega)
          rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hrule
          rw [exec_keccak (by omega)]
          have hM' := size_memoryExtend M (extendMemory M.size [(ow, sw)]).expandBy
          refine SimOutL.pre hrule (IH (h - 1) [] _ _ _ (k - 1) _ (pc + 1) _ _ st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR') ⟨hseg, by simp; omega, ?_,
            by rw [hM']; omega, memRel_expand I'.mem hbound⟩ ⟨R.storage, R.account, R.logs⟩)
          rw [hM']; omega
        · -- An environment read of the block or the transaction.
          rcases ar with _ | ar
          rotate_left
          · simp [blockStepL] at hok'
          simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
          obtain ⟨⟨⟨hreads, hsome⟩, hk1⟩, hok⟩ := hok'
          obtain ⟨⟨byte, w⟩, hread⟩ := Option.isSome_iff_exists.1 hsome
          simp only [lowerInstr, hread, Option.map_some, Option.getD_some,
            List.singleton_append] at I'
          obtain ⟨next, hd, hseg⟩ := I'.seg.head
          simp only [Item.expected] at hd
          obtain ⟨hlt, hcode, rfl⟩ := op_item hd
          have hS := I'.stack; have hG := I'.gas
          rw [exec_effect0 (w := BitVec.ofNat 256 w)
            (by simp [SolarTV.Machine.Effect.apply, he hreads name byte w hread]) (by omega)]
          have hrule := env_readG (msg := msg) (M := M) (st := st) (ss := ss) (rd := .empty) (gas := g)
            (stack := T) hread hlt hcode hbenv htx (by omega) (by unfold STACK_LIMIT; omega)
          exact SimOutL.pre hrule (IH (h + 1) [] _ _ _ (k - 1) s (pc + 1) M (g - 2) st ss hok
            (by simp; omega) (by hu_tac) (List.nil_prefix) (SR.cons (τ := some false) rfl hR) (I'.next hk1 hseg (by simp) (by omega)) R)
      · -- JUMP.
        simp only [blockStepL, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hk2, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩ := hok'
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, -⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd1 (by omega) (by omega)
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (rest := T) hlt2 hcode2 (show 8 ≤ g1 by omega)
          (by rw [hoff]; exact (G.target t htn htgt).1)
        rw [hoff] at hj
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false, SimOutL]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T, M, g1 - 8, st, ss,
          Triple.seq hpush hj, SR.le hty hR,
          I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- JUMPI.
        simp only [blockStepL, jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨⟨hk2, h1⟩, hdat⟩, ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩⟩, hok'⟩ := hok'
        rcases S with _ | ⟨cond, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨cond', T'⟩
        · simp at hL
        obtain rfl := (SR.head hR hdat).symm
        have hR' := (SR.uncons.1 hR).2
        simp only [lowerInstr, List.cons_append, List.nil_append] at I'
        obtain ⟨n1, hd1, hs1⟩ := I'.seg.head
        obtain ⟨n2, hd2, hseg⟩ := hs1.head
        simp only [Item.expected] at hd1 hd2
        obtain ⟨hlt2, hcode2, rfl⟩ := op_item hd2
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target t htn htgt).2.1 G.size_lt
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := cond :: T') hd1 (by omega) (by simp; omega)
        by_cases hc : cond = 0
        · subst hc
          have hj := Logic.jumpi_of_eq_zeroG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) rfl
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            ite_true]
          exact SimOutL.pre (Triple.seq hpush hj) (IH (h - 1) [] _ S' T' (k - 2) s (n1 + 1) M
            (g1 - 10) st ss hok' (by omega) (by hu_tac) (List.nil_prefix) hR'
            (I'.next2 hk2 hseg (by simp only [List.length_cons]; omega) (by omega)) R)
        · have hj := Logic.jumpi_takenG (message := msg) (memory := M) (state := st)
            (substate := ss) (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset t))
            (rest := T') hlt2 hcode2 (show 10 ≤ g1 by omega) hc
            (by rw [hoff]; exact (G.target t htn htgt).1)
          rw [hoff] at hj
          simp only [exec, List.length_cons, show ¬ S'.length + 1 + 1 > 1024 by omega, ite_false,
            hc, SimOutL]
          exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset t, T', M, g1 - 10, st,
            ss, Triple.seq hpush hj, SR.le hty hR',
            I'.target G htn htgt (m := 2) (by omega) (by omega), R⟩
      · -- A pushed return label: a PUSH of the block's offset.
        simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨⟨⟨hk1, hmem⟩, ht32⟩, hok⟩ := hok'
        have hmem' : t ∈ c.rets := by simpa using hmem
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, hseg⟩ := I'.seg.head
        simp only [Item.expected] at hd
        have hS := I'.stack; have hG := I'.gas
        obtain ⟨g1, hg1, hpush⟩ := push_itemG (msg := msg) (M := M) (st := st) (ss := ss) (gas := g)
          (stack := T) hd (by omega) (by omega)
        have htn : (BitVec.ofNat 256 t).toNat = t := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        simp only [exec, show ¬ S.length + 1 > 1024 by omega, ite_false]
        exact SimOutL.pre hpush (IH (h + 1) [] _ _ _ (k - 1) s next M g1 st ss hok (by simp; omega) (by hu_tac)
          (List.nil_prefix) (SR.cons ⟨by rw [htn]; exact hmem', by rw [htn]⟩ hR)
          (I'.next hk1 hseg (by simp) (by omega)) R)
      · -- A dynamic jump to a return label: a JUMP to the label's offset.
        simp only [blockStepL, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
          List.all_eq_true] at hok'
        obtain ⟨⟨⟨hk1, h1⟩, hlab⟩, hall⟩ := hok'
        rcases S with _ | ⟨x, S'⟩
        · simp at hh; omega
        rcases T with _ | ⟨y, T'⟩
        · simp at hL
        obtain ⟨hw, hR'⟩ := SR.uncons.1 hR
        rw [hlab] at hw
        obtain ⟨hmem, rfl⟩ := hw
        have hj' := hall _ hmem
        simp only [jumpOkL, Bool.and_eq_true, decide_eq_true_eq] at hj'
        obtain ⟨⟨⟨⟨htn, htgt⟩, hneed⟩, hty⟩, hcost⟩ := hj'
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        have hS := I'.stack; have hG := I'.gas
        simp only [List.length_cons] at hS hh hL hu
        have hoff := toNat_offset (G.target _ htn htgt).2.1 G.size_lt
        have hj := Logic.jumpG (message := msg) (memory := M) (state := st) (substate := ss)
          (returnData := .empty) (destination := BitVec.ofNat 256 (c.offset x.toNat)) (rest := T')
          hlt hcode (show 8 ≤ g by omega) (by rw [hoff]; exact (G.target _ htn htgt).1)
        rw [hoff] at hj
        simp only [exec, SimOutL]
        exact ⟨⟨by omega, fun _ => ⟨by omega, by omega⟩, Or.inr htgt⟩, c.offset x.toNat, T', M, g - 8, st,
          ss, hj, SR.le hty hR', I'.target G htn htgt (m := 1) (by omega) (by omega), R⟩
      · -- A conditional dynamic jump and a jump table: outside the fragment.
        simp [blockStepL] at hok'
      · simp [blockStepL] at hok'
      · -- STOP.
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        simp only [exec, SimOutL]
        exact SpecG.consequence (Logic.stopG hlt hcode) (fun _ h => h)
          fun evm h => postL_stop R hself evm h
      · -- RETURN.
        rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        simp only [blockStepL, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
        · simp at hk
        · simp at hk
        obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
        rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [exec, SolarTV.EVM.Program.output, SimOutL, Bool.false_eq_true, ↓reduceIte]
        exact SpecG.consequence (return_postSG (ss := ss) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl (R.slot hself)) (fun _ h => h)
          (fun _ h => ⟨ss, h, R.logs⟩)
      · -- REVERT.
        rcases known with _ | ⟨ow, _ | ⟨sw, known'⟩⟩
        · simp [blockStepL] at hok'
        · simp [blockStepL] at hok'
        simp only [blockStepL, rangeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok'
        obtain ⟨hdat, hin⟩ := hok'
        rcases S with _ | ⟨x, _ | ⟨y, S'⟩⟩
        · simp at hk
        · simp at hk
        obtain ⟨rfl, hk'⟩ := List.cons_prefix_cons.1 hk
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hk'
        rcases T with _ | ⟨x', _ | ⟨y', T'⟩⟩
        · simp at hL
        · simp at hL
        have htake := hR.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, -⟩ := htake
        simp only [lowerInstr, List.singleton_append] at I'
        obtain ⟨next, hd, -⟩ := I'.seg.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, -⟩ := op_item hd
        have hG := I'.gas
        have hmod : M.size % 32 = 0 := by rw [I'.mem.1]; omega
        obtain ⟨-, hcost⟩ := extend_cost (o := ow) (sz := sw) hmod G.top_mod I'.le_top
          (hin.imp_left fun h0 => BitVec.eq_of_toNat_eq (by simpa using h0))
        simp only [exec, SolarTV.EVM.Program.output, SimOutL, ↓reduceIte]
        exact SpecG.consequence (revert_postSG (ss := ss) (by decide) hlt hcode (by omega) rfl
          (by rw [read_eq I'.mem]; rfl) rfl) (fun _ h => h) (fun _ h => ⟨ss, h, R.logs⟩)
      · simp [blockStepL] at hok'



end SolidCore.Refinement.Solar.AssembleLoop

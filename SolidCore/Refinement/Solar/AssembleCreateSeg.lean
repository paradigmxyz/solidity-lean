import SolidCore.Refinement.Solar.AssembleCreateBack
import SolidCore.Refinement.Solar.AssembleCallValueEffect
import SolidCore.Refinement.Solar.AssembleCodeCopy

/-!
# CREATE2 as a cut of a run, at the frame's own gas

The checker cuts a block at each CREATE2 (as it does at a STATICCALL, `AssembleCallCut.staticcall_cut`):
from a run of the bytecode that succeeds, `create2_cut` reads the creation back at the frame's own gas
(`AssembleCreateBack.create2_back`) and gives the run's answers to it: the word the frame pushes (the
EIP-1014 address when the init code ends with no error, 0 when the creation fails or sends no message),
the return data the frame is left with, and the storage of the frame's account after it, which a
reentrant init code may have changed. A run's table of creations (`CreateTable`) records them in order,
and the oracle of every extension of it (`createOracle`) makes SolarTV's CREATE2 push that word, leave that
return data and storage, and record the init code EthLib runs; memory, the storage relation, the
account and the logs of the frame are related again (`Assemble.Rel`).

`createOracle o A` answers a world whose last message is a creation from the table, by the number of
creations in it, and every other world as `o` does, so it extends the oracle of calls and GAS reads of a run
(`AssembleCallWorld.OS`, `RunOracle.tableOracle`) without changing their answers (`createOracle_other`).

The init code is the callee's frame and nothing is assumed of its code. What SolarTV's frame cannot see
is named (`CreateOk`, a hypothesis on the frame that ends the creation's message, asked only of messages
from this frame with this init code): the creator's account still exists after it, a creation that
succeeds adds no log (SolarTV's world records only the frame's own logs, so a logging init code would
make the observables differ), and the revert data of a failed creation has fewer than `2 ^ 256` bytes
(as `AssembleCallCut.OutputFits` for calls).
-/

namespace SolidCore.Refinement.Solar.AssembleCreateSeg

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleEffects SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCreate SolidCore.Refinement.Solar.AssembleCreateBack
open SolidCore.Refinement.Solar.AssembleCallValueEffect
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-! ## A run's answers to its creations -/

/-- A creation event. -/
def isCreateE : Event → Bool
  | .create .. => true
  | _ => false

/-- The creations of a world. -/
def creates (w : List Event) : Nat := (w.filter isCreateE).length

/-- Whether the last message a world sent is a creation. -/
def lastCreate (w : List Event) : Bool :=
  match (w.filter Event.sends).getLast? with
  | some (.create ..) => true
  | _ => false

@[simp] theorem lastCreate_create (w : List Event) (ops : List Word) (c : List Memory.Byte)
    (sto tr : Word → Word) : lastCreate (w ++ [.create ops c sto tr]) = true := by
  simp [lastCreate, List.filter_append, Event.sends]

@[simp] theorem creates_create (w : List Event) (ops : List Word) (c : List Memory.Byte)
    (sto tr : Word → Word) : creates (w ++ [.create ops c sto tr]) = creates w + 1 := by
  simp [creates, List.filter_append, List.filter_cons, isCreateE]

@[simp] theorem lastCreate_read (w : List Event) (n : String) :
    lastCreate (w ++ [.read n]) = lastCreate w := by
  simp [lastCreate, List.filter_append, Event.sends]

@[simp] theorem lastCreate_log (w : List Event) (t : List Word) (d : List Memory.Byte) :
    lastCreate (w ++ [.log t d]) = lastCreate w := by
  simp [lastCreate, List.filter_append, Event.sends]

@[simp] theorem lastCreate_call (w : List Event) (k : SolarTV.Machine.CallKind) (ops : List Word)
    (i : List Memory.Byte) (sto tr : Word → Word) :
    lastCreate (w ++ [.call k ops i sto tr]) = false := by
  simp [lastCreate, List.filter_append, Event.sends]

@[simp] theorem creates_read (w : List Event) (n : String) : creates (w ++ [.read n]) = creates w := by
  simp [creates, List.filter_append, isCreateE]

@[simp] theorem creates_log (w : List Event) (t : List Word) (d : List Memory.Byte) :
    creates (w ++ [.log t d]) = creates w := by
  simp [creates, List.filter_append, isCreateE]

/-- What a run answers to its creations, in order: the word each pushed, the return data it left, and
the storage of the frame's account after it. -/
structure CreateTable where
  addrs : List Word := []
  outs : List ByteArray := []
  stores : List (Word → Word) := []

/-- A table that answers every creation the shorter one does, the same. -/
def CreateTable.Le (A B : CreateTable) : Prop :=
  A.addrs <+: B.addrs ∧ A.outs <+: B.outs ∧ A.stores <+: B.stores

theorem CreateTable.Le.refl (A : CreateTable) : A.Le A :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem CreateTable.Le.trans {A B C : CreateTable} (h1 : A.Le B) (h2 : B.Le C) : A.Le C :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- The table with one more creation. -/
def CreateTable.push (A : CreateTable) (r : Word) (out : ByteArray) (sto : Word → Word) :
    CreateTable :=
  { addrs := A.addrs ++ [r], outs := A.outs ++ [out], stores := A.stores ++ [sto] }

theorem CreateTable.le_push (A : CreateTable) (r : Word) (out : ByteArray) (sto : Word → Word) :
    A.Le (A.push r out sto) :=
  ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_append _ _⟩

/-- The return data the last creation of a world left. -/
def CreateTable.out (A : CreateTable) (w : List Event) : ByteArray := A.outs.getD (creates w - 1) .empty

/-- **The oracle of a run's creations**: a world whose last message is a creation is answered from
the table (the word pushed, the return data, the storage after), every other world as by `o`. -/
def createOracle (o : Oracle) (A : CreateTable) : Oracle :=
  { o with
    env := fun name w args =>
      if lastCreate w = true then
        if name = "returndatasize" ∧ args = [] then BitVec.ofNat 256 (A.out w).size
        else if name = "returndata" then
          match args with
          | [i] => BitVec.ofNat 256 (byteAt (A.out w) i.toNat).toNat
          | _ => o.env name w args
        else o.env name w args
      else o.env name w args
    result := fun w => if lastCreate w = true then A.addrs.getD (creates w - 1) 0 else o.result w
    storageAfter := fun w =>
      if lastCreate w = true then A.stores.getD (creates w - 1) (o.storageAfter w)
      else o.storageAfter w }

/-- Every world whose last message is no creation is answered as by `o`. -/
theorem createOracle_other {o : Oracle} {A : CreateTable} {w : List Event} (h : lastCreate w = false) :
    (createOracle o A).result w = o.result w ∧ (createOracle o A).storageAfter w = o.storageAfter w ∧
      (createOracle o A).transientAfter w = o.transientAfter w ∧
      ∀ name args, (createOracle o A).env name w args = o.env name w args := by
  simp [createOracle, h]

/-- The hash, the caller and the reads of the frame's code are `o`'s. -/
theorem createOracle_keccak (o : Oracle) (A : CreateTable) : (createOracle o A).keccak = o.keccak := rfl

theorem createOracle_caller (o : Oracle) (A : CreateTable) : (createOracle o A).caller = o.caller := rfl

theorem createOracle_code (o : Oracle) (A : CreateTable) (args : List Word) :
    (createOracle o A).env "code" [] args = o.env "code" [] args := by
  simp [createOracle, lastCreate]

/-- The storage of an account of EthLib's state, as SolarTV's words. -/
def storeOf (st : State.TransactionState) (a : Address) : Word → Word :=
  fun k => st.getStorage a (U256.toBeBytes k)

/-- SolarTV's state after a CREATE2 whose storage after is `sto`. -/
def postCreate (o : Oracle) (s : State) (sto : Word → Word) (value start size salt : Word) : State :=
  ⟨s.memory.expand start.toNat size.toNat, sto, o.transientAfter (createWorld s value start size salt),
    createWorld s value start size salt⟩

/-- **SolarTV's CREATE2 under the oracle of every extension of a table with the creation**: it
pushes the table's word, leaves the table's return data and storage. -/
theorem create2_apply {o : Oracle} {A A'' : CreateTable} {call : Call} {s : State}
    {value start size salt r : Word} {out : ByteArray} {sto : Word → Word}
    (hA : A.addrs.length = creates s.world) (hAo : A.outs.length = creates s.world)
    (hAs : A.stores.length = creates s.world) (hle : (A.push r out sto).Le A'')
    (hr : r.toNat < 2 ^ 160) (hsz : out.size < 2 ^ 256) :
    Effect.apply (createOracle o A'') call .create2 [value, start, size, salt] s =
        some (some r, postCreate o s sto value start size salt) ∧
      RdRel (createOracle o A'') (createWorld s value start size salt) out := by
  have haddr : A''.addrs.getD (creates s.world) 0 = r := by
    rw [AssembleRun.getD_of_prefix hle.1 (by simp [CreateTable.push, hA])]
    simp [CreateTable.push, hA]
  have hout : A''.outs.getD (creates s.world) .empty = out := by
    rw [AssembleRun.getD_of_prefix hle.2.1 (by simp [CreateTable.push, hAo])]
    simp [CreateTable.push, hAo]
  have hsto : ∀ d, A''.stores.getD (creates s.world) d = sto := by
    intro d
    rw [AssembleRun.getD_of_prefix hle.2.2 (by simp [CreateTable.push, hAs])]
    simp [CreateTable.push, hAs]
  have hr' : BitVec.ofNat 256 (r.toNat % 2 ^ 160) = r := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simp only [Effect.apply, created, createOracle, postCreate, createWorld, lastCreate_create,
      creates_create, Nat.add_sub_cancel, ite_true, haddr, hsto, hr']
  · simp only [returndataSize, createOracle, createWorld, lastCreate_create, and_self, ite_true,
      CreateTable.out, creates_create, Nat.add_sub_cancel, hout, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz
  · have hi' : i < 2 ^ 256 := by omega
    simp only [returndataByte, createOracle, createWorld, lastCreate_create, ite_true,
      show ¬("returndata" = "returndatasize" ∧ [BitVec.ofNat 256 i] = []) by simp, ite_false,
      CreateTable.out, creates_create, Nat.add_sub_cancel, hout, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hi']
    exact AssembleCodeCopy.setWidth_ofNat_byte _

/-! ## The frame after a creation -/

/-- **Named hypothesis on the frame that ends a creation's message**: the creator's account still
exists after it, a creation that succeeds adds no log, and the revert data has fewer than `2 ^ 256`
bytes. -/
def CreateOk (msg : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  (child.state.getAccountOptional msg.currentTarget).isSome = true ∧
    (child.error.isNone = true → child.substate.logs.toList = []) ∧ child.output.size < 2 ^ 256

/-- A creation event writes no log. -/
theorem logsRel_create {a : Address} {ss0 ss : Substate} {w : List Event} (ops : List Word)
    (c : List Memory.Byte) (sto tr : Word → Word) (h : LogsRel a ss0 ss w) :
    LogsRel a ss0 ss (w ++ [.create ops c sto tr]) := by
  obtain ⟨L, h1, h2⟩ := h
  refine ⟨L, h1, ?_⟩
  rw [List.filter_append]
  simpa [isLogE] using h2

/-- Adding one to the nonce of an account keeps it. -/
theorem account_incrementNonce {tx tx' : State.TransactionState} {a : Address}
    (h : tx.incrementNonce .fusaka a = .ok tx') : (tx'.getAccountOptional a).isSome = true := by
  have h' : tx.modifyState .fusaka a (fun account => .ok { account with nonce := account.nonce + 1 }) =
      .ok tx' := h
  obtain ⟨account, hf, rfl⟩ := EthLib.Execution.State.TransactionState.modifyState_eq_ok_iff.mp h'
  simp only [Except.ok.injEq] at hf
  subst hf
  have hne : ((tx.recordAccountRead a).setAccount a (some { tx.getAccount a with
      nonce := (tx.getAccount a).nonce + 1 })).accountExistsAndIsEmpty a = false := by
    simp [State.TransactionState.accountExistsAndIsEmpty,
      EthLib.Execution.State.TransactionState.getAccountOptional_setAccount_self]
  rw [hne, Bool.and_false]
  simp [EthLib.Execution.State.TransactionState.getAccountOptional_setAccount_self]

/-- A creation passes on at most the gas left. -/
theorem createMessageGas_le (x : Nat) : createMessageGas .fusaka x ≤ x := by
  unfold createMessageGas maxMessageCallGas
  split <;> omega

/-- The caller's state after the callee is the callee's. -/
theorem incorporateChild_state (caller child : Evm .fusaka Nat) :
    (incorporateChild .fusaka caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

/-! ## CREATE2 at the frame's own gas -/

/-- **CREATE2 as a cut of a run that succeeds**: the creation had the gas for its price, and the run
goes on from the frame after it, pushing the word `r` (the EIP-1014 address on success, 0 otherwise),
with return data `out` and the storage of the frame's account after it. Under the oracle of every
extension of the table with these answers, SolarTV's CREATE2 pushes `r`, leaves `out` and that storage,
and every relation of a block entry holds again, at no more gas than the frame had. -/
theorem create2_cut {code : ByteArray} {msg : Message .fusaka} {call : Call} {pc g G : Nat}
    {M : ByteArray} {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray}
    {value start size salt : U256} {Tr : List U256} {s : State} {evm : Evm .fusaka Nat}
    (o : Oracle) (A : CreateTable)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 256)
    (hat : At code msg pc (value :: start :: size :: salt :: Tr) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf5) (hstatic : msg.isStatic = false)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hq : ∀ caller m child, P caller m child → m.caller = msg.currentTarget →
      m.currentTarget = create2Address msg.currentTarget salt (memoryReadBytes (memoryExtend M
        (extendMemory M.size [(start, size)]).expandBy) start.toNat size.toNat) →
      m.code = memoryReadBytes (memoryExtend M (extendMemory M.size [(start, size)]).expandBy)
        start.toNat size.toNat → m.value = value →
      m.gas = createMessageGas .fusaka (g - cost2 M.size start size) → CreateOk msg child)
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
    ⟨-, -, -, -, caller, mm, child, after, within', hP, hcg, -, hcsub, hmg, hmc, hmt, hmcode, hmv, -,
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
    obtain ⟨hacc, hlogs, hfit⟩ := hq caller mm child hP hmc hmt hmcode hmv hmg
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

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSeg.create2_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_cut

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSeg.create2_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_apply

/-! ## CODECOPY at the frame's own gas -/

/-- The oracle of a run's creations reads the frame's code as `o` does. -/
theorem codeOk_createOracle {o : Oracle} {code : ByteArray} (A : CreateTable)
    (hc : AssembleCodeCopy.CodeOk o code) : AssembleCodeCopy.CodeOk (createOracle o A) code := by
  intro w
  rw [createOracle_code]
  exact hc w

/-- The oracle of a run's table reads the frame's code as its base does. -/
theorem codeOk_tableOracle {o : Oracle} {code : ByteArray} (T : RunTable)
    (hc : AssembleCodeCopy.CodeOk o code) : AssembleCodeCopy.CodeOk (tableOracle o T) code := by
  intro w
  have : (tableOracle o T).env "code" [] [w] = o.env "code" [] [w] := by
    simp [tableOracle]
  rw [this]
  exact hc w

/-- SolarTV's state after CODECOPY. -/
def codeCopied (o : Oracle) (s : State) (d off sz : Word) : State :=
  { s with memory := s.memory.write d.toNat sz.toNat (fun i => codeByte o (off.toNat + i)) }

/-- **CODECOPY as a cut of a run that succeeds**: with a code offset below `2 ^ 32` and an oracle that
reads the frame's code, the copy had its price, SolarTV's copy writes the bytes EthLib's does, and
every relation of a block entry holds again (memory is all it changes). -/
theorem codecopy_cut {code : ByteArray} {msg : Message .fusaka} {call : Call} {o : Oracle}
    (hc : AssembleCodeCopy.CodeOk o code) {pc g G : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss ss0 : Substate} {rd : ByteArray} {d off sz : U256}
    {Tr : List U256} {s : State} {evm : Evm .fusaka Nat} (hoff : off.toNat < 2 ^ 32)
    (hm : MemRel s.memory M) (R : Rel msg ss0 st ss s) (hb : MemBudget G M g) (hG : G < 2 ^ 256)
    (hat : At code msg pc (d :: off :: sz :: Tr) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      Effect.apply o call .codecopy [d, off, sz] s = some (none, codeCopied o s d off sz) ∧
      MemRel (codeCopied o s d off sz).memory M' ∧ Rel msg ss0 st ss (codeCopied o s d off sz) ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) Tr M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨M', g', m, within', hmem, hb', hg', hat', hrun'⟩ :=
    AssembleCodeCopy.codecopy_dyn hc hoff hm hb hG hat hlt hbyte within hrun hok
  exact ⟨M', g', m, within', AssembleCodeCopy.codecopy_effect o call d off sz s, hmem,
    ⟨R.storage, R.account, R.logs⟩, hb', hg', hat', hrun'⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSeg.codecopy_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms codecopy_cut

end SolidCore.Refinement.Solar.AssembleCreateSeg

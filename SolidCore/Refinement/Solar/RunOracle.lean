import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# One oracle per run

A call's outcomes in EthLib depend on the gas and on the other accounts: what GAS pushes, whether
a call succeeds, what it returns and the storage after it. No single SolarTV oracle describes every
run, and a fixed oracle constrained to agree with EthLib on all of them at once is unsatisfiable.
So the theorem from EVM IR to bytecode takes this form (`WithinRun`): for every gas and every call
of the scope, there is an oracle `o`, meeting the constraints `Ok` the certificate names, under
which every result of the bytecode on that call at that gas is the EVM IR's or a failure that
changes nothing. It composes with stages and specifications proved for every oracle
(`holds_of_withinRun`), which is how the MIR and source stages are stated.

`tableOracle` is the oracle a run gives: its answers to GAS, to RETURNDATASIZE and RETURNDATACOPY,
to the success of a call or creation and to the storage after it are read from tables indexed by
how many such events the world holds, so they are a function of the world by construction and
every table is realised (no consistency hypothesis needs a satisfiability argument beyond the
definition). Appending a log or a GAS read keeps the return data (`rd_log`, `rd_read`), as EthLib
does. `tableOracle` keeps the caller, the hash and the reads of the block and the transaction of
the oracle it extends, so `OracleOk` and `EnvOk` carry over (`tableOracle_oracleOk`,
`tableOracle_envOk`).

`withinRun_of_checkL` restates the assembly theorem for code with loops in this form, choosing the
oracle; for code with neither GAS nor calls the choice is any oracle meeting `OracleOk` and `EnvOk`.
-/

namespace SolidCore.Refinement.Solar.RunOracle

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble
open EthLib.Base (byteAt)

/-! ## The theorem form -/

/-- **Per-run refinement**: for every gas and every call of the scope there is an oracle meeting
`Ok`, under which every result of `code` on that call at that gas is the result of `p` in
`sem o`, or a failure that leaves the storage and logs nothing. -/
def WithinRun (sem : Oracle → Sem) (p : ∀ o, (sem o).Prog) (code : ByteArray) (scope : Call → Prop)
    (Ok : Oracle → Prop) : Prop :=
  ∀ gas call, scope call → ∃ o, Ok o ∧ Within (sem o) (ethLibWith gas) (p o) code (· = call)

/-- A refinement under one oracle meeting `Ok` at every gas is a per-run refinement. -/
theorem WithinRun.of_fixed {sem : Oracle → Sem} {p : ∀ o, (sem o).Prog} {code : ByteArray}
    {scope : Call → Prop} {Ok : Oracle → Prop} (o : Oracle) (ho : Ok o)
    (h : ∀ gas, Within (sem o) (ethLibWith gas) (p o) code scope) :
    WithinRun sem p code scope Ok :=
  fun gas call hc => ⟨o, ho, fun call' h' obs hrun => h gas call' (h' ▸ hc) obs hrun⟩

/-- Stages proved for every oracle meeting `Ok` before a per-run refinement, with the earlier
program defined wherever the later one is, give a per-run refinement from the earlier program. -/
theorem WithinRun.of_stage {A sem : Oracle → Sem} {q : ∀ o, (A o).Prog} {p : ∀ o, (sem o).Prog}
    {code : ByteArray} {scope : Call → Prop} {Ok : Oracle → Prop}
    (stage : ∀ o, Ok o → Stage (A o) (sem o) (q o) (p o) scope)
    (defined : ∀ o, Ok o → ∀ call, scope call → (A o).run (q o) call = none →
      (sem o).run (p o) call = none)
    (h : WithinRun sem p code scope Ok) : WithinRun A q code scope Ok := by
  intro gas call hc
  obtain ⟨o, ho, hw⟩ := h gas call hc
  refine ⟨o, ho, fun call' h' obs hrun => ?_⟩
  subst h'
  rcases hw call' rfl obs hrun with e | e
  · left
    cases hq : (A o).run (q o) call' with
    | none => rw [defined o ho call' hc hq] at e; cases e
    | some obs' =>
      have := stage o ho call' hc obs' hq
      rw [this] at e
      rw [e]
  · exact Or.inr e

/-- **A specification proved for every oracle meeting `Ok` holds of the bytecode at every gas.** -/
theorem holds_of_withinRun {St : Type} {sem : Oracle → Sem} {p : ∀ o, (sem o).Prog}
    {code : ByteArray} {spec : ContractSpec St} {Ok : Oracle → Prop}
    (holds : ∀ o, Ok o → Holds (sem o) (p o) spec) (h : WithinRun sem p code spec.Calls Ok)
    (gas : Nat) : Holds (ethLibWith gas) code spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hc : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  obtain ⟨o, ho, hw⟩ := h gas _ hc
  rcases hw _ rfl obs hrun with e | ⟨hs, hst, hl⟩
  · exact holds o ho f hf args ht v hv σ hinv hreq obs e
  · exact ⟨fun h'' => absurd (hs.symm.trans h'') (by decide), fun _ => ⟨hst, hl⟩⟩

/-! ## The oracle of a run -/

/-- An event that sends a message: a call or a creation. Their results, return data and the
storage after them are what the oracle answers. -/
def Event.sends : Event → Bool
  | .call .. | .create .. => true
  | .log .. | .read _ => false

/-- An event that reads the gas left. -/
def Event.readsGas : Event → Bool
  | .read n => n == "gas"
  | _ => false

/-- The messages a world has sent. -/
def sent (w : List Event) : Nat := (w.filter Event.sends).length

/-- The GAS reads of a world. -/
def gasReads (w : List Event) : Nat := (w.filter Event.readsGas).length

/-- What a run of the bytecode answers, in order: for each message it sends, its success, its
return data and the storage and transient storage after it; for each GAS read, the gas pushed. -/
structure RunTable where
  oks : List Bool := []
  outs : List ByteArray := []
  stores : List (Word → Word) := []
  transients : List (Word → Word) := []
  gases : List Nat := []

/-- The return data a world leaves under the table: the last message's, empty before any. -/
def RunTable.out (T : RunTable) (w : List Event) : ByteArray :=
  if sent w = 0 then .empty else T.outs.getD (sent w - 1) .empty

/-- The oracle a run gives, over `base` for everything a run does not decide. -/
def tableOracle (base : Oracle) (T : RunTable) : Oracle :=
  { base with
    env := fun name w args =>
      if name = "returndatasize" ∧ args = [] then BitVec.ofNat 256 (T.out w).size
      else if name = "returndata" then
        match args with
        | [i] => BitVec.ofNat 256 (byteAt (T.out w) i.toNat).toNat
        | _ => base.env name w args
      else if name = "gas" ∧ args = [] then
        BitVec.ofNat 256 (T.gases.getD (gasReads w - 1) 0)
      else base.env name w args
    result := fun w => if sent w ≠ 0 ∧ T.oks.getD (sent w - 1) false = true then 1 else 0
    storageAfter := fun w =>
      if sent w = 0 then base.storageAfter w else T.stores.getD (sent w - 1) (base.storageAfter w)
    transientAfter := fun w =>
      if sent w = 0 then base.transientAfter w
      else T.transients.getD (sent w - 1) (base.transientAfter w) }

/-! ## What the oracle of a run answers -/

@[simp] theorem sent_append (w w' : List Event) : sent (w ++ w') = sent w + sent w' := by
  simp [sent, List.filter_append]

@[simp] theorem gasReads_append (w w' : List Event) :
    gasReads (w ++ w') = gasReads w + gasReads w' := by
  simp [gasReads, List.filter_append]

@[simp] theorem sent_log (t : List Word) (d : List Memory.Byte) : sent [.log t d] = 0 := rfl
@[simp] theorem sent_read (n : String) : sent [.read n] = 0 := rfl
@[simp] theorem sent_call (k : CallKind) (ops : List Word) (i : List Memory.Byte)
    (s t : Word → Word) : sent [.call k ops i s t] = 1 := rfl
@[simp] theorem gasReads_gas : gasReads [.read "gas"] = 1 := rfl
@[simp] theorem gasReads_log (t : List Word) (d : List Memory.Byte) : gasReads [.log t d] = 0 := rfl
@[simp] theorem gasReads_call (k : CallKind) (ops : List Word) (i : List Memory.Byte)
    (s t : Word → Word) : gasReads [.call k ops i s t] = 0 := rfl

/-- The size of the return data is the table's. -/
theorem returndataSize_table (base : Oracle) (T : RunTable) (w : List Event) :
    returndataSize (tableOracle base T) w = BitVec.ofNat 256 (T.out w).size := by
  simp [returndataSize, tableOracle]

/-- Each byte of the return data is the table's. -/
theorem returndataByte_table (base : Oracle) (T : RunTable) (w : List Event) (i : Nat)
    (hi : i < 2 ^ 256) :
    returndataByte (tableOracle base T) w i = (byteAt (T.out w) i).toBitVec := by
  simp only [returndataByte, tableOracle]
  simp only [show ¬("returndata" = "returndatasize" ∧ [BitVec.ofNat 256 i] = []) by simp, ite_false,
    ite_true, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  have := (byteAt (T.out w) i).toNat_lt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The `k`-th GAS read pushes the table's `k`-th gas. -/
theorem gas_table (base : Oracle) (T : RunTable) (w : List Event) :
    (tableOracle base T).env "gas" (w ++ [.read "gas"]) [] =
      BitVec.ofNat 256 (T.gases.getD (gasReads w) 0) := by
  simp [tableOracle]

/-- A call's success flag is the table's. -/
theorem callFlag_table (base : Oracle) (T : RunTable) (w : List Event) (k : CallKind)
    (ops : List Word) (i : List Memory.Byte) (s t : Word → Word) :
    callFlag (tableOracle base T) (w ++ [.call k ops i s t]) =
      if T.oks.getD (sent w) false = true then 1 else 0 := by
  simp only [callFlag, tableOracle, sent_append, sent_call]
  cases h : T.oks[sent w]?.getD false <;> simp [List.getD_eq_getElem?_getD, h]

/-- The storage after the call is the table's. -/
theorem storageAfter_table (base : Oracle) (T : RunTable) (w : List Event) (k : CallKind)
    (ops : List Word) (i : List Memory.Byte) (s t : Word → Word) :
    (tableOracle base T).storageAfter (w ++ [.call k ops i s t]) =
      T.stores.getD (sent w) (base.storageAfter (w ++ [.call k ops i s t])) := by
  simp [tableOracle]

/-- After a call the return data is the call's output in the table. -/
theorem out_call (T : RunTable) (w : List Event) (k : CallKind) (ops : List Word)
    (i : List Memory.Byte) (s t : Word → Word) :
    T.out (w ++ [.call k ops i s t]) = T.outs.getD (sent w) .empty := by
  simp [RunTable.out]

/-- A log keeps the return data. -/
theorem rd_log (T : RunTable) (w : List Event) (t : List Word) (d : List Memory.Byte) :
    T.out (w ++ [.log t d]) = T.out w := by
  simp [RunTable.out]

/-- A read of the world, GAS among them, keeps the return data. -/
theorem rd_read (T : RunTable) (w : List Event) (n : String) : T.out (w ++ [.read n]) = T.out w := by
  simp [RunTable.out]

/-- Before any message the return data is empty, as EthLib's frame starts with. -/
theorem out_nil (T : RunTable) : T.out [] = .empty := rfl

/-- The oracle of a run keeps the caller and the hash. -/
theorem tableOracle_oracleOk {base : Oracle} (T : RunTable) (h : OracleOk base) :
    OracleOk (tableOracle base T) := h

/-- The oracle of a run keeps the reads of the block and the transaction. -/
theorem tableOracle_envOk {base : Oracle} (T : RunTable) (h : EnvOk base) :
    EnvOk (tableOracle base T) := by
  intro name byte w he world
  have hn : name ≠ "returndatasize" ∧ name ≠ "returndata" ∧ name ≠ "gas" := by
    unfold envRead at he
    refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; simp at he)
  simp only [tableOracle, hn.1, hn.2.1, hn.2.2, false_and, ite_false]
  exact h name byte w he world

/-- Every oracle extends to one meeting `OracleOk` and `EnvOk`, with any table: the constraints
the assembly theorem puts on the oracle of a run are satisfiable together. -/
theorem table_ok (o : Oracle) (T : RunTable) :
    OracleOk (tableOracle (envOracle (ethOracle o)) T) ∧
      EnvOk (tableOracle (envOracle (ethOracle o)) T) :=
  ⟨tableOracle_oracleOk T (ethOracle_ok o), tableOracle_envOk T (envOracle_ok _)⟩

/-! ## The assembly theorem in this form -/

/-- The constraints the certificate puts on the oracle of a run. -/
def CertOk (c : Cert) (o : Oracle) : Prop :=
  (c.env = true → OracleOk o) ∧ (c.reads = true → EnvOk o)

/-- An oracle: what a per-run theorem extends with the tables of a run. -/
def anyOracle : Oracle := ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩

/-- **EVM IR to bytecode, run by run, for code with loops.** -/
theorem withinRun_of_checkL {p : Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : AssembleLoop.checkL p code c mx = true) (scope : Call → Prop) :
    WithinRun evmirSem (fun _ => p) code scope (CertOk c) := by
  have hok := table_ok anyOracle {}
  refine WithinRun.of_fixed (tableOracle (envOracle (ethOracle anyOracle)) {})
    ⟨fun _ => hok.1, fun _ => hok.2⟩ fun gas => ?_
  exact AssembleLoop.within_of_checkL hc _ (fun _ => hok.1) scope gas (fun _ => hok.2)

/-- Stages read backwards (every result of the later program is the earlier one's), for every
oracle meeting `Ok`, before a per-run refinement give a per-run refinement from the earlier program. -/
theorem WithinRun.of_back {A sem : Oracle → Sem} {q : ∀ o, (A o).Prog} {p : ∀ o, (sem o).Prog}
    {code : ByteArray} {scope : Call → Prop} {Ok : Oracle → Prop}
    (back : ∀ o, Ok o → Stage (sem o) (A o) (p o) (q o) scope)
    (h : WithinRun sem p code scope Ok) : WithinRun A q code scope Ok := by
  intro gas call hc
  obtain ⟨o, ho, hw⟩ := h gas call hc
  refine ⟨o, ho, fun call' h' obs hrun => ?_⟩
  subst h'
  rcases hw call' rfl obs hrun with e | e
  · exact Or.inl (back o ho call' hc obs e)
  · exact Or.inr e

/-- **The first lowered MIR to the exact bytecode, run by run**: the backend stages read backwards
and the assembly checker for code with loops give, for every gas and every call, an oracle meeting
the certificate's constraints under which every result of the bytecode is the first lowered MIR's
or a failure that changes nothing. -/
theorem withinRun_mir_of_checkL {stage0 : MIR.Lowered.moduleLayer.Prog} {p : Program}
    {code : ByteArray} {c : Cert} {mx : List Nat} {S scope : Call → Prop}
    (back : ∀ o, Certified EVM.Program.layer MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call) (hc : AssembleLoop.checkL p code c mx = true) :
    WithinRun mirSem (fun _ => stage0) code scope (CertOk c) :=
  WithinRun.of_back (fun o _ => fun call hcall obs h =>
      stage_of_certified (back o) call (hS call hcall) obs h)
    (withinRun_of_checkL hc scope)

/-- info: 'SolidCore.Refinement.Solar.RunOracle.holds_of_withinRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_withinRun

/-- info: 'SolidCore.Refinement.Solar.RunOracle.withinRun_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_of_checkL

/-- info: 'SolidCore.Refinement.Solar.RunOracle.withinRun_mir_of_checkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_mir_of_checkL

/-- info: 'SolidCore.Refinement.Solar.RunOracle.table_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms table_ok

end SolidCore.Refinement.Solar.RunOracle

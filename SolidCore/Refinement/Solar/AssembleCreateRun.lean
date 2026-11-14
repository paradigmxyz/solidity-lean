import SolidCore.Refinement.Solar.AssembleCreateCut

/-!
# Segments of a run with calls and creations read the same under every longer table

A run that makes CALLs and CREATE2s is read back segment by segment under the oracle of its two
tables, `createOracle (tableOracle base T) A`: the run's table `T` of GAS reads and message answers
(indexed by the messages a world sent) and the table `A` of its creations (indexed by the creations
a world made). `AssembleCut.Agree` bounds the worlds it compares by GAS reads and messages only, which
does not bound the creations; but between two cuts a segment never changes its world (every effect that
adds an event is a cut, `apply_world_eq`), so it reads only the world it starts in and the empty one
(`execC_agreeW`). Every extension of both tables answers there as they do (`createTable_agree`), so
every extension runs the segment to the same end (`exec_F`), which a segment proof of runs with
creations needs, as `AssembleCut.exec_O` is for `AssembleCut.seg`.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateRun

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.RunOracle
open SolidCore.Refinement.Solar.AssembleCreateSeg

/-- An effect that stops no segment leaves the world as it was. -/
theorem apply_world_eq {o : Oracle} {call : Call} {e : Effect} (he : cutEffect e = false)
    {args : List Word} {s s' : State} {r : Option Word}
    (h : Effect.apply o call e args s = some (r, s')) : s'.world = s.world := by
  unfold Effect.apply at h
  split at h <;> (try split at h) <;> simp_all [cutEffect]
  all_goals (obtain ⟨-, rfl⟩ := h; simp)

/-- An effect that stops no segment answers the same under oracles that agree at its world and the
empty one. -/
theorem apply_congrW {o1 o2 : Oracle} (hk : o1.keccak = o2.keccak) (hc : o1.caller = o2.caller)
    (h0 : ∀ name a, o1.env name [] a = o2.env name [] a) {call : Call} {e : Effect}
    (he : cutEffect e = false) {args : List Word} {s : State}
    (hw : ∀ name a, o1.env name s.world a = o2.env name s.world a) :
    Effect.apply o1 call e args s = Effect.apply o2 call e args s := by
  unfold Effect.apply
  split <;> simp_all [cutEffect, returndataSize, returndataByte, codeByte, immutableWord,
    immutableValue]

/-- **A segment runs the same under oracles that agree at its world** (and the empty one). -/
theorem execC_agreeW {o1 o2 : Oracle} (hk : o1.keccak = o2.keccak) (hc : o1.caller = o2.caller)
    (h0 : ∀ name a, o1.env name [] a = o2.env name [] a) (call : Call) (b : Nat) :
    ∀ (is : List Assemble.Instr) (S : List Word) (s : State),
      (∀ name a, o1.env name s.world a = o2.env name s.world a) →
      execC o1 call b is S s = execC o2 call b is S s
  | [], _, _, _ => rfl
  | .op op :: rest, S, s, hw => by
    by_cases hcut : cutOp op = true
    · simp only [execC, hcut, ite_true]
    have hcut' : cutOp op = false := by simpa using hcut
    have hctx : SolarTV.EVM.Program.context o1 call s = SolarTV.EVM.Program.context o2 call s := by
      simp [SolarTV.EVM.Program.context, hw]
    cases h : SolarTV.EVM.Program.stepOp (SolarTV.EVM.Program.context o2 call s) op S s.memory with
    | error _ => simp only [execC, hctx, h, hcut', Bool.false_eq_true, ite_false]
    | ok r =>
      obtain ⟨S', m⟩ := r
      simp only [execC, hctx, h, hcut', Bool.false_eq_true, ite_false]
      exact execC_agreeW hk hc h0 call b rest S' { s with memory := m } hw
  | .effect e a :: rest, S, s, hw => by
    by_cases hcut : cutEffect e = true
    · simp only [execC, hcut, ite_true]
    have he : cutEffect e = false := by simpa using hcut
    by_cases hl : S.length < a
    · simp only [execC, hcut, hl, Bool.false_eq_true, ite_false, ite_true]
    cases happ : Effect.apply o2 call e (S.take a) s with
    | none =>
      simp only [execC, hcut, hl, Bool.false_eq_true, ite_false, apply_congrW hk hc h0 he hw, happ]
    | some r =>
      obtain ⟨res, s1⟩ := r
      have hw1 : ∀ name a, o1.env name s1.world a = o2.env name s1.world a := by
        rw [apply_world_eq he happ]
        exact hw
      simp only [execC, hcut, hl, Bool.false_eq_true, ite_false, apply_congrW hk hc h0 he hw, happ]
      split_ifs
      · rfl
      · exact execC_agreeW hk hc h0 call b rest _ s1 hw1
  | .jump t :: rest, S, s, _ => by simp only [execC]
  | .jumpi t :: rest, S, s, hw => by
    cases S with
    | nil => simp only [execC]
    | cons x S =>
      simp only [execC]
      split_ifs
      · rfl
      · exact execC_agreeW hk hc h0 call b rest S s hw
      · rfl
  | .pushLabel t :: rest, S, s, hw => by
    simp only [execC]
    split_ifs
    · rfl
    · exact execC_agreeW hk hc h0 call b rest _ s hw
  | .jumpDyn :: rest, S, s, _ => rfl
  | .jumpiDyn :: rest, S, s, hw => by
    match S with
    | [] => rfl
    | [_] => rfl
    | x :: y :: S =>
      simp only [execC]
      split_ifs
      · exact execC_agreeW hk hc h0 call b rest S s hw
      · rfl
  | .jumpTable ts :: rest, S, s, _ => rfl
  | .stop :: rest, S, s, _ => rfl
  | .ret :: rest, S, s, _ => rfl
  | .revert :: rest, S, s, _ => rfl
  | .invalid :: rest, S, s, _ => rfl

/-- A world whose last message is a creation made one. -/
theorem creates_pos_of_lastCreate {w : List Event} (h : lastCreate w = true) : 0 < creates w := by
  cases hl : (w.filter Event.sends).getLast? with
  | none => simp [lastCreate, hl] at h
  | some e =>
    have hm : e ∈ w.filter Event.sends := by
      first
        | exact List.mem_of_getLast? hl
        | exact List.mem_of_getLast?_eq_some hl
        | exact List.getLast?_mem hl
    have hc : isCreateE e = true := by
      cases e <;> simp_all [lastCreate, isCreateE]
    unfold creates
    exact List.length_pos_of_mem (List.mem_filter.2 ⟨(List.mem_filter.1 hm).1, hc⟩)

/-- **The oracle of two tables and of any extensions of both agree** at every world with no more GAS
reads, messages and creations than the tables answer. -/
theorem createTable_agree (base : Oracle) {T T'' : RunTable} {A A'' : CreateTable} (hT : T.Le T'')
    (hA : A.Le A'') {w : List Event} (hg : gasReads w ≤ T.gases.length) (hs : sent w ≤ T.outs.length)
    (hc : creates w ≤ A.outs.length) (name : String) (a : List Word) :
    (createOracle (tableOracle base T) A).env name w a =
      (createOracle (tableOracle base T'') A'').env name w a := by
  have ht : ∀ name a, (tableOracle base T).env name w a = (tableOracle base T'').env name w a :=
    (table_agree base hT (ng := T.gases.length) (ns := T.outs.length) le_rfl le_rfl).2.2 w hg hs
  by_cases hl : lastCreate w = true
  · have hout : A.out w = A''.out w := by
      have := creates_pos_of_lastCreate hl
      unfold CreateTable.out
      exact (AssembleRun.getD_of_prefix hA.2.1 (by omega) _).symm
    simp only [createOracle, hl, ite_true, ↓reduceIte, hout, ht]
  · simp only [createOracle, hl, Bool.false_eq_true, ite_false, ↓reduceIte, ht]

/-- **Every extension of both tables runs a segment to the same end** as the tables do. -/
theorem exec_F {base : Oracle} {T T'' : RunTable} {A A'' : CreateTable} (hT : T.Le T'')
    (hA : A.Le A'') {call : Call} {b : Nat} {is : List Assemble.Instr} {S : List Word} {s : State}
    (hg : gasReads s.world ≤ T.gases.length) (hs : sent s.world ≤ T.outs.length)
    (hc : creates s.world ≤ A.outs.length) :
    SolarTV.EVM.Program.exec (createOracle (tableOracle base T'') A'') call b is S s =
      match execC (createOracle (tableOracle base T) A) call b is S s with
      | .done r => r
      | .cut i rest S' s' =>
        SolarTV.EVM.Program.exec (createOracle (tableOracle base T'') A'') call b (i :: rest) S' s' := by
  rw [exec_eq_execC, execC_agreeW (o1 := createOracle (tableOracle base T'') A'')
    (o2 := createOracle (tableOracle base T) A) rfl rfl
    (fun name a => (createTable_agree base hT hA (w := []) (by simp [gasReads]) (by simp [sent])
      (by simp [creates]) name a).symm) call b is S s
    (fun name a => (createTable_agree base hT hA hg hs hc name a).symm)]
  rfl

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRun.exec_F' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exec_F

/-! ## The oracle of a run with creations -/

/-- What the oracle of a run with creations answers that the run does not decide: the frame's code
(`AssembleCodeCopy.codeOracle`), EthLib's caller, hash and environment, and every other call fails. -/
def baseF (code : ByteArray) : Oracle := AssembleCodeCopy.codeOracle code base0

/-- **The oracle of a run with creations**: GAS reads and message answers from the run's table,
creations from the creation table, the frame's code and EthLib's caller, hash and environment. -/
abbrev FO (code : ByteArray) (T : RunTable) (A : CreateTable) : Oracle :=
  createOracle (tableOracle (baseF code) T) A

/-- It reads the frame's code, which `AssembleCreateSeg.codecopy_cut` needs. -/
theorem FO_codeOk (code : ByteArray) (T : RunTable) (A : CreateTable) :
    AssembleCodeCopy.CodeOk (FO code T A) code :=
  codeOk_createOracle A (codeOk_tableOracle T (AssembleCodeCopy.codeOracle_ok code base0))

/-- It meets what every certificate asks of an oracle. -/
theorem FO_ok (c : Cert) (code : ByteArray) (T : RunTable) (A : CreateTable) :
    CertOk c (FO code T A) := by
  refine ⟨fun _ => ethOracle_ok Witness.failOracle, fun _ => ?_⟩
  intro name byte w he world
  have hn : name ≠ "returndatasize" ∧ name ≠ "returndata" ∧ name ≠ "gas" ∧ name ≠ "code" := by
    unfold envRead at he
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at he)
  simp only [FO, baseF, createOracle, tableOracle, AssembleCodeCopy.codeOracle, hn.1, hn.2.1,
    hn.2.2.1, hn.2.2.2, false_and, ite_false, ite_self]
  exact envOracle_ok _ name byte w he world

/-- The `k`-th GAS read pushes the table's `k`-th gas. -/
theorem FO_gas (code : ByteArray) (T : RunTable) (A : CreateTable) (w : List Event) :
    (FO code T A).env "gas" (w ++ [.read "gas"]) [] = BitVec.ofNat 256 (T.gases.getD (gasReads w) 0) := by
  rw [← gas_table (baseF code) T w]
  simp [FO, createOracle]

/-- GAS under the oracle of tables whose next gas is `v`. -/
theorem exec_gasF {code : ByteArray} {T : RunTable} {A : CreateTable} {call : Call} {b : Nat}
    {rest : List Assemble.Instr} {S : List Word} {s : State} {v : Nat}
    (hT : T.gases.getD (gasReads s.world) 0 = v) (hS : S.length < 1024) :
    SolarTV.EVM.Program.exec (FO code T A) call b (.effect .gas 0 :: rest) S s =
      SolarTV.EVM.Program.exec (FO code T A) call b rest (BitVec.ofNat 256 v :: S)
        { s with world := s.world ++ [.read "gas"] } := by
  have happ : Effect.apply (FO code T A) call .gas [] s =
      some (some (BitVec.ofNat 256 v), { s with world := s.world ++ [.read "gas"] }) := by
    simp only [Effect.apply]
    rw [FO_gas, hT]
  simp [SolarTV.EVM.Program.exec, happ, show ¬ 1024 < S.length + 1 by omega]

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRun.FO_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FO_ok

/-! ## The tables of a run with creations, along its world -/

theorem sends_call (k : CallKind) (ops : List Word) (i : List Memory.Byte) (sto tr : Word → Word) :
    (List.filter Event.sends [Event.call k ops i sto tr]).length = 1 := rfl

theorem sends_create (ops : List Word) (c : List Memory.Byte) (sto tr : Word → Word) :
    (List.filter Event.sends [Event.create ops c sto tr]).length = 1 := rfl

/-- **The run's tables match its world**: one gas per GAS read, one entry of the run table per
message (calls and creations alike), one entry of the creation table per creation. -/
def TabF (T : RunTable) (A : CreateTable) (w : List Event) : Prop :=
  T.gases.length = gasReads w ∧ T.oks.length = sent w ∧ T.outs.length = sent w ∧
    T.stores.length = sent w ∧ T.transients.length = sent w ∧ A.addrs.length = creates w ∧
    A.outs.length = creates w ∧ A.stores.length = creates w

theorem TabF.log {T : RunTable} {A : CreateTable} {w : List Event} (h : TabF T A w)
    (t : List Word) (d : List Memory.Byte) : TabF T A (w ++ [.log t d]) := by
  simpa [TabF, gasReads, sent, Event.sends, Event.readsGas, List.filter_append] using h

/-- A GAS read adds the gas it pushed to the run table. -/
theorem TabF.gas {T : RunTable} {A : CreateTable} {w : List Event} (h : TabF T A w) (v : Nat) :
    TabF { T with gases := T.gases ++ [v] } A (w ++ [.read "gas"]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by simpa [sent, Event.sends, List.filter_append] using h2⟩
  simp [gasReads, Event.readsGas, List.filter_append] at h1 ⊢
  omega

/-- A CALL adds its entry to the run table. -/
theorem TabF.call {T : RunTable} {A : CreateTable} {w : List Event} (h : TabF T A w) (ok : Bool)
    (out : ByteArray) (sto : Word → Word) (k : CallKind) (ops : List Word) (i : List Memory.Byte)
    (sto' tr : Word → Word) :
    TabF (AssembleCallValueSeg.pushCall T ok out sto) A (w ++ [.call k ops i sto' tr]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hs : sent (w ++ [.call k ops i sto' tr]) = sent w + 1 := by
    simp only [sent, List.filter_append, List.length_append, sends_call]
  have hg : gasReads (w ++ [.call k ops i sto' tr]) = gasReads w := by
    simp [gasReads, Event.readsGas, List.filter_append]
  have hc : creates (w ++ [.call k ops i sto' tr]) = creates w := by
    simp [creates, isCreateE, List.filter_append]
  simp only [TabF, AssembleCallValueSeg.pushCall, List.length_append, List.length_singleton, hs, hg,
    hc]
  omega

/-- A CREATE2 adds its entry to the creation table, and one to the run table at its message, whose
transient storage after it is the only answer the oracle reads from there. -/
theorem TabF.create {T : RunTable} {A : CreateTable} {w : List Event} (h : TabF T A w) (r : Word)
    (out : ByteArray) (sto : Word → Word) (ops : List Word) (c : List Memory.Byte)
    (sto' tr : Word → Word) :
    TabF (AssembleCallValueSeg.pushCall T false .empty (fun _ => 0)) (A.push r out sto)
      (w ++ [.create ops c sto' tr]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hs : sent (w ++ [.create ops c sto' tr]) = sent w + 1 := by
    simp only [sent, List.filter_append, List.length_append, sends_create]
  have hg : gasReads (w ++ [.create ops c sto' tr]) = gasReads w := by
    simp [gasReads, Event.readsGas, List.filter_append]
  simp only [TabF, AssembleCallValueSeg.pushCall, CreateTable.push, List.length_append,
    List.length_singleton, hs, hg, creates_create]
  omega

/-- Every extension of a run table answers the transient storage after a message the table holds
as the table does. -/
theorem table_transient {base : Oracle} {T1 T'' : RunTable} (hle : T1.Le T'') {w : List Event}
    (hw : sent w ≤ T1.transients.length) :
    (tableOracle base T'').transientAfter w = (tableOracle base T1).transientAfter w := by
  simp only [tableOracle]
  split_ifs with h
  · rfl
  · exact AssembleRun.getD_of_prefix hle.2.2.2.1 (by omega) _

/-- **SolarTV's CREATE2 reads the run table only for the transient storage after it**, so every
extension of a run table holding the creation's message answers it as that table does. -/
theorem create2_table {base : Oracle} {T1 T'' : RunTable} (hle : T1.Le T'') {A : CreateTable}
    {call : Call} {s : State} {value start size salt : Word}
    (hsent : sent s.world < T1.transients.length) (hA : creates s.world < A.stores.length) :
    Effect.apply (createOracle (tableOracle base T'') A) call .create2 [value, start, size, salt] s =
      Effect.apply (createOracle (tableOracle base T1) A) call .create2 [value, start, size, salt] s := by
  have key := table_transient (base := base) hle (w := s.world ++ [.create [value, salt]
    ((s.memory.expand start.toNat size.toNat).read start.toNat size.toNat) s.storage s.transient])
    (by simp only [sent, List.filter_append, List.length_append, sends_create] at hsent ⊢; omega)
  have key2 : ∀ d1 d2 : Word → Word, A.stores.getD (creates s.world) d1 =
      A.stores.getD (creates s.world) d2 := fun d1 d2 => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hA]
  simp only [Effect.apply, created, createOracle, lastCreate_create, ite_true, ↓reduceIte, key,
    creates_create, Nat.add_sub_cancel, Option.some.injEq, Prod.mk.injEq, State.mk.injEq, true_and,
    and_true]
  exact key2 _ _

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateRun.create2_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2_table

end SolidCore.Refinement.Solar.AssembleCreateRun

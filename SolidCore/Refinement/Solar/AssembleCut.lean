import SolidCore.Refinement.Solar.AssembleCutSim
import SolidCore.Refinement.Solar.AssembleDyn
import SolidCore.Refinement.Solar.AssembleDynCopy
import SolidCore.Refinement.Solar.AssembleRunLoop
import SolidCore.Refinement.Solar.RunOracleSource

/-!
# EVM IR to bytecode with GAS, at the run's own gas

`AssembleRunLoop.withinRun_of_checkL_atGas` runs each block with gas to spare and moves it back to the
frame's own gas (`Logic.reaches_low`). GAS pushes the gas left, which no run with more gas shows, so a
block with GAS runs in segments (`AssembleLoop.exec_simC`): each segment up to a GAS with gas to spare
for it alone, moved back to the frame's gas, then GAS at the frame's own gas (`gas_back`: a run that
succeeds had the gas for it), with the gas it pushes added to the run's table (`RunTable.gases`). The
oracle of a table answers what a segment reads as every oracle of a longer table does
(`execC_agree`), so every extension of the table runs the block to the same end, which
`AssembleRun.within_of_advances` needs.

`withinRun_of_checkC` is the per-run theorem (`RunOracle.WithinRun`) for every program the checker with
GAS (`checkC`) accepts.
-/

namespace SolidCore.Refinement.Solar.AssembleCut

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-! ## Oracles that agree before a GAS read or a message -/

/-- Two oracles answer the same at every world with at most `ng` GAS reads and `ns` messages. -/
def Agree (o1 o2 : Oracle) (ng ns : Nat) : Prop :=
  o1.keccak = o2.keccak ∧ o1.caller = o2.caller ∧
    ∀ w, gasReads w ≤ ng → sent w ≤ ns → ∀ name a, o1.env name w a = o2.env name w a

theorem Agree.refl (o : Oracle) (ng ns : Nat) : Agree o o ng ns :=
  ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩

/-- The oracle of a table and of any extension agree at the worlds the table answers. -/
theorem table_agree (base : Oracle) {T T2 : RunTable} (hle : T.Le T2) {ng ns : Nat}
    (hg : ng ≤ T.gases.length) (hs : ns ≤ T.outs.length) :
    Agree (tableOracle base T) (tableOracle base T2) ng ns := by
  refine ⟨rfl, rfl, fun w hw hsw name a => ?_⟩
  have hout : T.out w = T2.out w := by
    unfold RunTable.out
    split
    · rfl
    · exact (getD_of_prefix hle.2.1 (by omega) _).symm
  have hgas : gasReads w ≠ 0 →
      T.gases.getD (gasReads w - 1) 0 = T2.gases.getD (gasReads w - 1) 0 := fun h =>
    (getD_of_prefix hle.2.2.2.2 (by omega) _).symm
  simp only [tableOracle, hout]
  split_ifs <;> simp_all

/-- An effect that stops no segment answers the same under oracles that agree. -/
theorem apply_congr {o1 o2 : Oracle} {ng ns : Nat} (hA : Agree o1 o2 ng ns) {call : Call}
    {e : Effect} (he : cutEffect e = false) {args : List Word} {s : State}
    (hg : gasReads s.world ≤ ng) (hs : sent s.world ≤ ns) :
    Effect.apply o1 call e args s = Effect.apply o2 call e args s := by
  have hw := hA.2.2 s.world hg hs
  have h0 := hA.2.2 [] (by simp [gasReads]) (by simp [sent])
  obtain ⟨hk, hc, -⟩ := hA
  unfold Effect.apply
  split <;> simp_all [cutEffect, returndataSize, returndataByte, codeByte, immutableWord,
    immutableValue]

/-- An effect that stops no segment adds no GAS read and sends no message. -/
theorem apply_world {o : Oracle} {call : Call} {e : Effect} (he : cutEffect e = false)
    {args : List Word} {s s' : State} {r : Option Word}
    (h : Effect.apply o call e args s = some (r, s')) :
    gasReads s'.world = gasReads s.world ∧ sent s'.world = sent s.world := by
  unfold Effect.apply at h
  split at h <;> (try split at h) <;> simp_all [cutEffect]
  all_goals (obtain ⟨-, rfl⟩ := h; simp)

/-- The state a segment ends in, when it does not halt. -/
def endState : CRes → Option State
  | .cut _ _ _ s' => some s'
  | .done (.inr (_, _, s')) => some s'
  | .done (.inl _) => none

/-- A segment adds no GAS read and sends no message, and stops, if at all, inside its instructions. -/
def Kept (r : CRes) (n : Nat) (s : State) : Prop :=
  (∀ s', endState r = some s' →
    gasReads s'.world = gasReads s.world ∧ sent s'.world = sent s.world) ∧
  ∀ i rest S' s', r = .cut i rest S' s' → rest.length < n

theorem Kept.trans {r : CRes} {n n' : Nat} {s s1 : State} (h : Kept r n s1)
    (h1 : gasReads s1.world = gasReads s.world ∧ sent s1.world = sent s.world) (hn : n ≤ n') :
    Kept r n' s :=
  ⟨fun s' hs => ⟨(h.1 s' hs).1.trans h1.1, (h.1 s' hs).2.trans h1.2⟩,
    fun i rest S' s' hr => Nat.lt_of_lt_of_le (h.2 i rest S' s' hr) hn⟩

theorem Kept.halt {r : (Halt × State)} {n : Nat} {s : State} : Kept (.done (.inl r)) n s :=
  ⟨fun s' h => by simp [endState] at h, fun _ _ _ _ h => by cases h⟩

theorem Kept.next {t : Nat} {S : List Word} {n : Nat} {s : State} : Kept (.done (.inr (t, S, s))) n s :=
  ⟨fun s' h => by simp [endState] at h; subst h; exact ⟨by trivial, rfl⟩, fun _ _ _ _ h => by cases h⟩

/-- **A segment runs the same under oracles that agree**, and adds no GAS read or message. -/
theorem execC_agree {o1 o2 : Oracle} {ng ns : Nat} (hA : Agree o1 o2 ng ns) (call : Call) (b : Nat) :
    ∀ (is : List Assemble.Instr) (S : List Word) (s : State), gasReads s.world ≤ ng →
      sent s.world ≤ ns →
      execC o1 call b is S s = execC o2 call b is S s ∧ Kept (execC o1 call b is S s) is.length s
  | [], _, s, _, _ => ⟨rfl, Kept.next⟩
  | .op op :: rest, S, s, hg, hs => by
    by_cases hcut : cutOp op = true
    · simp only [execC, hcut, ite_true]
      exact ⟨by trivial, fun s' h => by simp [endState] at h; subst h; exact ⟨rfl, rfl⟩,
        fun _ _ _ _ h => by cases h; simp⟩
    have hcut' : cutOp op = false := by simpa using hcut
    have hc : SolarTV.EVM.Program.context o1 call s = SolarTV.EVM.Program.context o2 call s := by
      simp [SolarTV.EVM.Program.context, hA.2.2 s.world hg hs]
    cases h : SolarTV.EVM.Program.stepOp (SolarTV.EVM.Program.context o2 call s) op S s.memory with
    | error _ =>
      simp only [execC, hc, h, hcut', Bool.false_eq_true, ite_false]
      exact ⟨by trivial, Kept.halt⟩
    | ok r =>
      obtain ⟨S', m⟩ := r
      simp only [execC, hc, h, hcut', Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2⟩ := execC_agree hA call b rest S' { s with memory := m } hg hs
      exact ⟨h1, h2.trans ⟨rfl, rfl⟩ (by simp)⟩
  | .effect e a :: rest, S, s, hg, hs => by
    by_cases hc : cutEffect e = true
    · simp only [execC, hc, ite_true]
      exact ⟨by trivial, fun s' h => by simp [endState] at h; subst h; exact ⟨rfl, rfl⟩,
        fun _ _ _ _ h => by cases h; simp⟩
    · have he : cutEffect e = false := by simpa using hc
      by_cases hl : S.length < a
      · simp only [execC, hc, hl, Bool.false_eq_true, ite_false, ite_true]
        exact ⟨by trivial, Kept.halt⟩
      · cases happ : Effect.apply o2 call e (S.take a) s with
        | none =>
          simp only [execC, hc, hl, Bool.false_eq_true, ite_false, apply_congr hA he hg hs, happ]
          exact ⟨by trivial, Kept.halt⟩
        | some r =>
          obtain ⟨res, s1⟩ := r
          have hw := apply_world he happ
          simp only [execC, hc, hl, Bool.false_eq_true, ite_false, apply_congr hA he hg hs, happ]
          split_ifs
          · exact ⟨by trivial, Kept.halt⟩
          · obtain ⟨h1, h2⟩ := execC_agree hA call b rest _ s1 (by omega) (by omega)
            exact ⟨h1, h2.trans hw (by simp)⟩
  | .jump t :: rest, S, s, hg, hs => by
    simp only [execC]
    split_ifs
    · exact ⟨by trivial, Kept.halt⟩
    · exact ⟨by trivial, Kept.next⟩
  | .jumpi t :: rest, S, s, hg, hs => by
    cases S with
    | nil =>
      simp only [execC]
      split_ifs <;> exact ⟨by trivial, Kept.halt⟩
    | cons x S =>
      simp only [execC]
      split_ifs
      · exact ⟨by trivial, Kept.halt⟩
      · obtain ⟨h1, h2⟩ := execC_agree hA call b rest S s hg hs
        exact ⟨h1, h2.trans ⟨rfl, rfl⟩ (by simp)⟩
      · exact ⟨by trivial, Kept.next⟩
  | .pushLabel t :: rest, S, s, hg, hs => by
    simp only [execC]
    split_ifs
    · exact ⟨by trivial, Kept.halt⟩
    · obtain ⟨h1, h2⟩ := execC_agree hA call b rest _ s hg hs
      exact ⟨h1, h2.trans ⟨rfl, rfl⟩ (by simp)⟩
  | .jumpDyn :: rest, S, s, hg, hs => by
    cases S with
    | nil => exact ⟨by trivial, Kept.halt⟩
    | cons x S => exact ⟨by trivial, Kept.next⟩
  | .jumpiDyn :: rest, S, s, hg, hs => by
    match S with
    | [] => exact ⟨by trivial, Kept.halt⟩
    | [_] => exact ⟨by trivial, Kept.halt⟩
    | x :: y :: S =>
      simp only [execC]
      split_ifs
      · obtain ⟨h1, h2⟩ := execC_agree hA call b rest S s hg hs
        exact ⟨h1, h2.trans ⟨rfl, rfl⟩ (by simp)⟩
      · exact ⟨by trivial, Kept.next⟩
  | .jumpTable ts :: rest, S, s, hg, hs => by
    cases S with
    | nil => exact ⟨by trivial, Kept.halt⟩
    | cons x S =>
      cases h : ts[x.toNat]? with
      | none => simp only [execC, h]; exact ⟨by trivial, Kept.halt⟩
      | some t => simp only [execC, h]; exact ⟨by trivial, Kept.next⟩
  | .stop :: rest, S, s, _, _ => ⟨rfl, Kept.halt⟩
  | .ret :: rest, S, s, _, _ => ⟨rfl, fun s' h => by simp [endState, execC] at h; subst h; exact ⟨rfl, rfl⟩,
    fun _ _ _ _ h => by simp only [execC, CRes.cut.injEq] at h; obtain ⟨-, rfl, -, -⟩ := h; simp⟩
  | .revert :: rest, S, s, _, _ => ⟨rfl, fun s' h => by simp [endState, execC] at h; subst h; exact ⟨rfl, rfl⟩,
    fun _ _ _ _ h => by simp only [execC, CRes.cut.injEq] at h; obtain ⟨-, rfl, -, -⟩ := h; simp⟩
  | .invalid :: rest, S, s, _, _ => ⟨rfl, Kept.halt⟩

/-! ## GAS at the frame's own gas -/

/-- **GAS in a run that succeeds**: the frame had the gas for it, and the run goes on from the frame
after it, with the gas left after its price pushed. -/
theorem gas_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {evm : Evm .fusaka Nat} (hat : At code msg pc T M g st ss rd evm) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5a) (hstack : T.length < STACK_LIMIT) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    2 ≤ g ∧ ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) (BitVec.ofNat 256 (g - 2) :: T) M (g - 2) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  by_cases hg : 2 ≤ g
  · obtain ⟨m, hr, hm⟩ := Logic.gas_rule (fork := .fusaka) hlt hbyte hg hstack evm hat
    have := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq hr within
    rw [this] at hrun
    exact ⟨hg, m, _, hm, hrun⟩
  · exfalso
    have hspec : Spec .fusaka (At code msg pc T M g st ss rd) (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, -, hgas, -⟩ := hat'
      subst hcode hpc
      have decoded : Op.ofByte .fusaka e.code[e.pc] = some .gas := by
        rw [hbyte]
        exact ofByte_of_decode rfl (Fork.frontier_le _)
      rw [step_of_instruction hlt decoded rfl]
      simp [readFrame, chargeGas, GasMeter.charge, hgas, OPCODE_GAS, BASE, show g < 2 by omega, bind, Except.bind]
    obtain ⟨z, hr, hstop, hf⟩ := hspec evm hat
    rw [runFrame_of_reaches hr hstop within] at hrun
    cases hrun
    rw [hf.2.1] at hok
    cases hok

/-! ## The oracle of a run -/

/-- The oracle of a run of code that sends no message: `base` with the gas each GAS read pushed, in
order (the table's `gases`); every other read is `base`'s. -/
def gasOracle (base : Oracle) (T : RunTable) : Oracle :=
  { base with
    env := fun name w args =>
      if name = "gas" ∧ args = [] ∧ gasReads w ≠ 0 then
        BitVec.ofNat 256 (T.gases.getD (gasReads w - 1) 0)
      else base.env name w args }

/-- The `k`-th GAS read pushes the table's `k`-th gas. -/
theorem gasOracle_gas (base : Oracle) (T : RunTable) (w : List Event) :
    (gasOracle base T).env "gas" (w ++ [.read "gas"]) [] =
      BitVec.ofNat 256 (T.gases.getD (gasReads w) 0) := by
  simp [gasOracle]

/-- The gas oracle of a table and of any extension agree at the worlds the table answers. -/
theorem gas_agree (base : Oracle) {T T2 : RunTable} (hle : T.Le T2) {ng ns : Nat}
    (hg : ng ≤ T.gases.length) : Agree (gasOracle base T) (gasOracle base T2) ng ns := by
  refine ⟨rfl, rfl, fun w hw _ name a => ?_⟩
  have hgas : gasReads w ≠ 0 →
      T.gases.getD (gasReads w - 1) 0 = T2.gases.getD (gasReads w - 1) 0 := fun h =>
    (getD_of_prefix hle.2.2.2.2 (by omega) _).symm
  simp only [gasOracle]
  split_ifs with h
  · rw [hgas h.2.2]
  · rfl

/-- The gas oracle keeps every read but GAS: the code sizes, the return data and the results and
storage of calls stay the open world's. -/
theorem callsAgree_gas {o : Oracle} {W : World} (T : RunTable) (h : CallsAgree o W) :
    CallsAgree (gasOracle o T) W := by
  have henv : ∀ n w a, n ≠ "gas" → (gasOracle o T).env n w a = o.env n w a := by
    intro n w a hn
    simp [gasOracle, hn]
  have hcodes : ∀ w code, CodesAgree (gasOracle o T) w code ↔ CodesAgree o w code := by
    intro w code
    unfold CodesAgree
    simp only [henv "extcodesize" _ _ (by decide)]
  have hsize : ∀ w, returndataSize (gasOracle o T) w = returndataSize o w := fun w =>
    henv "returndatasize" w [] (by decide)
  have hbyte : ∀ w j, returndataByte (gasOracle o T) w j = returndataByte o w j := by
    intro w j
    unfold returndataByte
    rw [henv "returndata" w _ (by decide)]
  refine ⟨fun w hw => (hcodes _ _).2 (h.codes w hw), ?_, h.static⟩
  intro hh world req a ha w k s i st tr hl hm hst hcod
  obtain ⟨h1, h2, h3⟩ := h.calls hh world req a ha w k s i st tr hl hm hst ((hcodes _ _).1 hcod)
  refine ⟨h1, h2, fun rest hr => ?_⟩
  obtain ⟨r1, r2, r3⟩ := h3 rest hr
  exact ⟨by rw [hsize]; exact r1, fun j hj hj' => by rw [hbyte]; exact r2 j hj hj',
    (hcodes _ _).2 r3⟩

/-- What the oracle of a run answers that the run does not decide: every call fails, as the
open world `Witness.failWorld` answers, with EthLib's caller, hash and environment. -/
def base0 : Oracle := envOracle (ethOracle Witness.failOracle)

/-- The oracle of a run's table. -/
abbrev O (T : RunTable) : Oracle := gasOracle base0 T

theorem O_ok (c : Cert) (T : RunTable) : CertOk c (O T) := by
  refine ⟨fun _ => ethOracle_ok Witness.failOracle, fun _ => ?_⟩
  intro name byte w he world
  have hn : name ≠ "gas" := by
    unfold envRead at he
    rintro rfl
    simp at he
  simp only [O, gasOracle, hn, false_and, ite_false]
  exact envOracle_ok _ name byte w he world

/-- The oracle of every table agrees with an open world, so the composition with the source's
specification (`SourceOracle.holds_of_runs`) applies to it. -/
theorem O_agree (T : RunTable) : ∃ W : World, W.Open ∧ CallsAgree (O T) W :=
  ⟨Witness.failWorld, Witness.failWorld_open, callsAgree_gas T (callsAgree_envEth Witness.failAgree)⟩

/-- Under every extension of the table, a block runs as its segment under the table does, then
from the instruction the segment stopped at. -/
theorem exec_O {T T'' : RunTable} (hle : T.Le T'') {call : Call} {b : Nat}
    {is : List Assemble.Instr} {S : List Word} {s : State}
    (hg : gasReads s.world ≤ T.gases.length) (hs : sent s.world = 0) :
    SolarTV.EVM.Program.exec (O T'') call b is S s = match execC (O T) call b is S s with
      | .done r => r
      | .cut i rest S' s' => SolarTV.EVM.Program.exec (O T'') call b (i :: rest) S' s' := by
  rw [exec_eq_execC, ← (execC_agree (gas_agree base0 hle (ng := T.gases.length) (ns := 0) le_rfl)
    call b is S s hg (by omega)).1]
  rfl

/-- GAS under the oracle of a table whose next gas is `v`. -/
theorem exec_gas {T : RunTable} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {S : List Word} {s : State} {v : Nat} (hT : T.gases.getD (gasReads s.world) 0 = v)
    (hS : S.length < 1024) :
    SolarTV.EVM.Program.exec (O T) call b (.effect .gas 0 :: rest) S s =
      SolarTV.EVM.Program.exec (O T) call b rest (BitVec.ofNat 256 v :: S)
        { s with world := s.world ++ [.read "gas"] } := by
  have happ : Effect.apply (O T) call .gas [] s =
      some (some (BitVec.ofNat 256 v), { s with world := s.world ++ [.read "gas"] }) := by
    simp only [Effect.apply]
    rw [gasOracle_gas, hT]
  simp [SolarTV.EVM.Program.exec, happ, show ¬ 1024 < S.length + 1 by omega]

theorem lowerInstrs_gas (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .gas 0 :: rest) = .op 0x5a :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem blockOkC_gas {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .gas 0 :: rest) = true) :
    1 ≤ k ∧ blockOkC p c mx b (h + 1) [] (some false :: ty) (k - 1) rest = true := by
  simpa [blockOkC, turnedElse, dropped, isGasI] using hok

theorem isLoadI_eq {i : Assemble.Instr} (h : isLoadI i = true) : i = .op .load := by
  unfold isLoadI at h
  split at h
  · rfl
  · cases h

theorem isStoreI_eq {i : Assemble.Instr} (h : isStoreI i = true) : i = .op .store := by
  unfold isStoreI at h
  split at h
  · rfl
  · cases h

theorem lowerInstrs_load (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.op .load :: rest) = .op 0x51 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem lowerInstrs_store (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.op .store :: rest) = .op 0x52 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem blockOkC_load {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.op .load :: rest) = true) :
    1 ≤ k ∧ 1 ≤ h ∧ isData ty 1 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b h [] (some false :: ty.drop 1) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem blockOkC_store {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.op .store :: rest) = true) :
    1 ≤ k ∧ 2 ≤ h ∧ isData ty 2 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 2) [] (ty.drop 2) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, Bool.and_eq_true,
    decide_eq_true_eq, Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem isRetI_eq {i : Assemble.Instr} (h : isRetI i = true) : i = .ret := by
  unfold isRetI at h
  split at h
  · rfl
  · cases h

theorem isRevI_eq {i : Assemble.Instr} (h : isRevI i = true) : i = .revert := by
  unfold isRevI at h
  split at h
  · rfl
  · cases h

theorem lowerInstrs_ret (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.ret :: rest) = .op 0xf3 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem lowerInstrs_revert (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.revert :: rest) = .op 0xfd :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem blockOkC_ret {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.ret :: rest) = true) : 2 ≤ h ∧ isData ty 2 = true := by
  simpa [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI] using hok

theorem blockOkC_revert {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.revert :: rest) = true) :
    2 ≤ h ∧ isData ty 2 = true := by
  simpa [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI] using hok

theorem isKecI_eq {i : Assemble.Instr} (h : isKecI i = true) : i = .effect .keccak256 2 := by
  unfold isKecI at h
  split at h
  · rfl
  · cases h

theorem lowerInstrs_kec (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .keccak256 2 :: rest) = .op 0x20 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem blockOkC_kec {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .keccak256 2 :: rest) = true) :
    c.env = true ∧ 1 ≤ k ∧ 2 ≤ h ∧ isData ty 2 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 1) [] (some false :: ty.drop 2) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, ite_false,
    ite_true] at hok
  exact ⟨hok.1.1.1.1.1, hok.1.1.1.1.2, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem isLogI_eq {i : Assemble.Instr} (h : isLogI i = true) :
    ∃ n, n ≤ 4 ∧ i = .effect (.log n) (n + 2) := by
  unfold isLogI at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨_, h1, rfl⟩
  · cases h

theorem lowerInstrs_log (p : Assemble.Program) (c : Cert) (b : Nat) {n : Nat} (hn : n ≤ 4)
    (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect (.log n) (n + 2) :: rest) =
      .op (0xa0 + n) :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr, hn]

theorem blockOkC_log {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h n : Nat} (hn : n ≤ 4)
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect (.log n) (n + 2) :: rest) = true) :
    1 ≤ k ∧ n + 2 ≤ h ∧ isData ty (n + 2) = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - (n + 2)) [] (ty.drop (n + 2)) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, hn, decide_true, Bool.true_and, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem gasReads_log (w : List Event) (t : List Word) (d : List SolarTV.Memory.Byte) :
    gasReads (w ++ [.log t d]) = gasReads w := by
  simp [gasReads, Event.readsGas]

theorem sent_log (w : List Event) (t : List Word) (d : List SolarTV.Memory.Byte) :
    sent (w ++ [.log t d]) = sent w := by
  simp [sent, Event.sends]

theorem isCdcI_eq {i : Assemble.Instr} (h : isCdcI i = true) : i = .effect .calldatacopy 3 := by
  unfold isCdcI at h
  split at h
  · rfl
  · cases h

theorem lowerInstrs_cdc (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .calldatacopy 3 :: rest) = .op 0x37 :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem blockOkC_cdc {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .calldatacopy 3 :: rest) = true) :
    1 ≤ k ∧ 3 ≤ h ∧ isData ty 3 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 3) [] (ty.drop 3) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
    ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem isScI_eq {i : Assemble.Instr} (h : isScI i = true) : i = .effect (.call .staticcall) 6 := by
  unfold isScI at h
  split at h
  · rfl
  · cases h

/-- The checker cuts at a STATICCALL only in a program whose certificate says it makes calls. -/
theorem blockOkC_sc {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect (.call .staticcall) 6 :: rest) = true) :
    c.calls = true ∧ 1 ≤ k ∧ 6 ≤ h ∧ isData ty 6 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 5) [] (some false :: ty.drop 6) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
    ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1.1.1, hok.1.1.1.1.2, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

theorem isRdsI_eq {i : Assemble.Instr} (h : isRdsI i = true) : i = .effect .returndatasize 0 := by
  unfold isRdsI at h
  split at h
  · rfl
  · cases h

/-- The checker cuts at a RETURNDATASIZE only in a program whose certificate says it makes calls. -/
theorem blockOkC_rds {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .returndatasize 0 :: rest) = true) :
    c.calls = true ∧ 1 ≤ k ∧ blockOkC p c mx b (h + 1) [] (some false :: ty) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, isRdsI, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1, hok.1.2, hok.2⟩

theorem isRdcI_eq {i : Assemble.Instr} (h : isRdcI i = true) : i = .effect .returndatacopy 3 := by
  unfold isRdcI at h
  split at h
  · rfl
  · cases h

/-- The checker cuts at a RETURNDATACOPY only in a program whose certificate says it makes calls. -/
theorem blockOkC_rdc {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .returndatacopy 3 :: rest) = true) :
    c.calls = true ∧ 1 ≤ k ∧ 3 ≤ h ∧ isData ty 3 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 3) [] (ty.drop 3) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, isRdsI, isRdcI, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq,
    Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1.1, hok.1.1.1.1.2, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

/-- A program that creates makes no STATICCALL the checker accepts. (It may read the return data of
its CALLs and CREATE2s: RETURNDATASIZE and RETURNDATACOPY, which `AssembleCreateSegF.segF` reads
back from the run's tables.) -/
theorem blockOkC_noSc_creates {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {i : Assemble.Instr} {rest : List Assemble.Instr}
    (hi : isScI i = true)
    (hok : blockOkC p c mx b h known ty k (i :: rest) = true) : c.creates = false := by
  obtain rfl := isScI_eq hi
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
    ite_false, ite_true] at hok
  simpa using hok.1.1.1.1.1.2

theorem isCallI_eq {i : Assemble.Instr} (h : isCallI i = true) : i = .effect (.call .call) 7 := by
  unfold isCallI at h
  split at h
  · rfl
  · cases h

theorem isC2I_eq {i : Assemble.Instr} (h : isC2I i = true) : i = .effect .create2 4 := by
  unfold isC2I at h
  split at h
  · rfl
  · cases h

theorem isCcI_eq {i : Assemble.Instr} (h : isCcI i = true) : i = .effect .codecopy 3 := by
  unfold isCcI at h
  split at h
  · rfl
  · cases h

/-- The checker cuts at a CALL only in a program whose certificate says it makes calls and
creates. -/
theorem blockOkC_call {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect (.call .call) 7 :: rest) = true) :
    c.calls = true ∧ c.creates = true ∧ 1 ≤ k ∧ 7 ≤ h ∧ isData ty 7 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 6) [] (some false :: ty.drop 7) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, isRdsI, isRdcI, isCallI, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq, Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1.1.1, hok.1.1.1.1.1.2, hok.1.1.1.1.2, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

/-- The checker cuts at a CREATE2 only in a program whose certificate says it makes calls and
creates. -/
theorem blockOkC_c2 {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .create2 4 :: rest) = true) :
    c.calls = true ∧ c.creates = true ∧ 1 ≤ k ∧ 4 ≤ h ∧ isData ty 4 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 3) [] (some false :: ty.drop 4) (k - 1) rest = true := by
  simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
    isLogI, isCdcI, isScI, isRdsI, isRdcI, isCallI, isC2I, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq, Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1.1.1, hok.1.1.1.1.1.2, hok.1.1.1.1.2, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

/-- The checker cuts at a CODECOPY only in a program whose certificate says it makes calls and
creates, and only with its code offset known, below 2 ^ 32. -/
theorem blockOkC_cc {p : Assemble.Program} {c : Cert} {mx : List Nat} {b h : Nat}
    {known : Known} {ty : List Ty} {k : Nat} {rest : List Assemble.Instr}
    (hok : blockOkC p c mx b h known ty k (.effect .codecopy 3 :: rest) = true) :
    c.calls = true ∧ c.creates = true ∧ (∃ x off t, known = x :: some off :: t ∧ off.toNat < 2 ^ 32) ∧
      1 ≤ k ∧ 3 ≤ h ∧ isData ty 3 = true ∧ 2 ^ 140 ≤ c.top ∧
      blockOkC p c mx b (h - 3) [] (ty.drop 3) (k - 1) rest = true := by
  rcases known with _ | ⟨x, _ | ⟨_ | off, t⟩⟩ <;>
    simp only [blockOkC, turnedElse, dropped, isGasI, isLoadI, isStoreI, isRetI, isRevI, isKecI,
      isLogI, isCdcI, isScI, isRdsI, isRdcI, isCallI, isC2I, isCcI, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq, Bool.false_eq_true, ite_false, ite_true] at hok
  exact ⟨hok.1.1.1.1.1.1.1, hok.1.1.1.1.1.1.2, ⟨x, off, t, rfl, hok.1.1.1.1.1.2⟩, hok.1.1.1.1.2,
    hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩

/-! ## A block, segment by segment -/

/-- `AssembleRunLoop.Ent` with any return data in the frame: the relation at a block entry once
the frame may hold the output of a message it sent. -/
def EntC (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray) (msg : Message .fusaka)
    (ss0 : Substate) (x : Nat × List Word × Machine.State) (evm : Evm .fusaka Nat) : Prop :=
  ∃ (Tw : List Word) (pc : Nat) (M : ByteArray) (st : State.TransactionState) (ss : Substate)
    (rd : ByteArray),
    x.1 ≤ p.blocks.length ∧
    (x.1 < p.blocks.length → c.need x.1 ≤ x.2.1.length ∧ x.2.1.length ≤ maxH mx x.1) ∧
    SR c (c.entry x.1) x.2.1 Tw ∧
    Seg (bytesOf code) c.offset pc (lowerFrom p c x.1 (p.blocks.drop x.1)) code.size ∧
    M.size ≤ c.top ∧ MemRel x.2.2.memory M ∧ Rel msg ss0 st ss x.2.2 ∧
    At code msg pc Tw M evm.gas st ss rd evm

/-- `AssembleRunLoop.at_of_addGas` with any return data. -/
theorem at_of_addGasR {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {G : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray} {K : Nat}
    {m : Evm .fusaka Nat} (h : At code msg pc T M G st ss rd (addGas K m)) :
    At code msg pc T M m.gas st ss rd m ∧ m.gas + K = G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, rfl, h8, h9, h10, h11, h12, h13⟩, by simpa using h7⟩

/-- **The rest of a block from an instruction, read back from a run that succeeds**: the segments
up to each GAS with gas to spare, moved back to the frame's gas, and each GAS at the frame's gas,
its gas added to the table. Every extension of the table it ends with runs the rest of the block to
the same end: a halt the frame shows, or the next block, related to a frame the run goes on from. -/
theorem seg {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobT p c code) (hnc : c.calls = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    {b : Nat} (hb : b < p.blocks.length) {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {fin : Evm .fusaka Nat} (hok : fin.error = none) {G0 : Nat} (hG0 : G0 < 2 ^ 256)
    {rd : ByteArray} :
    ∀ (n : Nat) (is : List Assemble.Instr) (h : Nat) (known : Known) (ty : List Ty) (k : Nat)
      (S Tw : List Word) (s : State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate) (T : RunTable) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound),
      is.length < n → blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → KR known S → SR c ty S Tw →
      Seg (bytesOf code) c.offset pc
        (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size →
      S.length + k ≤ 1000 → M.size ≤ c.top → MemRel s.memory M → Rel msg ss0 st ss s →
      At code msg pc Tw M g st ss rd evm → T.gases.length = gasReads s.world →
      sent s.world = 0 → MemBudget G0 M g →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      ∃ T' r, T.Le T' ∧
        (∀ T'', T'.Le T'' → SolarTV.EVM.Program.exec (O T'') call b is S s = r) ∧
        (∀ res, r = .inl res → PostL call msg.currentTarget ss0 res.2 res.1 fin) ∧
        (∀ y, r = .inr y → (y.1 ≤ p.blocks.length ∧
          (y.1 < p.blocks.length → c.need y.1 ≤ y.2.1.length ∧ y.2.1.length ≤ maxH mx y.1) ∧
          (y.1 = b + 1 ∨ isTarget p c y.1 = true)) ∧
          ∃ (after : Evm .fusaka Nat) (within' : GasMeter.gasHeld after.gas ≤ bound),
            EntC p c mx code msg ss0 y after ∧ T'.gases.length = gasReads y.2.2.world ∧
            sent y.2.2.world = 0 ∧ after.gas ≤ g ∧
            memoryGasCost after.memory.size + after.gas ≤ G0 ∧
            runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, is, h, known, ty, k, S, Tw, s, pc, M, g, st, ss, T, evm, within, hn, hokC, hh, hu, hk,
      hR, hseg, hstk, htop, hmem, R, hat, hTg, hs0, hB, hrun => by
    have hge : evm.gas = g := hat.2.2.2.2.2.2.1
    -- The segment with gas to spare for it alone: `K` more than the frame holds.
    generalize hK : 22100 * k + memoryGasCost c.top = K
    have hp := hat.addGas K
    have I : InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1)
        (p.blocks.drop (b + 1))) k 0 pc S s M (g + K) :=
      ⟨hseg, hstk, by simp only [Nat.add_zero]; omega, htop, hmem⟩
    have hsim := exec_simC (mx := mx) G (o := O T) hdata hvalue hstatic hself hcaller
      (O_ok c T).1 hbenv htx (O_ok c T).2 b hb 0 (G0 + K) rd is h known ty S Tw k s pc M
      (g + K) st ss hokC hh hu hk hR I R (by unfold MemBudget at *; omega)
    have hcnt := (execC_agree (Agree.refl (O T) (gasReads s.world) (sent s.world)) call b is S s
      le_rfl le_rfl).2
    have hex : ∀ T'', T.Le T'' → SolarTV.EVM.Program.exec (O T'') call b is S s =
        match execC (O T) call b is S s with
        | .done r => r
        | .cut i rest S' s' => SolarTV.EVM.Program.exec (O T'') call b (i :: rest) S' s' :=
      fun T'' hle => exec_O hle (by omega) hs0
    generalize hr : execC (O T) call b is S s = r at hsim hcnt hex
    cases r with
    | done r =>
      refine ⟨T, r, RunTable.Le.refl T, fun T'' hle => hex T'' hle, fun res hres => ?_,
        fun y hy => ?_⟩
      · subst hres
        exact SpecG.low hsim hp within hrun hok
      · subst hy
        obtain ⟨t, S', s'⟩ := y
        obtain ⟨⟨htle, hneedt, hj⟩, pc', T', M', g', st', ss', hh', hR', E', R', hB'⟩ := hsim
        obtain ⟨e1, r1, he1⟩ := hh' _ hp
        obtain ⟨m, within', hz, hrm⟩ := reaches_low r1 K evm rfl within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hmK⟩ := at_of_addGasR he1
        have hgm := reaches_gas_le r1
        rw [hz] at hgm
        simp only [gas_addGas] at hgm
        have hc1 := hcnt.1 s' rfl
        refine ⟨⟨htle, hneedt, hj⟩, m, within', ⟨T', pc', M', st', ss', rd, htle, hneedt, hR', E'.seg,
          E'.le_top, E'.mem, R', hatm⟩, ?_, ?_, by omega,
          by rw [hatm.2.2.2.2.2.1]; unfold MemBudget at hB'; omega, hrm⟩
        · dsimp only; omega
        · dsimp only; omega
    | cut i rest S' s' =>
      obtain ⟨hci, h', known', ty', k', pc', T', M', g', st', ss', hh', hok2, hh2, hu2, hk2, hR',
        I', R', hB'⟩ := hsim
      -- The segment, moved back to the frame's gas.
      obtain ⟨e1, r1, he1⟩ := hh' _ hp
      obtain ⟨m, within1, hz, hrm⟩ := reaches_low r1 K evm rfl within hrun hok
      rw [hz] at he1
      obtain ⟨hatm, hmK⟩ := at_of_addGasR he1
      have hgm := reaches_gas_le r1
      rw [hz] at hgm
      simp only [gas_addGas] at hgm
      have hL := hR'.length
      have hst := I'.stack
      have hc1 := hcnt.1 s' rfl
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
          gas_back hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
        let T1 : RunTable := { T with gases := T.gases ++ [m.gas - 2] }
        have hle1 : T.Le T1 := ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_append _ _⟩
        have hv : ∀ T'', T1.Le T'' → T''.gases.getD (gasReads s'.world) 0 = m.gas - 2 := by
          intro T'' hle
          rw [getD_of_prefix hle.2.2.2.2 (by simp [T1]; omega)]
          simp [T1, List.getD_eq_getElem?_getD, hc1.1, ← hTg]
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) G hnc hdata hvalue hstatic hself hcaller hbenv
          htx hb hok hG0 n rest (h' + 1) [] (some false :: ty') (k' - 1)
          (BitVec.ofNat 256 (m.gas - 2) :: S') (BitVec.ofNat 256 (m.gas - 2) :: T')
          { s' with world := s'.world ++ [.read "gas"] } (pc' + 1) M' (m.gas - 2) st' ss' T1 m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
          I'.mem ⟨R'.storage, R'.account, logsRel_read _ R'.logs⟩ hat2
          (by simp [T1]; omega) (by simp [hc1.2, hs0])
          (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, r, hle1.trans hle2, fun T'' hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T'' (hle1.trans (hle2.trans hle))]
          show SolarTV.EVM.Program.exec (O T'') call b (.effect .gas 0 :: rest) S' s' = r
          rw [exec_gas (hv T'' (hle2.trans hle)) (by omega)]
          exact hex2 T'' hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

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
          AssembleDyn.mload_dyn I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest h' [] (some false :: ty'.drop 1) (k' - 1)
          (s'.memory.load x.toNat :: S'') (s'.memory.load x.toNat :: Tr)
          { s' with memory := s'.memory.expand x.toNat 32 } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.op .load :: rest) _ s' = r
          rw [exec_loadC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩
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
          AssembleDyn.mstore_dyn I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - 2) [] (ty'.drop 2) (k' - 1) S'' Tr
          { s' with memory := s'.memory.store x.toNat y } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.op .store :: rest) _ s' = r
          rw [exec_storeC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

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
        have hg := AssembleDyn.return_back hatm hlt hcode within1 hrm hok
        refine ⟨T, .inl (SolarTV.EVM.Program.output s' (x :: y :: S'') false), RunTable.Le.refl T,
          fun T3 hle => ?_, fun res hres => ?_, fun y hy => ?_⟩
        · rw [hex T3 hle]
          rfl
        · obtain rfl := Sum.inl.inj hres
          simp only [SolarTV.EVM.Program.output, Bool.false_eq_true, ↓reduceIte]
          exact SpecG.low (SpecG.consequence (return_postSG (ss := ss') hlt hcode (by omega) rfl
            (by rw [read_eq I'.mem]; rfl) rfl (R'.slot hself)) (fun _ h => h)
            (fun _ h => ⟨ss', h, R'.logs⟩)) (hatm.addGas 0) within1 hrm hok
        · cases hy
      · -- REVERT: no run that succeeds reaches it.
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
        exact (AssembleDyn.revert_false hatm hlt hcode within1 hrm hok).elim

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
          AssembleDyn.keccak_dyn I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        obtain ⟨-, hkec⟩ := (O_ok c T).1 henv
        rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hat2
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - 1) [] (some false :: ty'.drop 2) (k' - 1)
          ((O T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S'')
          ((O T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: Tr)
          { s' with memory := s'.memory.expand x.toNat y.toNat } (pc' + 1) _ _ st' ss' T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          (KR.nil _) (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.effect .keccak256 2 :: rest) _ s' = r
          rw [exec_keccakC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

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
          AssembleDyn.log_dyn (n := ⟨tops.length, by omega⟩) I'.mem hmB (by omega) hatm rfl hlt hcode
            (decode_log ⟨tops.length, by omega⟩) hstatic within1 hrm hok
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨L, hL1, hL2⟩ := R'.logs
        obtain ⟨T2', r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) (ss0 := ss0) G hnc hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 n rest (h' - (tops.length + 2)) [] (ty'.drop (tops.length + 2))
          (k' - 1) S2 T2
          ⟨s'.memory.expand x.toNat y.toNat, s'.storage, s'.transient,
            s'.world ++ [.log tops ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩
          (pc' + 1) _ _ st' { ss' with logs := ss'.logs.push ⟨msg.currentTarget,
            tops.map U256.toBeBytes, memoryReadBytes (memoryExtend M' (extendMemory M'.size
              [(x, y)]).expandBy) x.toNat y.toNat⟩ } T m2 within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2
          ⟨R'.storage, R'.account, ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy)
                x.toNat y.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, read_eq I'.mem⟩⟩⟩ hat2
          (by show T.gases.length = gasReads (s'.world ++ [_]); rw [gasReads_log, hc1.1]; exact hTg)
          (by show sent (s'.world ++ [_]) = 0; rw [sent_log, hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2', r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b
            (.effect (.log tops.length) (tops.length + 2) :: rest) _ s' = r
          rw [exec_logC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩

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
          AssembleDynCopy.cdc_dyn hdata I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := seg (G0 := G0) (ss0 := ss0) G hnc hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 n rest (h' - 3) [] (ty'.drop 3) (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => SolarTV.Machine.calldataByte call (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' T m2
          within2 (by omega) hok3 (by omega) (by omega)
          (KR.nil _) hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          (by show T.gases.length = gasReads s'.world; rw [hc1.1]; exact hTg)
          (by show sent s'.world = 0; rw [hc1.2]; exact hs0) hb2 hrun2
        refine ⟨T2, r, hle2, fun T3 hle => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 (hle2.trans hle)]
          show SolarTV.EVM.Program.exec (O T3) call b (.effect .calldatacopy 3 :: rest) _ s' = r
          rw [exec_cdcC (by omega)]
          exact hex2 T3 hle
        · obtain ⟨hy1, after, within', hE, hT, hsn, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hsn, by omega, hbud, hra⟩
      · -- STATICCALL: only a certificate that says the program makes calls lets the checker cut there.
        obtain rfl := isScI_eq hsci
        exact absurd (blockOkC_sc hok2).1 (by simp [hnc])
      · obtain rfl := isRdsI_eq hrdi
        exact absurd (blockOkC_rds hok2).1 (by simp [hnc])
      · obtain rfl := isRdcI_eq hrdci
        exact absurd (blockOkC_rdc hok2).1 (by simp [hnc])
      · -- CALL, CREATE2 and CODECOPY: only a certificate that says the program creates lets the
        -- checker cut there.
        obtain rfl := isCallI_eq hcalli
        exact absurd (blockOkC_call hok2).1 (by simp [hnc])
      · obtain rfl := isC2I_eq hc2i
        exact absurd (blockOkC_c2 hok2).1 (by simp [hnc])
      · obtain rfl := isCcI_eq hcci
        exact absurd (blockOkC_cc hok2).1 (by simp [hnc])

/-! ## The checker with GAS -/

/-- `AssembleLoop.blocksOkL` with GAS. -/
def blocksOkC (p : Assemble.Program) (c : Cert) (mx : List Nat) :
    Nat → List (List Assemble.Instr) → Bool
  | _, [] => true
  | b, instrs :: rest =>
    decide (labelItems p c b ≤ budget c b) && decide (c.need b ≤ maxH mx b) &&
      decide (maxH mx b + budget c b ≤ 1000) &&
      blockOkC p c mx b (c.need b) [] (c.entry b) (budget c b - labelItems p c b) instrs &&
      blocksOkC p c mx (b + 1) rest

/-- **The checker of code with loops and GAS**: `AssembleLoop.checkL` with `blockOkC`. -/
def checkCB (p : Assemble.Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkC p c mx 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 200) && decide (code.size < 2 ^ 32) && !c.creates

/-- **The checker of code with calls and creations**: `checkCB` without its gate on creations,
for a certificate that says the program makes CALLs, CREATE2s and CODECOPYs (`Cert.creates`, with
`Cert.calls`). No theorem over runs covers it yet: programs it accepts are checked, not proved. -/
def checkCF (p : Assemble.Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkC p c mx 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 200) && decide (code.size < 2 ^ 32)

/-- **The checker of code with loops and GAS** for a program that makes no call: `checkCB` and a
certificate that says so. (`AssembleCutCall` checks programs with STATICCALLs.) -/
def checkC (p : Assemble.Program) (code : ByteArray) (c : Cert) (mx : List Nat) : Bool :=
  (walk (bytesOf code) c.offset 0 (lower p c)).isSome && blocksOkC p c mx 0 p.blocks &&
    labelsValid p c code && decide (c.need 0 = 0) && decide (c.top % 32 = 0) &&
    decide (c.top ≤ 2 ^ 200) && decide (code.size < 2 ^ 32) && !c.calls && !c.creates

theorem checkC_base {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkC p code c mx = true) : checkCB p code c mx = true ∧ c.calls = false := by
  simp only [checkC, checkCB, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  exact ⟨⟨h.1.1, h.2⟩, h.1.2⟩

/-- The checker of code with GAS and STATICCALLs refuses a certificate that says the program creates. -/
theorem checkCB_creates {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkCB p code c mx = true) : c.creates = false := by
  simp only [checkCB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem blocksOkC_get {p : Assemble.Program} {c : Cert} {mx : List Nat} :
    ∀ (l : List (List Assemble.Instr)) (b : Nat),
    blocksOkC p c mx b l = true → ∀ k (hk : k < l.length),
      labelItems p c (b + k) ≤ budget c (b + k) ∧ c.need (b + k) ≤ maxH mx (b + k) ∧
      maxH mx (b + k) + budget c (b + k) ≤ 1000 ∧
      blockOkC p c mx (b + k) (c.need (b + k)) [] (c.entry (b + k))
        (budget c (b + k) - labelItems p c (b + k)) l[k] = true
  | [], _, _, _, hk => absurd hk (by simp)
  | x :: l, b, h, 0, _ => by
    simp only [blocksOkC, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [and_assoc] using h.1
  | x :: l, b, h, k + 1, hk => by
    simp only [blocksOkC, Bool.and_eq_true] at h
    have := blocksOkC_get l (b + 1) h.2 k (by simp at hk; omega)
    rw [show b + (k + 1) = b + 1 + k by omega]
    simpa using this

/-- The facts of the checker with GAS. -/
structure GlobC (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray) : Prop
    extends GlobT p c code where
  block : ∀ t (ht : t < p.blocks.length), labelItems p c t ≤ budget c t ∧
    c.need t ≤ maxH mx t ∧ maxH mx t + budget c t ≤ 1000 ∧
    blockOkC p c mx t (c.need t) [] (c.entry t) (budget c t - labelItems p c t) p.blocks[t] = true

theorem globC_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (h : checkCB p code c mx = true) :
    GlobC p c mx code ∧ Seg (bytesOf code) c.offset 0 (lower p c) code.size ∧ c.need 0 = 0 := by
  simp only [checkCB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hw, hblocks⟩, hlabels⟩, hneed⟩, hmod⟩, htop⟩, hsize⟩, -⟩ := h
  obtain ⟨stream, hw⟩ := Option.isSome_iff_exists.1 hw
  have hseg : Seg (bytesOf code) c.offset 0 (lower p c) code.size := by
    have := seg_of_walk (walk_sound hw)
    rwa [length_bytesOf] at this
  refine ⟨⟨⟨hmod, htop, hsize, fun t ht htgt => ?_⟩, fun t ht => ?_⟩, hseg, hneed⟩
  · have hv : isValidJumpDest (validJumpDestinations code) (c.offset t) = true := by
      simp only [labelsValid, List.all_eq_true, List.mem_range] at hlabels
      have := hlabels t ht
      simpa [htgt] using this
    obtain ⟨pc', hs, hpc⟩ := seg_lowerFrom p c t p.blocks 0 0 hseg ht
    simp only [Nat.zero_add] at hs hpc
    rw [← hpc htgt] at hs
    refine ⟨hv, ?_, hs⟩
    have hs' := hs
    rw [lowerFrom_drop p c ht] at hs'
    simp only [lowerBlock, htgt, ite_true, List.cons_append] at hs'
    cases hs' with
    | cons d _ _ =>
      have := decode_lt d
      rwa [length_bytesOf] at this
  · have := blocksOkC_get p.blocks 0 hblocks t ht
    simpa using this

/-! ## A block, read back from a run that succeeds -/

/-- The relation at a block entry, with the table's GAS reads and no message sent. -/
def EntT (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray)
    (msg : Message .fusaka) (ss0 : Substate) (T : RunTable) (x : Nat × List Word × State)
    (evm : Evm .fusaka Nat) : Prop :=
  EntC p c mx code msg ss0 x evm ∧ T.gases.length = gasReads x.2.2.world ∧ sent x.2.2.world = 0 ∧
    memoryGasCost evm.memory.size + evm.gas ≤ msg.gas

/-- **A block of code with loops and GAS, read back from a run that succeeds.** -/
theorem advances_checkC {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobC p c mx code) (hnc : c.calls = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntT p c mx code msg ss0 T0 x evm) :
    Advances (fun o => SolarTV.EVM.Program.block o call p) O (EntT p c mx code msg ss0)
      (fun res => PostL call msg.currentTarget ss0 res.2 res.1)
      (fun y e => AssembleLoop.meas p c e.gas y.1) T0 x evm := by
  intro bound runChild _ within fin hrun hok
  obtain ⟨b, S, s⟩ := x
  obtain ⟨⟨Tw, pc, M, st, ss, rd, hle, hneed, hR, hseg, htop, hmem, R, hat⟩, hTg, hs0, hbud⟩ := hE
  simp only at hle hneed hR hseg hmem R hTg hs0
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
        obtain ⟨m, within', hz, hrm⟩ := reaches_low r1 1 evm rfl within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hgm⟩ := at_of_addGasR he1
        exact ⟨pc + 1, m, within', hatm, hseg', by simp only [ht, ite_true]; omega, hrm⟩
      · simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at hseg
        exact ⟨pc, evm, within, hat, hseg, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          hrun⟩
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := seg (G0 := msg.gas) G.toGlobT hnc hdata hvalue hstatic hself hcaller
      hbenv htx hb hok hgas (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) (KR.nil _) hR hseg1 (by omega) htop hmem R hat1 hTg hs0
      (by unfold MemBudget; rw [← hat.2.2.2.2.2.1]; omega) hrun1
    refine ⟨T', r, hle', fun T'' h => ?_, fun res hres => hpost res hres, fun y hy => ?_⟩
    · simp only [SolarTV.EVM.Program.block, hblk]
      rw [hex T'' h]
    · obtain ⟨t, S', s'⟩ := y
      obtain ⟨⟨htle, -, hj⟩, after, within', hE', hT', hs', hga, hbud', hra⟩ := hnext _ hy
      refine ⟨after, within', ⟨hE', hT', hs', hbud'⟩, ?_, hra⟩
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
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy

/-- **EVM IR to bytecode, run by run, at the run's own gas, for code with loops, GAS and memory at
any offset**: for every program the checker with GAS accepts, at every gas below `2 ^ 256` and
every call, the oracle of the run's table makes every result of the bytecode the EVM IR's or a
failure that changes nothing. The bound on the gas is what keeps memory a run pays for within
SolarTV's count of words (`AssembleLoop.size_le_of_cost`). -/
theorem runs_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkC p code c mx = true) (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) :
    ∃ T, Within (evmirSem (O T)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨hcb, hnc⟩ := checkC_base hc
  obtain ⟨G, hseg, hneed0⟩ := globC_of_checkC hcb
  refine within_of_advances O (fun ss0 => EntT p c mx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p c e.gas y.1) (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkC G hnc rfl
      (by simp [Final.Target.messageWith, Target.message]) rfl rfl rfl rfl rfl hgas T x evm hE)
  refine ⟨⟨[], 0, .empty, st', ss', .empty, Nat.zero_le _, fun _ => ⟨by simp [hneed0], by simp⟩,
    SR.nil c _, by rw [List.drop_zero]; exact hseg, by simp, memRel_initial, R, ?_⟩, rfl, rfl, ?_⟩
  have hcode : (Final.Target.messageWith gas code call).code = code := rfl
  · exact ⟨by simp [startFrame, hcode], by simp [startFrame, hcode], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
  · have h0 : memoryGasCost 0 = 0 := by rw [memoryGasCost_eq]; simp [wordCount, ceil32, WORD_BYTES]
    simp only [startFrame, ByteArray.size_empty, h0, Nat.zero_add]
    exact le_refl _

/-- `RunOracle.WithinRun` at every gas below `2 ^ 256` (a transaction's gas is at most
`2 ^ 64`). -/
def WithinRunLt (sem : Oracle → Sem) (p : ∀ o, (sem o).Prog) (code : ByteArray)
    (scope : Call → Prop) (Ok : Oracle → Prop) : Prop :=
  ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ o, Ok o ∧
    Within (sem o) (ethLibWith gas) (p o) code (· = call)

/-- `RunOracle.WithinRun.of_back` below `2 ^ 256` gas. -/
theorem WithinRunLt.of_back {A sem : Oracle → Sem} {q : ∀ o, (A o).Prog} {p : ∀ o, (sem o).Prog}
    {code : ByteArray} {scope : Call → Prop} {Ok : Oracle → Prop}
    (back : ∀ o, Ok o → Stage (sem o) (A o) (p o) (q o) scope)
    (h : WithinRunLt sem p code scope Ok) : WithinRunLt A q code scope Ok := by
  intro gas hgas call hc
  obtain ⟨o, ho, hw⟩ := h gas hgas call hc
  refine ⟨o, ho, fun call' h' obs hrun => ?_⟩
  subst h'
  rcases hw call' rfl obs hrun with e | e
  · exact Or.inl (back o ho call' hc obs e)
  · exact Or.inr e

/-- The per-run theorem below `2 ^ 256` gas for every program the checker with GAS accepts. -/
theorem withinRun_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert}
    {mx : List Nat} (hc : checkC p code c mx = true) (scope : Call → Prop) :
    WithinRunLt evmirSem (fun _ => p) code scope (CertOk c) := by
  intro gas hgas call _
  obtain ⟨T, hT⟩ := runs_of_checkC hc gas hgas call
  exact ⟨O T, O_ok c T, hT⟩

/-- **The assembly premise of `holds_of_runs`** below `2 ^ 256` gas for every program the
checker with GAS accepts: an oracle and an open world that agree, under which the EVM IR gives the
bytecode's result or a failure that changes nothing. -/
theorem assembly_of_checkC {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkC p code c mx = true) (scope : Call → Prop) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call _
  obtain ⟨T, hT⟩ := runs_of_checkC hc gas hgas call
  obtain ⟨W, hW, hA⟩ := O_agree T
  exact ⟨O T, W, hW, hA, hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCut.withinRun_of_checkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_of_checkC

/-- info: 'SolidCore.Refinement.Solar.AssembleCut.assembly_of_checkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkC

/-- **The first lowered MIR to the exact bytecode, run by run, for code with loops, GAS and memory
at any offset**: the backend stages read backwards and the checker with GAS give, for every gas below
`2 ^ 256` and every call, an oracle meeting the certificate's constraints under which every result
of the bytecode is the first lowered MIR's or a failure that changes nothing. -/
theorem withinRun_mir_of_checkC {stage0 : SolarTV.MIR.Lowered.moduleLayer.Prog}
    {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat} {S scope : Call → Prop}
    (back : ∀ o, Certified SolarTV.EVM.Program.layer SolarTV.MIR.Lowered.moduleLayer o p stage0 S)
    (hS : ∀ call, scope call → S call) (hc : checkC p code c mx = true) :
    WithinRunLt mirSem (fun _ => stage0) code scope (CertOk c) :=
  WithinRunLt.of_back (fun o _ => fun call hcall obs h =>
      stage_of_certified (back o) call (hS call hcall) obs h)
    (withinRun_of_checkC hc scope)

/-- info: 'SolidCore.Refinement.Solar.AssembleCut.withinRun_mir_of_checkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms withinRun_mir_of_checkC

/-- **`holds_of_runs` below `2 ^ 256` gas**: the specification of SolidCore, the stages to EVM IR
and the assembly premise at every gas below `2 ^ 256` (`assembly_of_checkC`) give the
specification of the bytecode at each such gas. -/
theorem holds_of_runs_lt {St : Type} {fuel : Nat}
    {mirSem evmirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : ∀ o, (mirSem o).Prog} {evmir : ∀ o, (evmirSem o).Prog} {code : ByteArray}
    {spec : Final.ContractSpec St}
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : ∀ o W, CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (mir o) spec.Calls)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (mir o) (evmir o) spec.Calls)
    (assembly : ∀ gas, gas < 2 ^ 256 → ∀ call, spec.Calls call → ∃ o W, W.Open ∧ CallsAgree o W ∧
      Final.Within (evmirSem o) (Final.ethLibWith gas) (evmir o) code (· = call))
    (gas : Nat) (hgas : gas < 2 ^ 256) : Final.Holds (Final.ethLibWith gas) code spec := by
  intro f hf args ht v hv σ hinv hreq obs hrun
  have hc : spec.Calls (f.call args v σ) := ⟨f, hf, args, ht, v, hv, σ, rfl⟩
  obtain ⟨o, W, hopen, hagree, hwithin⟩ := assembly gas hgas _ hc
  have agree := Final.agree_of_stage ((lowering o W hagree).trans (backend o)) (fin W hopen)
  rcases hwithin _ rfl obs hrun with h | ⟨hs, hst, hl⟩
  · obtain ⟨obs', hs', hm⟩ := agree _ hc
    rw [h] at hm
    cases hm
    exact source W hopen f hf args ht v hv σ hinv hreq obs hs'
  · exact ⟨fun h'' => absurd (hs.symm.trans h'') (by decide), fun _ => ⟨hst, hl⟩⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCut.holds_of_runs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_runs_lt

end SolidCore.Refinement.Solar.AssembleCut

import SolidCore.Refinement.Solar.AssembleCreateRun
import SolidCore.Refinement.Solar.AssembleCreateCutQ
import SolidCore.Refinement.Solar.AssembleCallSeg

/-!
# Code with CALLs, CREATE2s and CODECOPYs, block by block, at the frame's own gas

The checker without the creation gate (`AssembleCut.checkCF`) cuts a block at each CALL, CREATE2 and
CODECOPY (`AssembleCut.blockOkC`, under a certificate that says the program creates), and refuses
STATICCALL there (`AssembleCut.blockOkC_noSc_creates`). `segF` reads each
segment back from a run that succeeds as `AssembleCut.seg` does, under the oracle of the run's two tables
(`AssembleCreateRun.FO`): GAS adds its gas to the run table, CALL its flag, return data and storage
after (`AssembleCallValueZeroSeg.call0_cut`, `AssembleCallValueSeg.callValue_cut`), CREATE2 its word,
return data and storage after to the creation table and an entry at its message to the run table
(`AssembleCreateSeg.create2_cut`, `AssembleCreateRun.create2_table`), and CODECOPY reads the frame's code
(`AssembleCreateSeg.codecopy_cut`). RETURNDATASIZE and RETURNDATACOPY read the frame's return data,
which is the tables' answer at the frame's world (`RdF`): the run table's output of the last CALL,
the creation table's of the last CREATE2, empty before any message; each cut re-establishes it from
the frame EthLib's runner returned (`call0_cutQ`, `callValue_cutQ`, `create2_cutQ`).

Every extension of both tables runs each segment to the same end (`AssembleCreateRun.exec_F`), and
`TabF` keeps the tables in step with the frame's world from cut to cut.

`segF` names what it assumes of the run:

* `SitesOk`: at every CALL and CREATE2 of the run, the frames the runner returns for its message from
  the caller state it makes keep the frame's account, add no log when they succeed and have outputs
  below `2 ^ 256` bytes (`AssembleCreateCutQ`), and a CALL with value calls code that is no
  EIP-7702 delegation.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateSegF

open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Final
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.RunOracle SolidCore.Refinement.Solar.AssembleRun
open SolidCore.Refinement.Solar.AssembleRunLoop SolidCore.Refinement.Solar.AssembleCut
open SolidCore.Refinement.Solar.AssembleEffects
open SolidCore.Refinement.Solar.AssembleCreateSeg SolidCore.Refinement.Solar.AssembleCreateRun
open SolidCore.Refinement.Solar.AssembleCallValueSeg SolidCore.Refinement.Solar.AssembleCallValueZeroSeg
open SolidCore.Refinement.Solar.AssembleCreateSegOracle SolidCore.Refinement.Solar.AssembleCreateCut
open SolidCore.Refinement.Solar.AssembleCreateCutQ
open SolidCore.Refinement.Solar.AssembleCallValueEffect
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

/-- **A segment keeps the frame's world**: every effect that adds an event is a cut. -/
theorem execC_world (o : Oracle) (call : Call) (b : Nat) :
    ∀ (is : List Assemble.Instr) (S : List Word) (s s' : State),
      endState (execC o call b is S s) = some s' → s'.world = s.world
  | [], _, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .op op :: rest, S, s, s', h => by
    by_cases hc : cutOp op = true
    · simp only [execC, hc, ite_true, endState, Option.some.injEq] at h
      subst h; rfl
    · have hc' : cutOp op = false := by simpa using hc
      cases hs : SolarTV.EVM.Program.stepOp (SolarTV.EVM.Program.context o call s) op S s.memory with
      | error _ => simp [execC, hc', hs, endState] at h
      | ok r =>
        obtain ⟨S', m⟩ := r
        simp only [execC, hc', hs, Bool.false_eq_true, ite_false] at h
        exact execC_world o call b rest S' { s with memory := m } s' h
  | .effect e a :: rest, S, s, s', h => by
    by_cases hc : cutEffect e = true
    · simp only [execC, hc, ite_true, endState, Option.some.injEq] at h
      subst h; rfl
    · have he : cutEffect e = false := by simpa using hc
      by_cases hl : S.length < a
      · simp [execC, he, hl, endState] at h
      · cases happ : Effect.apply o call e (S.take a) s with
        | none => simp [execC, he, hl, happ, endState] at h
        | some r =>
          obtain ⟨res, s1⟩ := r
          have hw := apply_world_eq he happ
          simp only [execC, he, hl, Bool.false_eq_true, ite_false, happ] at h
          split_ifs at h
          · simp [endState] at h
          · rw [execC_world o call b rest _ s1 s' h, hw]
  | .jump t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h <;> simp [endState] at h
    subst h; rfl
  | .jumpi t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h
    · simp [endState] at h
    · cases S with
      | nil => simp [endState] at h
      | cons x S =>
        simp only at h
        split_ifs at h
        · exact execC_world o call b rest S s s' h
        · simp [endState] at h; subst h; rfl
  | .pushLabel t :: rest, S, s, s', h => by
    simp only [execC] at h
    split_ifs at h
    · simp [endState] at h
    · exact execC_world o call b rest _ s s' h
  | .jumpDyn :: rest, S, s, s', h => by
    cases S with
    | nil => simp [execC, endState] at h
    | cons x S => simp [execC, endState] at h; subst h; rfl
  | .jumpiDyn :: rest, S, s, s', h => by
    match S with
    | [] => simp [execC, endState] at h
    | [_] => simp [execC, endState] at h
    | x :: y :: S =>
      simp only [execC] at h
      split_ifs at h
      · exact execC_world o call b rest S s s' h
      · simp [endState] at h; subst h; rfl
  | .jumpTable ts :: rest, S, s, s', h => by
    cases S with
    | nil => simp [execC, endState] at h
    | cons x S =>
      cases ht : ts[x.toNat]? with
      | none => simp [execC, ht, endState] at h
      | some t => simp [execC, ht, endState] at h; subst h; rfl
  | .stop :: rest, S, s, s', h => by simp [execC, endState] at h
  | .ret :: rest, S, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .revert :: rest, S, s, s', h => by simp [execC, endState] at h; subst h; rfl
  | .invalid :: rest, S, s, s', h => by simp [execC, endState] at h

/-- The oracle of a run with creations reads the frame's code as its base does, whatever its
tables. -/
theorem codeByte_FO (code : ByteArray) (T : RunTable) (A : CreateTable) (j : Nat) :
    codeByte (FO code T A) j = codeByte (baseF code) j := by
  have h1 : (FO code T A).env "code" [] [BitVec.ofNat 256 j] =
      (tableOracle (baseF code) T).env "code" [] [BitVec.ofNat 256 j] :=
    (createOracle_other (o := tableOracle (baseF code) T) (A := A) (w := []) (by simp [lastCreate])).2.2.2 _ _
  have h2 : (tableOracle (baseF code) T).env "code" [] [BitVec.ofNat 256 j] =
      (baseF code).env "code" [] [BitVec.ofNat 256 j] := by
    simp [tableOracle]
  unfold codeByte
  rw [h1, h2]

theorem codeCopied_FO (code : ByteArray) (T T' : RunTable) (A A' : CreateTable) (s : State)
    (d off sz : Word) : codeCopied (FO code T' A') s d off sz = codeCopied (FO code T A) s d off sz := by
  simp only [codeCopied, codeByte_FO]

/-! ## The named hypotheses on a run with calls and creations -/

/-- **Named hypothesis on a run with calls and creations**: at every CALL and CREATE2 of the frame
that the run goes on from to `fin`, what the run gives the callee's frame (`AssembleCreateCutQ.Call0Q`,
`CallVQ`, `Create2Q`: it keeps the frame's account, adds no log when it succeeds and has an output
below `2 ^ 256` bytes), and at a CALL with value, a callee whose code is found and is no EIP-7702
delegation. -/
structure SitesOk (code : ByteArray) (msg : Message .fusaka)
    (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop) (bound : Nat)
    (runChild : MessageRunner .fusaka Nat bound) (fin : Evm .fusaka Nat) : Prop where
  call0 : ∀ {e : Evm .fusaka Nat} {within : GasMeter.gasHeld e.gas ≤ bound} {pc : Nat}
    {asked addr inOff inSize outOff outSize : U256} {Tr : List U256} {M : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray},
    At code msg pc (asked :: addr :: 0 :: inOff :: inSize :: outOff :: outSize :: Tr) M g st ss rd e →
    (hlt : pc < code.size) → code[pc] = 0xf1 →
    runFrame (step .fusaka) (step_decreases .fusaka) bound runChild e within = .ok fin →
    Call0Q msg P st M addr inOff inSize outOff outSize
  callV : ∀ {e : Evm .fusaka Nat} {within : GasMeter.gasHeld e.gas ≤ bound} {pc : Nat}
    {asked dst v i isz o osz : U256} {Tr : List U256} {M : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray},
    At code msg pc (asked :: dst :: v :: i :: isz :: o :: osz :: Tr) M g st ss rd e →
    (hlt : pc < code.size) → code[pc] = 0xf1 → v ≠ 0 →
    runFrame (step .fusaka) (step_decreases .fusaka) bound runChild e within = .ok fin →
    ∃ calleeCode, st.getCode (st.getAccount (toAddressMasked dst)).codeHash = .ok calleeCode ∧
      delegatedAddress calleeCode = none ∧ CallVQ msg P g st ss M asked dst v i isz o osz calleeCode
  create2 : ∀ {e : Evm .fusaka Nat} {within : GasMeter.gasHeld e.gas ≤ bound} {pc : Nat}
    {value start size salt : U256} {Tr : List U256} {M : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray},
    At code msg pc (value :: start :: size :: salt :: Tr) M g st ss rd e →
    (hlt : pc < code.size) → code[pc] = 0xf5 →
    runFrame (step .fusaka) (step_decreases .fusaka) bound runChild e within = .ok fin →
    Create2Q msg P g st M value start size salt

/-! ## A block, segment by segment, with calls and creations -/

/-! ## The return data of a run with calls and creations -/

/-- **The frame's return data is the tables' answer** at the world, under every extension of both
tables: after a CALL the run table's output of its message, after a CREATE2 the creation table's, and
empty before any message. -/
def RdF (code : ByteArray) (T : RunTable) (A : CreateTable) (w : List Event) (rd : ByteArray) : Prop :=
  ∀ T'' A'', T.Le T'' → A.Le A'' → RdRel (FO code T'' A'') w rd

theorem RdF.mono {code : ByteArray} {T T1 : RunTable} {A A1 : CreateTable} {w : List Event}
    {rd : ByteArray} (hT : T.Le T1) (hA : A.Le A1) (h : RdF code T A w rd) : RdF code T1 A1 w rd :=
  fun T'' A'' h1 h2 => h T'' A'' (hT.trans h1) (hA.trans h2)

/-- An event that sends no message keeps what the tables answer for the return data. -/
theorem FO_rd_append {code : ByteArray} {T : RunTable} {A : CreateTable} {w : List Event} {e : Event}
    (he : Event.sends e = false) (hc : isCreateE e = false) (name : String) (a : List Word)
    (hn : (name = "returndatasize" ∧ a = []) ∨ ∃ i, name = "returndata" ∧ a = [i]) :
    (FO code T A).env name (w ++ [e]) a = (FO code T A).env name w a := by
  have hl : lastCreate (w ++ [e]) = lastCreate w := by
    simp [lastCreate, List.filter_append, he]
  have hcr : creates (w ++ [e]) = creates w := by
    simp [creates, List.filter_append, hc]
  have hs : sent (w ++ [e]) = sent w := by
    simp [sent, List.filter_append, he]
  have hout : T.out (w ++ [e]) = T.out w := by simp [RunTable.out, hs]
  have hAo : A.out (w ++ [e]) = A.out w := by simp [CreateTable.out, hcr]
  rcases hn with ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
  · simp [FO, createOracle, tableOracle, hl, hAo, hout]
  · simp [FO, createOracle, tableOracle, hl, hAo, hout]

theorem RdF.append {code : ByteArray} {T : RunTable} {A : CreateTable} {w : List Event} {e : Event}
    {rd : ByteArray} (he : Event.sends e = false) (hc : isCreateE e = false) (h : RdF code T A w rd) :
    RdF code T A (w ++ [e]) rd := by
  intro T'' A'' h1 h2
  obtain ⟨h3, h4⟩ := h T'' A'' h1 h2
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [returndataSize] at h3 ⊢
    rw [FO_rd_append he hc _ _ (.inl ⟨rfl, rfl⟩)]
    exact h3
  · simp only [returndataByte] at h4 ⊢
    rw [FO_rd_append he hc _ _ (.inr ⟨_, rfl, rfl⟩)]
    exact h4 i hi

/-- A world whose last message is no creation reads the return data of the run table. -/
theorem rdRel_FO_of_table {code : ByteArray} {T : RunTable} {A : CreateTable} {w : List Event}
    {rd : ByteArray} (hl : lastCreate w = false) (h : RdRel (tableOracle (baseF code) T) w rd) :
    RdRel (FO code T A) w rd := by
  obtain ⟨_, _, _, henv⟩ := createOracle_other (o := tableOracle (baseF code) T) (A := A) hl
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [returndataSize, henv]
    exact h.1
  · simp only [returndataByte, henv]
    exact h.2 i hi

/-- A world whose last message is a creation reads the return data of the creation table, whatever
the oracle under it. -/
theorem rdRel_FO_of_create {code : ByteArray} {o : Oracle} {T : RunTable} {A : CreateTable}
    {w : List Event} {rd : ByteArray} (hl : lastCreate w = true) (h : RdRel (createOracle o A) w rd) :
    RdRel (FO code T A) w rd := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := h.1
    simp only [returndataSize, createOracle, hl, ite_true, and_self] at this ⊢
    exact this
  · have := h.2 i hi
    simp only [returndataByte, createOracle, hl, ite_true] at this ⊢
    simpa using this

/-- Before any message the frame's return data is empty, which every table answers. -/
theorem RdF.nil (code : ByteArray) (T : RunTable) (A : CreateTable) : RdF code T A [] .empty := by
  intro T'' A'' _ _
  have hl : lastCreate ([] : List Event) = false := by simp [lastCreate]
  refine rdRel_FO_of_table hl ?_
  refine ⟨?_, fun i hi => by simp at hi⟩
  simp [returndataSize, tableOracle, RunTable.out, sent]

set_option maxRecDepth 8000 in
/-- **`AssembleCut.seg` with CALLs, CREATE2s and CODECOPYs**: the rest of a block from an instruction,
read back from a run that succeeds, under the oracle of the run's two tables. Every extension of the
tables it ends with runs the rest of the block to the same end. -/
theorem segF {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobT p c code) (hcr : c.creates = true) {call : Call} {msg : Message .fusaka}
    {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    {b : Nat} (hb : b < p.blocks.length) {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {fin : Evm .fusaka Nat} (hok : fin.error = none) {G0 : Nat} (hG0 : G0 < 2 ^ 256)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hsites : SitesOk code msg P bound runChild fin) :
    ∀ (n : Nat) (is : List Assemble.Instr) (h : Nat) (known : List Word) (ty : List Ty) (k : Nat)
      (S Tw : List Word) (s : State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate) (rd : ByteArray) (T : RunTable)
      (A : CreateTable) (evm : Evm .fusaka Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      is.length < n → blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → known <+: S → SR c ty S Tw →
      Seg (bytesOf code) c.offset pc
        (lowerInstrs p c b is ++ lowerFrom p c (b + 1) (p.blocks.drop (b + 1))) code.size →
      S.length + k ≤ 1000 → M.size ≤ c.top → MemRel s.memory M → Rel msg ss0 st ss s →
      At code msg pc Tw M g st ss rd evm → TabF T A s.world → RdF code T A s.world rd →
      MemBudget G0 M g →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      ∃ T' A' r, T.Le T' ∧ A.Le A' ∧
        (∀ T'' A'', T'.Le T'' → A'.Le A'' →
          SolarTV.EVM.Program.exec (FO code T'' A'') call b is S s = r) ∧
        (∀ res, r = .inl res → PostL call msg.currentTarget ss0 res.2 res.1 fin) ∧
        (∀ y, r = .inr y → (y.1 ≤ p.blocks.length ∧
          (y.1 < p.blocks.length → c.need y.1 ≤ y.2.1.length ∧ y.2.1.length ≤ maxH mx y.1) ∧
          (y.1 = b + 1 ∨ isTarget p c y.1 = true)) ∧
          ∃ (after : Evm .fusaka Nat) (within' : GasMeter.gasHeld after.gas ≤ bound),
            EntC p c mx code msg ss0 y after ∧ TabF T' A' y.2.2.world ∧
            RdF code T' A' y.2.2.world after.returnData ∧ after.gas ≤ g ∧
            memoryGasCost after.memory.size + after.gas ≤ G0 ∧
            runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, is, h, known, ty, k, S, Tw, s, pc, M, g, st, ss, rd, T, A, evm, within, hn, hokC, hh, hu,
      hk, hR, hseg, hstk, htop, hmem, R, hat, hs0, hrd0, hB, hrun => by
    have hTg : T.gases.length = gasReads s.world := hs0.1
    have hge : evm.gas = g := hat.2.2.2.2.2.2.1
    -- The segment with gas to spare for it alone: `K` more than the frame holds.
    generalize hK : 22100 * k + memoryGasCost c.top = K
    have hp := hat.addGas K
    have I : InvL c code call (lowerInstrs p c b is ++ lowerFrom p c (b + 1)
        (p.blocks.drop (b + 1))) k 0 pc S s M (g + K) :=
      ⟨hseg, hstk, by simp only [Nat.add_zero]; omega, htop, hmem⟩
    have hsim := exec_simC (mx := mx) G (o := FO code T A) hdata hvalue hstatic hself hcaller
      (FO_ok c code T A).1 hbenv htx (FO_ok c code T A).2 b hb 0 (G0 + K) rd is h known ty S Tw k s pc M
      (g + K) st ss hokC hh hu hk hR I R (by unfold MemBudget at *; omega)
    have hcnt := (execC_agree (Agree.refl (FO code T A) (gasReads s.world) (sent s.world)) call b is S s
      le_rfl le_rfl).2
    have hex : ∀ T'' A'', T.Le T'' → A.Le A'' → SolarTV.EVM.Program.exec (FO code T'' A'') call b is S s =
        match execC (FO code T A) call b is S s with
        | .done r => r
        | .cut i rest S' s' => SolarTV.EVM.Program.exec (FO code T'' A'') call b (i :: rest) S' s' :=
      fun T'' A'' hle hleA => exec_F hle hleA (by omega) (le_of_eq hs0.2.2.1.symm) (le_of_eq hs0.2.2.2.2.2.2.1.symm)
    generalize hr : execC (FO code T A) call b is S s = r at hsim hcnt hex
    cases r with
    | done r =>
      refine ⟨T, A, r, RunTable.Le.refl T, CreateTable.Le.refl A, fun T'' A'' hle hleA => hex T'' A'' hle hleA,
        fun res hres => ?_, fun y hy => ?_⟩
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
        have hw1 := execC_world _ _ _ is S s s' (by rw [hr]; rfl)
        refine ⟨⟨htle, hneedt, hj⟩, m, within', ⟨T', pc', M', st', ss', rd, htle, hneedt, hR', E'.seg,
          E'.le_top, E'.mem, R', hatm⟩, ?_, ?_, by omega,
          by rw [hatm.2.2.2.2.2.1]; unfold MemBudget at hB'; omega, hrm⟩
        · dsimp only
          rw [hw1]
          exact hs0
        · dsimp only
          rw [hw1, show m.returnData = rd from hatm.2.2.2.2.2.2.2.2.2.2.2.2]
          exact hrd0
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
      have hw1 := execC_world _ _ _ is S s s' (by rw [hr]; rfl)
      have hs1 : TabF T A s'.world := by rw [hw1]; exact hs0
      have hrd1 : RdF code T A s'.world rd := by rw [hw1]; exact hrd0
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
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue hstatic hself hcaller hbenv
          htx hb hok hG0 hdepth meets hsites n rest (h' + 1) [] (some false :: ty') (k' - 1)
          (BitVec.ofNat 256 (m.gas - 2) :: S') (BitVec.ofNat 256 (m.gas - 2) :: T')
          { s' with world := s'.world ++ [.read "gas"] } (pc' + 1) M' (m.gas - 2) st' ss' rd T1 A m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
          I'.mem ⟨R'.storage, R'.account, logsRel_read _ R'.logs⟩ hat2
          (TabF.gas hs1 (m.gas - 2)) (RdF.append rfl rfl (RdF.mono hle1 (CreateTable.Le.refl A) hrd1))
          (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, A2, r, hle1.trans hle2, hA2, fun T'' A'' hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T'' A'' (hle1.trans (hle2.trans hle)) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T'' A'') call b (.effect .gas 0 :: rest) S' s' = r
          rw [exec_gasF (hv T'' (hle2.trans hle)) (by omega)]
          exact hex2 T'' A'' hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest h' [] (some false :: ty'.drop 1) (k' - 1)
          (s'.memory.load x.toNat :: S'') (s'.memory.load x.toNat :: Tr)
          { s' with memory := s'.memory.expand x.toNat 32 } (pc' + 1) M2 g2 st' ss' rd T A m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.op .load :: rest) _ s' = r
          rw [exec_loadC (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
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
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 2) [] (ty'.drop 2) (k' - 1) S'' Tr
          { s' with memory := s'.memory.store x.toNat y } (pc' + 1) M2 g2 st' ss' rd T A m2
          within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.op .store :: rest) _ s' = r
          rw [exec_storeC (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩

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
        refine ⟨T, A, .inl (SolarTV.EVM.Program.output s' (x :: y :: S'') false), RunTable.Le.refl T,
          CreateTable.Le.refl A, fun T3 A3 hle hleA => ?_, fun res hres => ?_, fun y hy => ?_⟩
        · rw [hex T3 A3 hle hleA]
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
        obtain ⟨-, hkec⟩ := (FO_ok c code T A).1 henv
        rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hat2
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 1) [] (some false :: ty'.drop 2) (k' - 1)
          ((FO code T A).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S'')
          ((FO code T A).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: Tr)
          { s' with memory := s'.memory.expand x.toNat y.toNat } (pc' + 1) _ _ st' ss' rd T A m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
          (by simp; omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .keccak256 2 :: rest) _ s' = r
          rw [exec_keccakC (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2', A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) (ss0 := ss0) G hcr hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - (tops.length + 2)) [] (ty'.drop (tops.length + 2))
          (k' - 1) S2 T2
          ⟨s'.memory.expand x.toNat y.toNat, s'.storage, s'.transient,
            s'.world ++ [.log tops ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩
          (pc' + 1) _ _ st' { ss' with logs := ss'.logs.push ⟨msg.currentTarget,
            tops.map U256.toBeBytes, memoryReadBytes (memoryExtend M' (extendMemory M'.size
              [(x, y)]).expandBy) x.toNat y.toNat⟩ } rd T A m2 within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2
          ⟨R'.storage, R'.account, ⟨L ++ [⟨msg.currentTarget, tops.map U256.toBeBytes,
              memoryReadBytes (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy)
                x.toNat y.toNat⟩], by simp [Array.toList_push, hL1],
              filter_snoc_log ▸ forall₂_snoc hL2 ⟨rfl, rfl, read_eq I'.mem⟩⟩⟩ hat2
          (TabF.log hs1 _ _) (RdF.append rfl rfl hrd1) hb2 hrun2
        refine ⟨T2', A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b
            (.effect (.log tops.length) (tops.length + 2) :: rest) _ s' = r
          rw [exec_logC (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩

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
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) (ss0 := ss0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 3) [] (ty'.drop 3) (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => SolarTV.Machine.calldataByte call (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd T A m2
          within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .calldatacopy 3 :: rest) _ s' = r
          rw [exec_cdcC (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
      · -- STATICCALL: the checker refuses it in a program that creates.
        exact absurd (blockOkC_noSc_creates hsci hok2) (by simp [hcr])
      · -- RETURNDATASIZE at the frame's gas: the size of the frame's return data, the tables'.
        obtain rfl := isRdsI_eq hrdi
        obtain ⟨-, hk1, hok3⟩ := blockOkC_rds hok2
        have hs := I'.seg
        rw [AssembleCallSeg.lowerInstrs_rds, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        obtain ⟨h2, m2, within2, hat2, hrun2⟩ :=
          AssembleCallSeg.rds_back hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
        have hv : ∀ T3 A3, T.Le T3 → A.Le A3 →
            (FO code T3 A3).env "returndatasize" s'.world [] = BitVec.ofNat 256 rd.size := by
          intro T3 A3 hle hleA
          have h1 := (hrd1 T3 A3 hle hleA).1
          simp only [returndataSize] at h1
          have hlt' : rd.size < 2 ^ 256 := by rw [← h1]; exact BitVec.isLt _
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt hlt']
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' + 1) []
          (some false :: ty') (k' - 1) (BitVec.ofNat 256 rd.size :: S')
          (BitVec.ofNat 256 rd.size :: T') s' (pc' + 1) M' (m.gas - 2) st' ss' rd T A m2 within2
          (by omega) hok3 (by simp; omega) (by simp; omega) List.nil_prefix
          (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top I'.mem R' hat2 hs1
          hrd1 (by unfold MemBudget at *; omega) hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .returndatasize 0 :: rest) S' s' = r
          rw [AssembleCallSeg.exec_rdsC (hv T3 A3 (hle2.trans hle) (hA2.trans hleA)) (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
      · -- RETURNDATACOPY at the frame's gas, of any range within the return data.
        obtain rfl := isRdcI_eq hrdci
        obtain ⟨-, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_rdc hok2
        have hs := I'.seg
        rw [AssembleCallSeg.lowerInstrs_rdc, List.cons_append] at hs
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
        obtain ⟨hfit, M2, g2, m2, within2, hmem2, hb2, hg2, hat2, hrun2⟩ :=
          AssembleCallSeg.rdc_dyn I'.mem hmB (by omega) (hrd1 T A (RunTable.Le.refl T)
            (CreateTable.Le.refl A)) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        have hext : ∀ T3 A3, T.Le T3 → A.Le A3 → returndataByte (FO code T3 A3) s'.world =
            returndataByte (FO code T A) s'.world := by
          intro T3 A3 hle hleA
          funext i
          simp only [returndataByte]
          rw [createTable_agree (baseF code) hle hleA (le_of_eq hs1.1.symm) (le_of_eq hs1.2.2.1.symm)
            (le_of_eq hs1.2.2.2.2.2.2.1.symm)]
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 3) [] (ty'.drop 3)
          (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => returndataByte (FO code T A) s'.world (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd
          T A m2 within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
          hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .returndatacopy 3 :: rest) _ s' = r
          rw [AssembleCallSeg.exec_rdcC (by rw [(hrd1 T3 A3 (hle2.trans hle) (hA2.trans hleA)).1]; exact hfit)
            (by omega), hext T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
      · -- CALL at the frame's gas: the callee's flag, output and the storage after join the table.
        obtain rfl := isCallI_eq hcalli
        obtain ⟨-, -, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_call hok2
        have hs := I'.seg
        rw [lowerInstrs_call, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, S''⟩⟩⟩⟩⟩⟩⟩
        all_goals (first | (simp at hh2; omega) | skip)
        rcases T' with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, _ | ⟨y7, Tr⟩⟩⟩⟩⟩⟩⟩
        all_goals (first | (simp at hL; done) | skip)
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 7) S'' Tr := by simpa using SR.drop 7 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨ok, out, s2, st2, ss2, M2, g2, m2, within2, hall, hw, hmem2, R2, hb2, hg2, hat2,
            hrun2⟩ : ∃ (ok : Bool) (out : ByteArray) (s2 : State) (st2 : State.TransactionState)
            (ss2 : Substate) (M2 : ByteArray) (g2 : Nat) (m2 : Evm .fusaka Nat)
            (within2 : GasMeter.gasHeld m2.gas ≤ bound),
            (∀ T'', (pushCall T ok out (storeOf st2 msg.currentTarget)).Le T'' →
              Effect.apply (tableOracle (baseF code) T'') call (.call .call)
                [x1, x2, x3, x4, x5, x6, x7] s' = some (some (if ok then 1 else 0), s2) ∧
                RdRel (tableOracle (baseF code) T'') s2.world out) ∧
            s2.world = callWorld s' x1 x2 x3 x4 x5 x6 x7 ∧ MemRel s2.memory M2 ∧
            Rel msg ss0 st2 ss2 s2 ∧ MemBudget G0 M2 g2 ∧ g2 ≤ m.gas ∧
            At code msg (pc' + 1) ((if ok then 1 else 0) :: Tr) M2 g2 st2 ss2 out m2 ∧
            runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m2 within2 = .ok fin := by
          by_cases hv : x3 = 0
          · subst hv
            obtain ⟨ok, out, s2, st2, ss2, M2, g2, m2, within2, hall, hw, hmem2, R2, hb2, hg2, hat2,
              hrun2⟩ := call0_cutQ (baseF code) T I'.mem R' hmB (by omega) hatm hlt hcode hstatic
                hdepth meets (hsites.call0 hatm hlt hcode hrm) within1 hrm hok
                hs1.2.1 hs1.2.2.1 hs1.2.2.2.1 hs1.2.2.2.2.1
            exact ⟨ok, out, s2, st2, ss2, M2, g2, m2, within2, fun T'' hle => hall T'' hle, hw,
              hmem2, R2, hb2, hg2, hat2, hrun2⟩
          · obtain ⟨cc, hcc, hdel, hq⟩ := hsites.callV hatm hlt hcode hv hrm
            obtain ⟨ok, out, s2, st2, ss2, M2, g2, m2, within2, hall, hw, hmem2, R2, hb2, hg2, hat2,
              hrun2⟩ := callValue_cutQ (baseF code) T I'.mem R' hmB (by omega) hatm hlt hcode hv
                hstatic hcc hdel hdepth meets hq
                within1 hrm hok hs1.2.1 hs1.2.2.1 hs1.2.2.2.1 hs1.2.2.2.2.1
            exact ⟨ok, out, s2, st2, ss2, M2, g2, m2, within2, fun T'' hle => hall T'' hle, hw,
              hmem2, R2, hb2, hg2, hat2, hrun2⟩
        have hle1 := le_pushCall T ok out (storeOf st2 msg.currentTarget)
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        have hT1 : TabF (pushCall T ok out (storeOf st2 msg.currentTarget)) A s2.world := by
          rw [hw]
          exact TabF.call hs1 ok out _ .call [x1, x2, x3] _ _ _
        have hRd1 : RdF code (pushCall T ok out (storeOf st2 msg.currentTarget)) A s2.world out := by
          intro T'' A'' h1 _
          have hl : lastCreate s2.world = false := by
            rw [hw]
            simp [callWorld, lastCreate, List.filter_append, Event.sends]
          exact rdRel_FO_of_table hl (hall T'' h1).2
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 6) []
          (some false :: ty'.drop 7) (k' - 1) ((if ok then 1 else 0) :: S'')
          ((if ok then 1 else 0) :: Tr) s2 (pc' + 1) M2 g2 st2 ss2 out _ A m2 within2 (by omega)
          hok3 (by simp; omega) (by simp; omega) List.nil_prefix (SR.cons (τ := some false) rfl hR'')
          hseg' (by simp; omega) hsz hmem2 R2 hat2 hT1 hRd1 hb2 hrun2
        refine ⟨T2, A2, r, hle1.trans hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle1.trans (hle2.trans hle)) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b
            (.effect (.call .call) 7 :: rest) _ s' = r
          have happ3 : Effect.apply (FO code T3 A3) call (.call .call) [x1, x2, x3, x4, x5, x6, x7] s' =
              some (some (if ok then 1 else 0), s2) := by
            rw [apply_call_createOracle]
            exact (hall T3 (hle2.trans hle)).1
          rw [exec_callC happ3 (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
      · -- CREATE2 at the frame's gas: its word, return data and the storage after join the
        -- creation table, and an entry at its message the run table.
        obtain rfl := isC2I_eq hc2i
        obtain ⟨-, -, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_c2 hok2
        have hs := I'.seg
        rw [lowerInstrs_c2, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, S''⟩⟩⟩⟩
        all_goals (first | (simp at hh2; omega) | skip)
        rcases T' with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, Tr⟩⟩⟩⟩
        all_goals (first | (simp at hL; done) | skip)
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 4) S'' Tr := by simpa using SR.drop 4 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        have hle1 := le_pushCall T false .empty (fun _ => 0)
        obtain ⟨r0, out, st2, ss2, M2, g2, m2, within2, hall, hmem2, R2, hb2, hg2, hat2, hrun2⟩ :=
          create2_cutQ (tableOracle (baseF code) (pushCall T false .empty (fun _ => 0))) A I'.mem R'
            hmB hG0 hatm hlt hcode hstatic meets (hsites.create2 hatm hlt hcode hrm)
            within1 hrm hok hs1.2.2.2.2.2.1 hs1.2.2.2.2.2.2.1 hs1.2.2.2.2.2.2.2
        have hleA1 := CreateTable.le_push A r0 out (storeOf st2 msg.currentTarget)
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        have hT1 : TabF (pushCall T false .empty (fun _ => 0))
            (A.push r0 out (storeOf st2 msg.currentTarget))
            (postCreate (tableOracle (baseF code) (pushCall T false .empty (fun _ => 0))) s'
              (storeOf st2 msg.currentTarget) x1 x2 x3 x4).world :=
          TabF.create hs1 r0 out _ [x1, x4] _ _ _
        have hRd1 : RdF code (pushCall T false .empty (fun _ => 0))
            (A.push r0 out (storeOf st2 msg.currentTarget))
            (postCreate (tableOracle (baseF code) (pushCall T false .empty (fun _ => 0))) s'
              (storeOf st2 msg.currentTarget) x1 x2 x3 x4).world out := by
          intro T'' A'' _ h2
          have hl : lastCreate (createWorld s' x1 x2 x3 x4) = true := by
            simp [createWorld]
          exact rdRel_FO_of_create hl (hall A'' h2).2
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 3) []
          (some false :: ty'.drop 4) (k' - 1) (r0 :: S'') (r0 :: Tr) _ (pc' + 1) M2 g2 st2 ss2 out _
          _ m2 within2 (by omega) hok3 (by simp; omega) (by simp; omega) List.nil_prefix
          (SR.cons (τ := some false) rfl hR'') hseg' (by simp; omega) hsz hmem2 R2 hat2 hT1 hRd1 hb2 hrun2
        refine ⟨T2, A2, r, hle1.trans hle2, hleA1.trans hA2, fun T3 A3 hle hleA => ?_, hpost,
          fun y hy => ?_⟩
        · rw [hex T3 A3 (hle1.trans (hle2.trans hle)) (hleA1.trans (hA2.trans hleA))]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .create2 4 :: rest) _ s' = r
          have hlA := (hA2.trans hleA).2.2.length_le
          simp only [CreateTable.push, List.length_append, List.length_singleton] at hlA
          have htr := hs1.2.2.2.2.1
          have hAst := hs1.2.2.2.2.2.2.2
          have hsent : sent s'.world < (pushCall T false .empty (fun _ => 0)).transients.length := by
            simp only [pushCall, List.length_append, List.length_singleton]
            omega
          have happ3 : Effect.apply (FO code T3 A3) call .create2 [x1, x2, x3, x4] s' =
              some (some r0, postCreate (tableOracle (baseF code) (pushCall T false .empty (fun _ => 0)))
                s' (storeOf st2 msg.currentTarget) x1 x2 x3 x4) := by
            rw [create2_table (hle2.trans hle) hsent (by omega)]
            exact (hall A3 (hA2.trans hleA)).1
          rw [exec_c2C happ3 (by omega)]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩
      · -- CODECOPY at the frame's gas, at the code offset the checker knows.
        obtain rfl := isCcI_eq hcci
        obtain ⟨-, -, ⟨x0, off0, t0, rfl, hoff⟩, hk1, hh1, hdat, htop', hok3⟩ := blockOkC_cc hok2
        have hs := I'.seg
        rw [lowerInstrs_cc, List.cons_append] at hs
        obtain ⟨next, hd, hseg'⟩ := hs.head
        simp only [Item.expected] at hd
        obtain ⟨hlt, hcode, rfl⟩ := op_item hd
        rcases S' with _ | ⟨x, _ | ⟨y, _ | ⟨z, S''⟩⟩⟩
        all_goals (first | (simp at hh2; omega) | skip)
        rcases T' with _ | ⟨x', _ | ⟨y', _ | ⟨z', Tr⟩⟩⟩
        all_goals (first | (simp at hL; done) | skip)
        obtain ⟨u, hu⟩ := hk2
        simp only [List.cons_append, List.cons.injEq] at hu
        obtain ⟨rfl, rfl, -⟩ := hu
        have htake := hR'.data hdat
        simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at htake
        obtain ⟨rfl, rfl, rfl, -⟩ := htake
        have hR'' : SR c (ty'.drop 3) S'' Tr := by simpa using SR.drop 3 hR'
        simp only [List.length_cons] at hL hst hh2 hu2
        obtain ⟨M2, g2, m2, within2, -, hmem2, R2, hb2, hg2, hat2, hrun2⟩ :=
          codecopy_cut (call := call) (FO_codeOk code T A) hoff I'.mem R' hmB hG0 hatm hlt hcode
            within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, A2, r, hle2, hA2, hex2, hpost, hnext⟩ := segF (G0 := G0) G hcr hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hsites n rest (h' - 3) []
          (ty'.drop 3) (k' - 1) S'' Tr _ (pc' + 1) M2 g2 st'
          ss' rd T A m2 within2 (by omega) hok3 (by omega) (by omega) List.nil_prefix hR'' hseg'
          (by omega) hsz hmem2 R2 hat2 hs1 hrd1 hb2 hrun2
        refine ⟨T2, A2, r, hle2, hA2, fun T3 A3 hle hleA => ?_, hpost, fun y hy => ?_⟩
        · rw [hex T3 A3 (hle2.trans hle) (hA2.trans hleA)]
          show SolarTV.EVM.Program.exec (FO code T3 A3) call b (.effect .codecopy 3 :: rest) _ s' = r
          rw [exec_codecopy (by omega), codeCopied_FO code T T3 A A3]
          exact hex2 T3 A3 hle hleA
        · obtain ⟨hy1, after, within', hE, hT, hrdy, hga, hbud, hra⟩ := hnext y hy
          exact ⟨hy1, after, within', hE, hT, hrdy, by omega, hbud, hra⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCreateSegF.segF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segF

end SolidCore.Refinement.Solar.AssembleCreateSegF

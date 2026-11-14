import SolidCore.Refinement.Solar.AssembleCallCut

/-!
# Code with STATICCALLs, block by block, at the frame's own gas

The checker without the certificate's no-call gate (`AssembleCut.checkCB`) cuts a block at each
STATICCALL (`AssembleCutSim.blockOkC`), and `segS` reads each segment back from a run that
succeeds as `AssembleCut.seg` does, with the run's table grown at each STATICCALL by the callee
frame's flag and output (`AssembleCallCut.staticcall_cut`). The oracle of a run's table is
`AssembleCallWorld.OS`: it answers the `n`-th STATICCALL to code from the table, and agrees with an
open world (`AssembleCallWorld.OS_agree`), so the composition with the source's specification
applies to it.

RETURNDATASIZE and RETURNDATACOPY are cuts too: `segS` keeps the return data of the frame related to
the oracle of every extension of the table (`AssembleEffects.RdRel`), so they read the last call's
output from the table, and a RETURNDATACOPY past the return data, which EthLib fails, is no run
that succeeds (`rdc_back`).

The final theorems name what they assume of the run, beside `AssembleCallCut.StaticOk`'s
`StaticNoLogs` and `OutputFits`:

* `CalleesOk`: at every STATICCALL of the run, the callee address is not a precompile's, or it is
  ECRECOVER's and `AssembleCallCut.PreOk` holds (the named `AssembleCallPre.EcrecoverAgree`, at
  least 3000 gas passed on, no delegation at address 1); then the source's answer gives the flag
  and return data and EthLib's ECRECOVER frame matches it. For calls to code it is a condition on
  the addresses the run calls only, not on any state: the callee's code (and, for an
  EIP-7702 delegation, its delegate's) is derived from the run succeeding
  (`AssembleCall.staticcall_routes_of_ok`), and delegated callees are covered
  (`AssembleCall.staticcall_back` follows EthLib's `callKindRoute` along any route).
-/

namespace SolidCore.Refinement.Solar.AssembleCallSeg

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

/-! ## The named hypothesis on the run's callees -/

/-- A STATICCALL to `addr` is answered by the run's table: `addr` is no precompile's address.
Nothing about the state: the callee's code and route come from the run (`staticcall_back`). -/
def CalleeOk (addr : U256) : Prop :=
  toCode .staticcall (addr.toNat % 2 ^ 160) 0 = true

/-- **Named hypothesis on a run**: every frame of the code that the run goes on from to `fin` and
that is at a STATICCALL calls an address that is no precompile's (`CalleeOk`), or calls ECRECOVER
(address 1) as `AssembleCallCut.PreOk` asks: under the named `AssembleCallPre.EcrecoverAgree`, with
an account at address 1 that is no delegation and at least 3000 gas passed on. -/
def CalleesOk (code : ByteArray) (msg : Message .fusaka)
    (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop) (bound : Nat)
    (runChild : MessageRunner .fusaka Nat bound) (fin : Evm .fusaka Nat) : Prop :=
  ∀ {e : Evm .fusaka Nat} {within : GasMeter.gasHeld e.gas ≤ bound} {pc : Nat}
    {asked addr inOff inSize outOff outSize : U256}
    {S : List U256} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray},
    At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: S) M g st ss rd e →
    (hlt : pc < code.size) → code[pc] = 0xfa →
    runFrame (step .fusaka) (step_decreases .fusaka) bound runChild e within = .ok fin →
    CalleeOk addr ∨ PreOk P st ss M g asked addr inOff inSize outOff outSize

/-- What the final theorems ask of the runner's callee frames: `StaticOk`, and EthLib's ECRECOVER
on priced messages to address 1 (proved, `AssembleCallPre.meets_ecrecover`). -/
def StaticOkE (caller : Evm .fusaka Nat) (m : Message .fusaka) (child : Evm .fusaka Nat) : Prop :=
  StaticOk caller m child ∧ AssembleCallPre.EcrecoverRuns caller m child

/-! ## The table and the frame's world -/

theorem sent_append (w v : List Event) : sent (w ++ v) = sent w + sent v := by
  simp [sent, List.filter_append]

theorem gasReads_append (w v : List Event) : gasReads (w ++ v) = gasReads w + gasReads v := by
  simp [gasReads, List.filter_append]

theorem machineCalls_append : ∀ w v : List Event, machineCalls (w ++ v) = machineCalls w ++ machineCalls v
  | [], v => rfl
  | e :: w, v => by
    cases e <;> simp [machineCalls, machineCalls_append w v]

/-- The table holds one flag and one output for each message the frame sent, and the frame's
messages are its calls. -/
def TabInv (T : RunTable) (w : List Event) : Prop :=
  sent w = T.oks.length ∧ (machineCalls w).length = T.oks.length ∧ T.outs.length = T.oks.length

theorem TabInv.of_seg {T : RunTable} {w w' : List Event} (hs : sent w' = sent w)
    (hm : machineCalls w' = machineCalls w) (h : TabInv T w) : TabInv T w' :=
  ⟨hs.trans h.1, by rw [hm]; exact h.2.1, h.2.2⟩

theorem TabInv.read {T : RunTable} {w : List Event} {n : String} (h : TabInv T w) :
    TabInv T (w ++ [.read n]) :=
  ⟨by rw [sent_append]; simpa using h.1, by rw [machineCalls_append]; simpa [machineCalls] using h.2.1,
    h.2.2⟩

theorem TabInv.log {T : RunTable} {w : List Event} {t : List Word} {d : List SolarTV.Memory.Byte}
    (h : TabInv T w) : TabInv T (w ++ [.log t d]) :=
  ⟨by rw [sent_append]; simpa using h.1, by rw [machineCalls_append]; simpa [machineCalls] using h.2.1,
    h.2.2⟩

/-- Under every extension of the table, a block runs as its segment under the table does, then
from the instruction the segment stopped at. -/
theorem exec_OS (codes : SolidCore.Solidity.Shared.Account.BytesMap) {T T'' : RunTable}
    (hle : T.Le T'') {call : Call} {b : Nat} {is : List Assemble.Instr} {S : List Word} {s : State}
    (hg : gasReads s.world ≤ T.gases.length) (hs : TabInv T s.world) :
    SolarTV.EVM.Program.exec (OS codes T'') call b is S s = match execC (OS codes T) call b is S s with
      | .done r => r
      | .cut i rest S' s' => SolarTV.EVM.Program.exec (OS codes T'') call b (i :: rest) S' s' := by
  rw [exec_eq_execC, ← (execC_agree (OS_agreeT codes hle (ng := T.gases.length)
    (ns := sent s.world) le_rfl (by rw [hs.1]) (by rw [hs.1, hs.2.2])) call b is S s hg le_rfl).1]
  rfl

theorem lowerInstrs_sc (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect (.call .staticcall) 6 :: rest) = .op 0xfa :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem exec_scC {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {a1 a2 a3 a4 a5 a6 w : Word} {S : List Word} {s s2 : State}
    (happ : Effect.apply o call (.call .staticcall) [a1, a2, a3, a4, a5, a6] s = some (some w, s2))
    (h : S.length < 1024) :
    SolarTV.EVM.Program.exec o call b (.effect (.call .staticcall) 6 :: rest)
        (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: S) s =
      SolarTV.EVM.Program.exec o call b rest (w :: S) s2 := by
  simp [SolarTV.EVM.Program.exec, happ, show ¬ 1024 < S.length + 1 by omega]


/-- GAS under the oracle of a table whose next gas is `v`. -/
theorem exec_gasS (codes : SolidCore.Solidity.Shared.Account.BytesMap) {T : RunTable} {call : Call}
    {b : Nat} {rest : List Assemble.Instr} {S : List Word} {s : State} {v : Nat}
    (hT : T.gases.getD (gasReads s.world) 0 = v) (hS : S.length < 1024) :
    SolarTV.EVM.Program.exec (OS codes T) call b (.effect .gas 0 :: rest) S s =
      SolarTV.EVM.Program.exec (OS codes T) call b rest (BitVec.ofNat 256 v :: S)
        { s with world := s.world ++ [.read "gas"] } := by
  have happ : Effect.apply (OS codes T) call .gas [] s =
      some (some (BitVec.ofNat 256 v), { s with world := s.world ++ [.read "gas"] }) := by
    simp only [Effect.apply]
    rw [gasOracle_gas, hT]
  simp [SolarTV.EVM.Program.exec, happ, show ¬ 1024 < S.length + 1 by omega]


theorem machineCalls_read (w : List Event) (n : String) :
    machineCalls (w ++ [.read n]) = machineCalls w := by
  rw [machineCalls_append]; simp [machineCalls]

theorem machineCalls_log (w : List Event) (t : List Word) (d : List SolarTV.Memory.Byte) :
    machineCalls (w ++ [.log t d]) = machineCalls w := by
  rw [machineCalls_append]; simp [machineCalls]

/-- The table's oracle reads a world, but GAS, only through the frame's calls. -/
theorem OS_env_world (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable)
    {w w' : List Event} (h : machineCalls w' = machineCalls w) {n : String} (hn : n ≠ "gas")
    (a : List Word) : (OS codes T).env n w' a = (OS codes T).env n w a := by
  simp only [OS, gasOracle, hn, false_and, ite_false]
  simp only [envOracle, ethOracle, tabOracle_envEq, tabEnv, h]

/-- The return data the table's oracle answers stays while the frame makes no call. -/
theorem rdRel_world (codes : SolidCore.Solidity.Shared.Account.BytesMap) {T : RunTable}
    {w w' : List Event} {rd : ByteArray} (h : machineCalls w' = machineCalls w)
    (hr : RdRel (OS codes T) w rd) : RdRel (OS codes T) w' rd := by
  obtain ⟨h1, h2⟩ := hr
  refine ⟨?_, fun i hi => ?_⟩
  · have := OS_env_world codes T h (n := "returndatasize") (by decide) []
    simp only [returndataSize] at h1 ⊢
    rw [this]; exact h1
  · have := OS_env_world codes T h (n := "returndata") (by decide) [BitVec.ofNat 256 i]
    have h3 := h2 i hi
    simp only [returndataByte] at h3 ⊢
    rw [this]; exact h3

/-- Before any call, the table's oracle answers no return data. -/
theorem rdRel_nil (codes : SolidCore.Solidity.Shared.Account.BytesMap) (T : RunTable) :
    RdRel (OS codes T) [] ByteArray.empty :=
  ⟨by simp [returndataSize, OS, gasOracle, envOracle, ethOracle, tabOracle_envEq, tabEnv, machineCalls,
    envRead], fun i hi => by simp at hi⟩

theorem lowerInstrs_rds (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .returndatasize 0 :: rest) = .op 0x3d :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem exec_rdsC {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {S : List Word} {s : State} {v : Word} (hv : o.env "returndatasize" s.world [] = v)
    (h : S.length < 1024) :
    SolarTV.EVM.Program.exec o call b (.effect .returndatasize 0 :: rest) S s =
      SolarTV.EVM.Program.exec o call b rest (v :: S) s := by
  simp [SolarTV.EVM.Program.exec, SolarTV.Machine.Effect.apply, hv, show ¬ 1024 < S.length + 1 by omega]

/-- RETURNDATASIZE (EIP-211) pushes the size of the frame's return data, for 2 gas. -/
theorem returndatasize_rule {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {stack : List U256}
    {memory : ByteArray} {gas : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare .fusaka (At code msg pc stack memory gas st ss rd)
      (At code msg (pc + 1) (BitVec.ofNat 256 rd.size :: stack) memory (gas - 2) st ss rd) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .returndatasize) rfl (by decide)) rfl
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [readFrame_of_length_lt (by rw [hst]; exact hstack),
    charge_nat (by rw [hg, show OPCODE_RETURNDATASIZE = 2 from rfl]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, hmem, by simp [hg, OPCODE_RETURNDATASIZE, BASE],
    hrun, herr, hout, hs, hss, hrd⟩
  simp [hst, hg, hrd, OPCODE_RETURNDATASIZE, BASE, GasMeter.gasLeft]

/-- **RETURNDATASIZE in a run that succeeds**: the frame had the gas for it, and the run goes on
from the frame after it, with the size of its return data pushed. -/
theorem rds_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {T : List Word}
    {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {evm : Evm .fusaka Nat} (hat : At code msg pc T M g st ss rd evm) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3d) (hstack : T.length < STACK_LIMIT) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
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
    rw [hf.2.1] at hok
    cases hok


/-- The table's oracle and that of any extension answer alike, but GAS, at a world whose calls the
table answers. -/
theorem OS_env_ext (codes : SolidCore.Solidity.Shared.Account.BytesMap) {T T3 : RunTable}
    (hle : T.Le T3) {w : List Event} (hm : (machineCalls w).length ≤ T.oks.length)
    (hm' : (machineCalls w).length ≤ T.outs.length) (hg : gasReads w ≤ T.gases.length)
    {n : String} (hn : n ≠ "gas") (a : List Word) :
    (OS codes T3).env n w a = (OS codes T).env n w a := by
  by_cases h0 : (machineCalls w).length = 0
  · have hnil : machineCalls w = [] := List.eq_nil_of_length_eq_zero h0
    simp only [OS, gasOracle, hn, false_and, ite_false]
    simp only [envOracle, ethOracle, tabOracle_envEq, tabEnv, hnil]
    split <;> simp_all
  · exact (OS_le (codes := codes) hle hm hm' (by omega) (by omega) hg).1 n a

theorem instruction_returndatacopy :
    instruction (Meter := Nat) .fusaka .returndatacopy = some returndatacopyStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- RETURNDATACOPY (EIP-211) of a range within the return data: 3, 3 gas a word and the growth of
memory, then the bytes of the return data written. -/
theorem returndatacopy_rule {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {start offset size : U256} {rest : List U256} {memory : ByteArray} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) (hfit : offset.toNat + size.toNat ≤ rd.size)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare .fusaka (At code msg pc (start :: offset :: size :: rest) memory gas st ss rd)
      (At code msg (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat (memoryReadBytes rd offset.toNat size.toNat))
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        st ss rd) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .returndatacopy) rfl (by decide))
    instruction_returndatacopy
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss, hrd⟩
  rw [returndatacopyStep_cons hst (by rw [hrd]; exact hfit)]
  dsimp only
  rw [show OPCODE_RETURNDATACOPY_BASE = 3 from rfl, show OPCODE_RETURNDATACOPY_PER_WORD = 3 from rfl,
    hmem, hg, hrd, charge_nat hgas]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun', herr, hout, hs, hss, rfl⟩

/-- RETURNDATACOPY that cannot pay fails out of gas. -/
theorem returndatacopyStep_oog {e : Evm .fusaka Nat} {d off sz : U256} {T : List U256}
    (h : e.stack.val = d :: off :: sz :: T)
    (hc : GasMeter.charge e.gas (OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD *
      wordCount sz.toNat + (extendMemory e.memory.size [(d, sz)]).cost) = .error .outOfGas) :
    returndatacopyStep e = .error .outOfGas := by
  have hstack : e.stack = ⟨d :: off :: sz :: T, h ▸ e.stack.property⟩ := Subtype.ext h
  simp only [returndatacopyStep, popWord, chargeGas, hstack, Stack.pop]
  simp [hc, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- **RETURNDATACOPY in a run that succeeds**: the range was within the return data, the frame had
the gas for the copy and the growth of memory, and the run goes on from the frame after it. -/
theorem rdc_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
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
        rw [step_of_instruction hlt (by rw [hbyte]; exact decoded) instruction_returndatacopy]
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
      rw [hf.2.1] at hok
      cases hok
  · exfalso
    have hspec : Spec .fusaka (At code msg pc (d :: off :: sz :: T) M g st ss rd)
        (Faulted .outOfGas st ss) := by
      refine At.fault rfl fun e hat' => ?_
      obtain ⟨hcode, -, -, hpc, hst, hmem, hgas, -⟩ := hat'
      subst hcode hpc
      rw [step_of_instruction hlt (by rw [hbyte]; exact decoded) instruction_returndatacopy]
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
    rw [hf.2.1] at hok
    cases hok

/-- **RETURNDATACOPY of any range, in a run that succeeds**: with the budget below `2 ^ 300` and an
oracle that answers the frame's return data, SolarTV's copy agrees with EthLib's memory after it,
the budget holds at the gas left, and the run goes on. -/
theorem rdc_dyn {code : ByteArray} {msg : Message .fusaka} {o : Oracle} {w : List Event}
    {pc : Nat} {d off sz : Word} {T : List Word} {M : ByteArray} {g G : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} {m0 : SolarTV.Machine.Mem}
    (hm : MemRel m0 M) (hb : MemBudget G M g) (hG : G < 2 ^ 300) (hrdr : RdRel o w rd)
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    off.toNat + sz.toNat ≤ rd.size ∧
    ∃ (M' : ByteArray) (g' : Nat) (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      MemRel (m0.write d.toNat sz.toNat (fun i => returndataByte o w (off.toNat + i))) M' ∧
      MemBudget G M' g' ∧ g' ≤ g ∧ At code msg (pc + 1) T M' g' st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin := by
  obtain ⟨hfit0, hg, m, within', hat', hrun'⟩ := rdc_back hat hlt hbyte within hrun hok
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

theorem lowerInstrs_rdc (p : Assemble.Program) (c : Cert) (b : Nat) (rest : List Assemble.Instr) :
    lowerInstrs p c b (.effect .returndatacopy 3 :: rest) = .op 0x3e :: lowerInstrs p c b rest := by
  simp [lowerInstrs, turnedElse, dropped, lowerInstr]

theorem exec_rdcC {o : Oracle} {call : Call} {b : Nat} {rest : List Assemble.Instr}
    {d off sz : Word} {S : List Word} {s : State}
    (hfit : off.toNat + sz.toNat ≤ (o.env "returndatasize" s.world []).toNat) (h : S.length ≤ 1024) :
    SolarTV.EVM.Program.exec o call b (.effect .returndatacopy 3 :: rest) (d :: off :: sz :: S) s =
      SolarTV.EVM.Program.exec o call b rest S { s with
        memory := s.memory.write d.toNat sz.toNat (fun i => returndataByte o s.world (off.toNat + i)) } := by
  have hn : ¬ (o.env "returndatasize" s.world []).toNat < off.toNat + sz.toNat := by omega
  simp [SolarTV.EVM.Program.exec, SolarTV.Machine.Effect.apply, hn, show ¬ 1024 < S.length by omega]

/-! ## A block, segment by segment, with STATICCALLs -/

set_option maxRecDepth 8000 in
/-- **`AssembleCut.seg` with STATICCALLs**: the rest of a block from an instruction, read back from
a run that succeeds, under the oracle of the run's table of GAS reads and static calls. -/
theorem segS {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobT p c code) (codes : SolidCore.Solidity.Shared.Account.BytesMap) (hcr : c.creates = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    {b : Nat} (hb : b < p.blocks.length) {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    {fin : Evm .fusaka Nat} (hok : fin.error = none) {G0 : Nat} (hG0 : G0 < 2 ^ 256)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop} (meets : Meets P runChild)
    (hPok : ∀ c m ch, P c m ch → StaticOk c m ch)
    (hcal : CalleesOk code msg P bound runChild fin) :
    ∀ (n : Nat) (is : List Assemble.Instr) (h : Nat) (known : List Word) (ty : List Ty) (k : Nat)
      (S Tw : List Word) (s : State) (pc : Nat) (M : ByteArray) (g : Nat)
      (st : State.TransactionState) (ss : Substate) (rd : ByteArray) (T : RunTable) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound),
      is.length < n → blockOkC p c mx b h known ty k is = true → h ≤ S.length →
      S.length + c.need b ≤ h + maxH mx b → known <+: S → SR c ty S Tw →
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
      obtain ⟨m, within1, hz, hrm⟩ := reaches_low r1 K evm rfl within hrun hok
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
          gas_back hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
        let T1 : RunTable := { T with gases := T.gases ++ [m.gas - 2] }
        have hle1 : T.Le T1 := ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_append _ _⟩
        have hv : ∀ T'', T1.Le T'' → T''.gases.getD (gasReads s'.world) 0 = m.gas - 2 := by
          intro T'' hle
          rw [getD_of_prefix hle.2.2.2.2 (by simp [T1]; omega)]
          simp [T1, List.getD_eq_getElem?_getD, hc1.1, ← hTg]
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself hcaller hbenv
          htx hb hok hG0 hdepth meets hPok hcal n rest (h' + 1) [] (some false :: ty') (k' - 1)
          (BitVec.ofNat 256 (m.gas - 2) :: S') (BitVec.ofNat 256 (m.gas - 2) :: T')
          { s' with world := s'.world ++ [.read "gas"] } (pc' + 1) M' (m.gas - 2) st' ss' rd T1 m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
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
          AssembleDyn.mload_dyn I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest h' [] (some false :: ty'.drop 1) (k' - 1)
          (s'.memory.load x.toNat :: S'') (s'.memory.load x.toNat :: Tr)
          { s' with memory := s'.memory.expand x.toNat 32 } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
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
          AssembleDyn.mstore_dyn I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 2) [] (ty'.drop 2) (k' - 1) S'' Tr
          { s' with memory := s'.memory.store x.toNat y } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
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
        obtain ⟨-, hkec⟩ := (OS_ok codes c T).1 henv
        rw [byteArray_eq_of_map (read_eq I'.mem), ← hkec] at hat2
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 1) [] (some false :: ty'.drop 2) (k' - 1)
          ((OS codes T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: S'')
          ((OS codes T).keccak ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat) :: Tr)
          { s' with memory := s'.memory.expand x.toNat y.toNat } (pc' + 1) _ _ st' ss' rd T m2
          within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl (by simpa using hR'')) hseg'
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
          AssembleDyn.log_dyn (n := ⟨tops.length, by omega⟩) I'.mem hmB (by omega) hatm rfl hlt hcode
            (decode_log ⟨tops.length, by omega⟩) hstatic within1 hrm hok
        have hsz : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size ≤ c.top := by
          have hmod : (memoryExtend M' (extendMemory M'.size [(x, y)]).expandBy).size % 32 = 0 := by
            rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨L, hL1, hL2⟩ := R'.logs
        obtain ⟨T2', r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) (ss0 := ss0) G codes (hcr := hcr) hdata hvalue hstatic hself
          hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - (tops.length + 2)) [] (ty'.drop (tops.length + 2))
          (k' - 1) S2 T2
          ⟨s'.memory.expand x.toNat y.toNat, s'.storage, s'.transient,
            s'.world ++ [.log tops ((s'.memory.expand x.toNat y.toNat).read x.toNat y.toNat)]⟩
          (pc' + 1) _ _ st' { ss' with logs := ss'.logs.push ⟨msg.currentTarget,
            tops.map U256.toBeBytes, memoryReadBytes (memoryExtend M' (extendMemory M'.size
              [(x, y)]).expandBy) x.toNat y.toNat⟩ } rd T m2 within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2
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
          AssembleDynCopy.cdc_dyn hdata I'.mem hmB (by omega) hatm hlt hcode within1 hrm hok
        have hsz : M2.size ≤ c.top := by
          have hmod : M2.size % 32 = 0 := by rw [hmem2.1]; omega
          have := size_le_of_cost (B := G0) (by unfold MemBudget at hb2; omega) hG0 hmod
          omega
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) (ss0 := ss0) G codes (hcr := hcr) hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 3) [] (ty'.drop 3) (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => SolarTV.Machine.calldataByte call (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd T m2
          within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
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
          R2, hb2, hg2, hat2, hrun2⟩ := staticcall_cut codes T I'.mem R' hmB (by omega) hatm hlt hcode
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
          · rw [hw, sent_append, hev1, hc1.2, hi1]
            simp [T1]
          · rw [hw, machineCalls_append, List.length_append, hev3, hmc, hi2]
            simp [T1]
          · simp [T1, hi3]
        have hTg1 : T1.gases.length = gasReads s2.world := by
          rw [hw, gasReads_append, hev2, hc1.1]
          simpa [T1] using hTg
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic
          hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 5) []
          (some false :: ty'.drop 6) (k' - 1) ((if ok then 1 else 0) :: S'')
          ((if ok then 1 else 0) :: Tr) s2 (pc' + 1) M2 g2 st2 ss2 out T1 m2 within2 (by omega) hok3
          (by simp; omega) (by simp; omega) List.nil_prefix (SR.cons (τ := some false) rfl hR'')
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
          rds_back hatm hlt hcode (by unfold STACK_LIMIT; omega) within1 hrm hok
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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue hstatic
          hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' + 1) [] (some false :: ty')
          (k' - 1) (BitVec.ofNat 256 rd.size :: S') (BitVec.ofNat 256 rd.size :: T') s' (pc' + 1) M'
          (m.gas - 2) st' ss' rd T m2 within2 (by omega) hok3 (by simp; omega) (by simp; omega)
          List.nil_prefix (SR.cons (τ := some false) rfl hR') hseg' (by simp; omega) I'.le_top
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
          rdc_dyn I'.mem hmB (by omega) (hrd' T (RunTable.Le.refl T)) hatm hlt hcode within1 hrm hok
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
        obtain ⟨T2, r, hle2, hex2, hpost, hnext⟩ := segS (G0 := G0) G codes (hcr := hcr) hdata hvalue
          hstatic hself hcaller hbenv htx hb hok hG0 hdepth meets hPok hcal n rest (h' - 3) [] (ty'.drop 3)
          (k' - 1) S'' Tr
          { s' with
            memory := s'.memory.write x.toNat z.toNat
              (fun i => returndataByte (OS codes T) s'.world (y.toNat + i)) } (pc' + 1) M2 g2 st' ss' rd
          T m2 within2 (by omega) hok3 (by omega) (by omega)
          List.nil_prefix hR'' hseg' (by omega) hsz hmem2 ⟨R'.storage, R'.account, R'.logs⟩ hat2
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

/-- info: 'SolidCore.Refinement.Solar.AssembleCallSeg.segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segS


/-! ## Runs under a runner meeting an assumption, with a hypothesis on the run -/

section BlocksQ

variable {σ : Type} (blk : Oracle → σ → Option ((Halt × Machine.State) ⊕ σ))
  (O : RunTable → Oracle)

/-- **One block of the simulation, read back from a run that succeeds**, as
`AssembleCall.AdvancesS` under every runner of messages meeting `P`, for the runs to a frame `fin`
that meet the hypothesis `Q`. -/
def AdvancesQ (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : RunTable → σ → Evm .fusaka Nat → Prop)
    (Post : Halt × Machine.State → Evm .fusaka Nat → Prop) (meas : σ → Evm .fusaka Nat → Nat)
    (T : RunTable) (x : σ) (evm : Evm .fusaka Nat) : Prop :=
  ∀ (bound : Nat) (runChild : MessageRunner .fusaka Nat bound), Meets P runChild →
    ∀ (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none → Q bound runChild fin →
      ∃ T' r, T.Le T' ∧ (∀ T'', T'.Le T'' → blk (O T'') x = some r) ∧
        (∀ res, r = .inl res → Post res fin) ∧
        (∀ y, r = .inr y → ∃ after within', E T' y after ∧ meas y after < meas x evm ∧
          runFrame (step .fusaka) (step_decreases .fusaka) bound runChild after within' = .ok fin)

/-- A run of EthLib that ends with no error and meets the hypothesis is SolarTV's, for every table
extending the last one the run grew. -/
theorem run_of_advancesQ {P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop}
    {Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop}
    {E : RunTable → σ → Evm .fusaka Nat → Prop}
    {Post : Halt × Machine.State → Evm .fusaka Nat → Prop} {meas : σ → Evm .fusaka Nat → Nat}
    (adv : ∀ T x evm, E T x evm → AdvancesQ blk O P Q E Post meas T x evm)
    {bound : Nat} {runChild : MessageRunner .fusaka Nat bound}
    (meets : Meets P runChild) :
    ∀ (n : Nat) (T : RunTable) (x : σ) (evm : Evm .fusaka Nat)
      (within : GasMeter.gasHeld evm.gas ≤ bound) (fin : Evm .fusaka Nat),
      E T x evm → meas x evm < n →
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin →
      fin.error = none → Q bound runChild fin →
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
        run_of_advancesQ adv meets n T' y after within' fin hE' (by omega) hrun' hok hq
      refine ⟨T2, res, hle.trans hle2, fun T'' h => ?_, hpost⟩
      obtain ⟨k, hk⟩ := hit T'' h
      exact ⟨k + 1, by simp [SolarTV.Machine.iterate, hstep T'' (hle2.trans h), hk]⟩

end BlocksQ

section Runs

open EthLib.Execution.State

open SolarTV.EVM.Program SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm.Symex in
/-- **EVM IR to bytecode at the given gas, run by run, from a block simulation**: when every frame
related to a block state (`E`, from the substate the frame started with) advances (`Advances`) to
an end SolarTV's halt shows (`PostL`) or to the next block, and the frame a call starts with is
related to SolarTV's initial state, then the oracle of the run's table makes every result of the
bytecode on the call the EVM IR's or a failure that changes nothing. -/
theorem within_of_advancesQ {p : Assemble.Program} {code : ByteArray} {call : Call} {gas : Nat}
    (O : RunTable → Oracle) (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (Q : (bound : Nat) → MessageRunner .fusaka Nat bound → Evm .fusaka Nat → Prop)
    (E : Substate → RunTable → Nat × List Word × Machine.State → Evm .fusaka Nat → Prop)
    (meas : Nat × List Word × Machine.State → Evm .fusaka Nat → Nat)
    (hP : Meets P (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas))
    (hQ : ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
        (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
      Q _ (processRunner .fusaka (Meter := Nat) (Final.Target.messageWith gas code call).gas) r.1)
    (start : ∀ st' ss', Rel (Final.Target.messageWith gas code call) ss' st' ss'
        (Machine.State.initial call) →
      E ss' {} (0, [], Machine.State.initial call)
        (startFrame (Final.Target.messageWith gas code call) st' ss' gas))
    (adv : ∀ ss0 T x evm, E ss0 T x evm → AdvancesQ (fun o => block o call p) O P Q (E ss0)
      (fun res => PostL call (Final.Target.messageWith gas code call).currentTarget ss0 res.2 res.1)
      meas T x evm) :
    ∃ T, Within (evmirSem (O T)) (ethLibWith gas) p code (· = call) := by
  by_cases hs : ∃ obs, Target.runWith gas code call = some obs ∧ obs.success = true
  swap
  · refine ⟨{}, fun call' hc obs hrun => Or.inr ?_⟩
    subst hc
    have hf : obs.success = false := by
      cases h : obs.success
      · rfl
      · exact absurd ⟨obs, hrun, h⟩ hs
    exact ⟨hf, Target.runWith_failure hrun hf⟩
  obtain ⟨obs, hrun, hsucc⟩ := hs
  suffices H : ∃ T, (evmirSem (O T)).run p call = some obs by
    obtain ⟨T, hT⟩ := H
    refine ⟨T, fun call' hc obs' hrun' => Or.inl ?_⟩
    subst hc
    change Target.runWith gas code call' = some obs' at hrun'
    rw [hrun] at hrun'
    cases hrun'
    exact hT
  unfold Target.runWith Target.runMsg at hrun
  split at hrun
  · cases hrun
  rename_i evm hev hpm
  simp only [Option.some.injEq] at hrun
  subst hrun
  have hok : evm.error = none := by simpa using hsucc
  obtain ⟨st', ss', within, hcases, hmove, hrf⟩ :=
    AssembleRun.processMessage_ok' (message := Final.Target.messageWith gas code call) (evm := ⟨evm, hev⟩)
      (precompileAddress_message code call) hpm hok
  simp only at hrf
  have R := AssembleLoop.rel_start code call gas ss' (fun h => (hcases h).1) (fun h => (hmove h).1)
  obtain ⟨T, ⟨halt, sF⟩, -, hit, hpost⟩ := run_of_advancesQ (fun o => block o call p) O (adv ss')
    hP _ {} _ _ within evm (start st' ss' R) (Nat.lt_succ_self _) hrf hok (hQ _ hpm hok)
  obtain ⟨k, hk⟩ := hit T (RunTable.Le.refl T)
  refine ⟨T, ?_⟩
  have hres : (evmirSem (O T)).run p call = some (observe call sF halt) := by
    change (SolarTV.EVM.Program.layer.result (O T) p call).map _ = _
    rw [SolarTV.EVM.Program.layer.result_of_ends ⟨k, hk⟩]
    rfl
  rw [hres]
  set msg := Final.Target.messageWith gas code call with hmsg
  obtain ⟨ssF, ⟨herr, hout, hlogsF, hst⟩, L, hL1, hL2⟩ := hpost
  have hss' : ss'.logs.toList = [] := by
    by_cases htr : msg.shouldTransferValue = true ∧ msg.value ≠ 0
    · rw [(hmove htr).2]
      simp [pushTransferLog, show ¬ (Fork.fusaka ≥ Fork.glamsterdam) by decide, Substate.empty]
    · rw [(hcases htr).2]
      simp [Substate.empty]
  have hlogs := logs_of_match hL2
  have hL1' : ssF.logs.toList = L := by rw [hL1, hss', List.nil_append]
  have herr' : evm.error = errorOf (observe call sF halt) := herr
  have hout' : evm.output.toList.map (·.toNat) = (observe call sF halt).output := hout
  have hst' : (observe call sF halt).success = true →
      evm.substate.logs = ssF.logs ∧ ∀ slot,
        (evm.state.getStorage (Target.address selfAddress) (Target.storageKey slot)).toNat =
          (observe call sF halt).storage slot :=
    fun h => ⟨hlogsF, hst h⟩
  have hfail : (observe call sF halt).success = false →
      (observe call sF halt).logs = [] ∧
      (observe call sF halt).storage = slotValue call.storage := by
    cases halt <;> simp [observe]
  have hok2 : (observe call sF halt).success = true →
      (observe call sF halt).logs = logs sF := by
    cases halt <;> simp [observe]
  clear herr hout hst hres hit hk
  generalize observe call sF halt = X at *
  have hsucc' : evm.error.isNone = X.success := by
    rw [herr']; cases hX : X.success <;> simp [errorOf, hX]
  symm
  congr 1
  cases X with
  | mk success output logs storage =>
    simp only at hsucc' hout' hfail hok2 hst' ⊢
    rw [SolarTV.Observable.mk.injEq]
    refine ⟨hsucc', hout', ?_, ?_⟩
    · rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        rw [(hst' hs).1, hL1', hlogs, hok2 hs]
        rfl
    · funext slot
      rw [hsucc']
      cases hs : success
      · simp [hok, hs] at hsucc'
      · simp only [ite_true]
        exact (hst' hs).2 slot


end Runs

/-! ## The checker with STATICCALLs -/

/-- The relation at a block entry, with the table's GAS reads and one flag and output per message
sent. -/
def EntS (codes : SolidCore.Solidity.Shared.Account.BytesMap) (p : Assemble.Program) (c : Cert) (mx : List Nat) (code : ByteArray)
    (msg : Message .fusaka) (ss0 : Substate) (T : RunTable) (x : Nat × List Word × State)
    (evm : Evm .fusaka Nat) : Prop :=
  EntC p c mx code msg ss0 x evm ∧ T.gases.length = gasReads x.2.2.world ∧ TabInv T x.2.2.world ∧
    (∀ T'', T.Le T'' → RdRel (OS codes T'') x.2.2.world evm.returnData) ∧
    memoryGasCost evm.memory.size + evm.gas ≤ msg.gas

/-- **A block of code with loops, GAS and STATICCALLs, read back from a run that succeeds.** -/
theorem advances_checkCS {p : Assemble.Program} {c : Cert} {mx : List Nat} {code : ByteArray}
    (G : GlobC p c mx code) (codes : SolidCore.Solidity.Shared.Account.BytesMap) (hcr : c.creates = false) {call : Call} {msg : Message .fusaka} {ss0 : Substate}
    (hdata : msg.data = call.calldata) (hvalue : msg.value = BitVec.ofNat 256 call.callvalue)
    (hstatic : msg.isStatic = false) (hself : msg.currentTarget = Target.address selfAddress)
    (hcaller : msg.caller = Target.address callerAddress)
    (hbenv : msg.blockEnv = Target.blockEnv) (htx : msg.txEnv = Target.txEnv)
    (hgas : msg.gas < 2 ^ 256) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (T0 : RunTable) (x : Nat × List Word × State) (evm : Evm .fusaka Nat)
    (hE : EntS codes p c mx code msg ss0 T0 x evm) :
    AdvancesQ (fun o => SolarTV.EVM.Program.block o call p) (OS codes) StaticOkE
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
        obtain ⟨m, within', hz, hrm⟩ := reaches_low r1 1 evm rfl within hrun hok
        rw [hz] at he1
        obtain ⟨hatm, hgm⟩ := at_of_addGasR he1
        exact ⟨pc + 1, m, within', hatm, hseg', by simp only [ht, ite_true]; omega, hrm⟩
      · simp only [ht, Bool.false_eq_true, ite_false, List.nil_append] at hseg
        exact ⟨pc, evm, within, hat, hseg, by simp only [ht, Bool.false_eq_true, ite_false]; omega,
          hrun⟩
    obtain ⟨T', r, hle', hex, hpost, hnext⟩ := segS (G0 := msg.gas) G.toGlobT codes (hcr := hcr) hdata hvalue hstatic hself hcaller
      hbenv htx hb hok hgas hdepth meets (fun _ _ _ h => h.1) hcal (p.blocks[b].length + 1) p.blocks[b] (c.need b) [] (c.entry b)
      (budget c b - labelItems p c b) S Tw s pc1 M m1.gas st ss rd T0 m1 within1 (Nat.lt_succ_self _)
      hblock hn (by omega) List.nil_prefix hR hseg1 (by omega) htop hmem R hat1 hTg hs0
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
      exact SpecG.low (SpecG.consequence (stop_of_size_leG (by omega))
        (fun _ h => h) fun evm h => postL_stop R hself evm h) (hat.addGas 0) within hrun hok
    · intro y hy
      cases hy

/-- **Named hypothesis on a run of the bytecode**: the run of the call, when it succeeds, calls code
at each STATICCALL (`CalleesOk`). -/
def CalleesRun (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
    CalleesOk code (Final.Target.messageWith gas code call) StaticOkE gas (processRunner .fusaka (Meter := Nat) gas) r.1

/-- **Named hypotheses on the runner of messages**: a static message that succeeds ends with no log
(EIP-214), and a callee's output has fewer than `2 ^ 256` bytes. -/
def StaticRunner (gas : Nat) : Prop :=
  Meets (bound := gas) (fun caller m child => StaticNoLogs caller m child ∧ OutputFits caller m child)
    (processRunner .fusaka (Meter := Nat) gas)

theorem staticOk_of (gas : Nat) (h : StaticRunner gas) :
    Meets (bound := gas) StaticOk (processRunner .fusaka (Meter := Nat) gas) :=
  ⟨fun a b c d e => ⟨(meets_static gas).ok a b c d e, h.ok a b c d e⟩, h.aborts⟩

theorem staticOkE_of (gas : Nat) (h : StaticRunner gas) :
    Meets (bound := gas) StaticOkE (processRunner .fusaka (Meter := Nat) gas) :=
  ⟨fun a b c d e => ⟨(staticOk_of gas h).ok a b c d e, (AssembleCallPre.meets_ecrecover gas).ok a b c d e⟩,
    h.aborts⟩

/-- **EVM IR to bytecode, run by run, for code with loops, GAS, memory at any offset and
STATICCALLs to code**: for every program the checker without the no-call gate accepts, at every
gas below `2 ^ 256` and every call whose run meets the named hypotheses, the oracle of the run's
table (`OS`: the static calls' flags and outputs, the GAS reads) makes every result of the bytecode
the EVM IR's or a failure that changes nothing. -/
theorem runs_of_checkCB {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCB p code c mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (gas : Nat) (hgas : gas < 2 ^ 256) (call : Call) (hP : StaticRunner gas)
    (hQ : CalleesRun gas code call) :
    ∃ T, Within (evmirSem (OS codes T)) (ethLibWith gas) p code (· = call) := by
  obtain ⟨G, hseg, hneed0⟩ := globC_of_checkC hc
  refine within_of_advancesQ (OS codes) StaticOkE
    (CalleesOk code (Final.Target.messageWith gas code call) StaticOkE)
    (fun ss0 => EntS codes p c mx code (Final.Target.messageWith gas code call) ss0)
    (fun y e => AssembleLoop.meas p c e.gas y.1) (staticOkE_of gas hP) hQ (fun st' ss' R => ?_)
    (fun ss0 T x evm hE => advances_checkCS G codes (hcr := checkCB_creates hc) rfl
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

/-- **The assembly premise of `holds_of_runs` for code with STATICCALLs**: below `2 ^ 256` gas, for
every call in scope whose run meets the named hypotheses, an oracle and an open world that agree
(`AssembleCallWorld.tabWorld` answers the static calls from the run's table), under which the EVM IR
gives the bytecode's result or a failure that changes nothing. -/
theorem assembly_of_checkCB {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCB p code c mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : Call → Prop) (hP : ∀ gas, StaticRunner gas)
    (hQ : ∀ gas call, scope call → CalleesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : Oracle) (W : World), W.Open ∧
      CallsAgree o W ∧ CertOk c o ∧ Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hs
  obtain ⟨T, hT⟩ := runs_of_checkCB hc codes gas hgas call (hP gas) (hQ gas call hs)
  exact ⟨OS codes T, tabWorld T.oks T.outs codes, (OS_agree codes T).1, (OS_agree codes T).2,
    OS_ok codes c T, hT⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCallSeg.assembly_of_checkCB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembly_of_checkCB


/-- **The specification of SolidCore to the exact bytecode, for code with STATICCALLs**: the
source's specification at every open world, its totality on the calls in scope, the stages to EVM
IR and the checker without the no-call gate give the specification of the bytecode at every gas
below `2 ^ 256`, for the runs meeting the named hypotheses `StaticRunner` and `CalleesRun`. -/
theorem holds_of_checkCB {St : Type} {fuel : Nat}
    {mirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : ∀ o, (mirSem o).Prog} {p : Assemble.Program} {code : ByteArray} {cert : Cert}
    {mx : List Nat} {spec : Final.ContractSpec St}
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : ∀ o W, CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (mir o) spec.Calls)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (mir o) p spec.Calls)
    (hc : checkCB p code cert mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (hP : ∀ gas, StaticRunner gas) (hQ : ∀ gas call, spec.Calls call → CalleesRun gas code call)
    (gas : Nat) (hgas : gas < 2 ^ 256) : Final.Holds (Final.ethLibWith gas) code spec :=
  holds_of_runs_lt (evmirSem := evmirSem) (evmir := fun _ => p) source fin lowering backend
    (fun gas hg call hcall => by
      obtain ⟨o, W, h1, h2, -, h4⟩ := assembly_of_checkCB hc codes spec.Calls hP hQ gas hg call hcall
      exact ⟨o, W, h1, h2, h4⟩) gas hgas

/-- info: 'SolidCore.Refinement.Solar.AssembleCallSeg.holds_of_checkCB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_checkCB

/-- **The assembly premise in the shape of `Shapes.equiv_of_runs`** for code with STATICCALLs: at every gas
below `2 ^ 256` and every valid call whose run meets the named hypotheses, an oracle meeting the
certificate's constraints and agreeing with an open world, under which every result of the
bytecode is the EVM IR's or a failure that changes nothing. -/
theorem runs_shape_of_checkCB {p : Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkCB p code c mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (Valid : Call → Prop) (hP : ∀ gas, StaticRunner gas)
    (hQ : ∀ gas call, Valid call → CalleesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, Valid call → ∃ o : Oracle,
      (CertOk c o ∧ ∃ W : World, W.Open ∧ CallsAgree o W) ∧
      Within (evmirSem o) (ethLibWith gas) p code (· = call) := by
  intro gas hgas call hv
  obtain ⟨o, W, h1, h2, h3, h4⟩ := assembly_of_checkCB hc codes Valid hP hQ gas hgas call hv
  exact ⟨o, ⟨h3, W, h1, h2⟩, h4⟩

/-- info: 'SolidCore.Refinement.Solar.AssembleCallSeg.runs_shape_of_checkCB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runs_shape_of_checkCB


/-! ## The ECRECOVER agreement as a hypothesis of its own -/

/-- `AssembleCallCut.PreOk` without the named agreement of the two ECRECOVER implementations: what a
run must give a STATICCALL to address 1 (no delegation there, at least 3000 gas passed on), the
runner's ECRECOVER frames being proved (`AssembleCallPre.meets_ecrecover`). -/
def PreRun (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop)
    (st : State.TransactionState) (ss : Substate) (M : ByteArray) (g : Nat)
    (asked addr inOff inSize outOff outSize : U256) : Prop :=
  addr.toNat % 2 ^ 160 = 1 ∧ (∀ c m ch, P c m ch → AssembleCallPre.EcrecoverRuns c m ch) ∧
    (∀ cc, st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok cc →
      delegatedAddress cc = none) ∧
    3000 ≤ (messageCallGas .fusaka 0 asked.toNat g
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost
      (if decide (toAddressMasked addr ∉ ss.accessedAddresses) then 2600 else 100)).subCall

/-- `CalleesOk` with `PreRun` for the calls to ECRECOVER. -/
def CalleesOkR (code : ByteArray) (msg : Message .fusaka)
    (P : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop) (bound : Nat)
    (runChild : MessageRunner .fusaka Nat bound) (fin : Evm .fusaka Nat) : Prop :=
  ∀ {e : Evm .fusaka Nat} {within : GasMeter.gasHeld e.gas ≤ bound} {pc : Nat}
    {asked addr inOff inSize outOff outSize : U256}
    {S : List U256} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray},
    At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: S) M g st ss rd e →
    (hlt : pc < code.size) → code[pc] = 0xfa →
    runFrame (step .fusaka) (step_decreases .fusaka) bound runChild e within = .ok fin →
    CalleeOk addr ∨ PreRun P st ss M g asked addr inOff inSize outOff outSize

/-- **Named hypothesis on a run**, without the ECRECOVER agreement: its STATICCALLs call code, or
ECRECOVER as `PreRun` asks. -/
def CalleesRunR (gas : Nat) (code : ByteArray) (call : Call) : Prop :=
  ∀ r, processMessage (Meter := Nat) .fusaka (Final.Target.messageWith gas code call)
      (SolidCore.Refinement.Target.preState code call) Substate.empty = .ok r → r.1.error = none →
    CalleesOkR code (Final.Target.messageWith gas code call) StaticOkE gas
      (processRunner .fusaka (Meter := Nat) gas) r.1

theorem calleesRun_of_R (hagree : AssembleCallPre.EcrecoverAgree) {gas : Nat} {code : ByteArray}
    {call : Call} (h : CalleesRunR gas code call) : CalleesRun gas code call :=
by
  intro r hr he e within pc asked addr inOff inSize outOff outSize S M g st ss rd hat hlt hb hrun
  exact (h r hr he hat hlt hb hrun).imp id fun ⟨a, b, c, d⟩ => ⟨a, hagree, b, c, d⟩

/-- **`holds_of_checkCB` with every assumption named in its statement**: the source's
specification at every open world, its totality, the stages and the checker give the
specification of the exact bytecode at every gas below `2 ^ 256`, under the named hypotheses
`StaticRunner` (EIP-214 logs, output sizes), `AssembleCallPre.EcrecoverAgree` (SolidCore's and
EthLib's ECRECOVER agree) and `CalleesRunR` (each STATICCALL of the run calls code, or ECRECOVER
with its price passed on and no delegation at address 1). -/
theorem holds_of_checkCB_named {St : Type} {fuel : Nat}
    {mirSem : SolarTV.Machine.Oracle → Sem} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {mir : ∀ o, (mirSem o).Prog} {p : Assemble.Program} {code : ByteArray} {cert : Cert}
    {mx : List Nat} {spec : Final.ContractSpec St}
    (source : ∀ W : World, W.Open → Final.Holds (solidCoreIn W fuel) c spec)
    (fin : ∀ W : World, W.Open → ∀ call, spec.Calls call → (Source.runIn W fuel c call).isSome)
    (lowering : ∀ o W, CallsAgree o W → Stage (solidCoreIn W fuel) (mirSem o) c (mir o) spec.Calls)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) (mir o) p spec.Calls)
    (hc : checkCB p code cert mx = true) (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (hP : ∀ gas, StaticRunner gas) (hagree : AssembleCallPre.EcrecoverAgree)
    (hQ : ∀ gas call, spec.Calls call → CalleesRunR gas code call)
    (gas : Nat) (hgas : gas < 2 ^ 256) : Final.Holds (Final.ethLibWith gas) code spec :=
  holds_of_checkCB source fin lowering backend hc codes hP
    (fun gas call hcall => calleesRun_of_R hagree (hQ gas call hcall)) gas hgas

/-- info: 'SolidCore.Refinement.Solar.AssembleCallSeg.holds_of_checkCB_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holds_of_checkCB_named

end SolidCore.Refinement.Solar.AssembleCallSeg

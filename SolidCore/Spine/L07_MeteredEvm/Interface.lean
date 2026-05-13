import SharedSemantics.External
import SolidCore.Spine.L05_Bytecode.Interface
import SolidCoreYulCore.BytecodeMultiContract

namespace SolidCore
namespace Spine
namespace L07_MeteredEvm

abbrev Word := SharedSemantics.Word
abbrev Byte := SharedSemantics.External.Byte
abbrev Bytes := SharedSemantics.External.Bytes
abbrev WordMap := SolidCoreYulCore.BytecodeEvm.WordMap
abbrev HashMap := SharedSemantics.External.HashMap
abbrev BytesMap := SharedSemantics.External.BytesMap
abbrev BytesSet := SharedSemantics.External.BytesSet
abbrev Opcode := SolidCoreYulCore.BytecodeEvm.Opcode
abbrev EvmState := SolidCoreYulCore.BytecodeEvm.State
abbrev MeteredState := SolidCoreYulCore.BytecodeGas.MeteredState
abbrev Gas := SolidCoreYulCore.BytecodeGas.Gas
abbrev Pc := L05_Bytecode.Pc

/--
Public L07 names are aliases for the executable bytecode EVM. The target layer
should not grow a second, theorem-only model of accounts, calls, or logs unless
there is an explicit refinement theorem back to these types.
-/
abbrev Address := Word
abbrev Account := SolidCoreYulCore.BytecodeEvm.Account
abbrev AccountMap := SolidCoreYulCore.BytecodeEvm.AccountMap
abbrev StorageAccessKey := SolidCoreYulCore.BytecodeGas.StorageAccessKey
abbrev TxContext := SolidCoreYulCore.BytecodeEvm.TxContext
abbrev BlockContext := SolidCoreYulCore.BytecodeEvm.BlockContext
abbrev CallContext := SolidCoreYulCore.BytecodeEvm.CallContext
abbrev CallKind := SharedSemantics.External.ExternalCallKind
abbrev CreateKind := SharedSemantics.External.ExternalCreateKind
abbrev Message := SolidCoreYulCore.BytecodeEvm.ExternalCall
abbrev CreateMessage := SolidCoreYulCore.BytecodeEvm.ExternalCreate
abbrev Log := SolidCoreYulCore.BytecodeEvm.LogEntry
abbrev ExternalAction := SolidCoreYulCore.BytecodeEvm.ExternalAction
abbrev ExternalResult := SolidCoreYulCore.BytecodeEvm.ExternalResult
abbrev HaltReason := SolidCoreYulCore.BytecodeEvm.HaltKind
abbrev StepError := SolidCoreYulCore.BytecodeEvm.StepError
abbrev GasError := SolidCoreYulCore.BytecodeGas.GasError
abbrev CheatcodeSignature := SolidCoreYulCore.BytecodeEvm.CheatcodeSignature
abbrev State := MeteredState

def IsCanonicalAddress (address : Address) : Prop :=
  address = SolidCoreYulCore.BytecodeEvm.addressWord address

def AccountMapAddressesCanonical : AccountMap → Prop
  | [] => True
  | (address, _) :: rest =>
      IsCanonicalAddress address ∧ AccountMapAddressesCanonical rest

def AccountCodeHashSound
    (keccakSpec : Bytes → Word → Prop) (account : Account) : Prop :=
  SharedSemantics.norm account.codeHash = 0 ∨
    keccakSpec account.code (SharedSemantics.norm account.codeHash)

def AccountMapCodeHashesSound
    (keccakSpec : Bytes → Word → Prop) : AccountMap → Prop
  | [] => True
  | (_, account) :: rest =>
      AccountCodeHashSound keccakSpec account ∧
        AccountMapCodeHashesSound keccakSpec rest

/--
Transaction-envelope wellformedness for host-supplied address fields.
The bytecode interpreter truncates stack-supplied account operands to the low
160 bits, but context fields such as `ADDRESS`, `CALLER`, `ORIGIN`, and
`COINBASE` are already 160-bit EVM addresses in real executions. Public target
claims should assume that host-provided initial states respect that boundary.
-/
structure AddressEnvelopeWellformed (state : EvmState) : Prop where
  callAddressCanonical : IsCanonicalAddress state.call.address
  callerCanonical : IsCanonicalAddress state.call.caller
  originCanonical : IsCanonicalAddress state.tx.origin
  coinbaseCanonical : IsCanonicalAddress state.block.coinbase
  accountKeysCanonical : AccountMapAddressesCanonical state.accounts

def ExternalHashSound (spec : Bytes → Word → Prop) (table : HashMap) :
    Prop :=
  ∀ input output,
    SharedSemantics.External.lookupHash? table input = some output →
      spec input output

def ExternalBytesSound (spec : Bytes → Bytes → Prop) (table : BytesMap) :
    Prop :=
  ∀ input output,
    SharedSemantics.External.lookupBytes? table input = some output →
      spec input output

def ExternalBytesSetSound (predicate : Bytes → Prop) (set : BytesSet) : Prop :=
  ∀ input,
    SharedSemantics.External.containsBytes set input = true →
      predicate input

def ExternalWordSound (spec : Word → Word → Prop) (table : WordMap) :
    Prop :=
  ∀ input output,
    SolidCoreYulCore.BytecodeEvm.lookupWord? table input = some output →
      spec input output

def ExternalWordListSound (spec : Word → Word → Prop) (values : List Word) :
    Prop :=
  ∀ index,
    spec index (SharedSemantics.External.wordListAt values index)

structure HostSpec where
  blockhash : Word → Word → Prop
  blobhash : Word → Word → Prop
  keccak256 : Bytes → Word → Prop
  wordPrecompile : Address → Bytes → Word → Prop
  bytesPrecompile : Address → Bytes → Bytes → Prop
  precompileFailure : Address → Bytes → Prop
  precompileSuccessNoOutput : Address → Bytes → Prop
  ecrecoverSignature : Word → CheatcodeSignature → Address → Prop

/--
Names the target boundary for values supplied by the host/parity harness rather
than computed inside Lean. This is intentionally an assumption interface:
block-hash and transaction blob-hash contents, crypto hashes, elliptic-curve
precompile bodies, P256/BLS checks, ECRECOVER signer recovery, and explicitly
installed account code hashes are not proved by the bytecode interpreter.
-/
structure HostAssumptions (spec : HostSpec) (state : EvmState) : Prop where
  blockhashesSound :
    ExternalWordSound spec.blockhash state.block.blockhashes
  blobhashesSound :
    ExternalWordListSound spec.blobhash state.tx.blobhashes
  accountCodeHashesSound :
    AccountMapCodeHashesSound spec.keccak256 state.accounts
  ecrecoverTablesSound :
    ∀ digest signature privateKey address,
      SolidCoreYulCore.BytecodeEvm.lookupCheatcodeSignatureSigner?
          state.cheatcodeSignatures digest signature = some privateKey →
        SolidCoreYulCore.BytecodeEvm.lookupWord?
          state.cheatcodeAddresses privateKey = some address →
          spec.ecrecoverSignature digest signature address
  keccakHashesSound : ExternalHashSound spec.keccak256 state.keccakHashes
  sha256HashesSound :
    ExternalHashSound (spec.wordPrecompile 0x02) state.sha256Hashes
  ripemd160HashesSound :
    ExternalHashSound (spec.wordPrecompile 0x03) state.ripemd160Hashes
  modexpResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x05) state.modexpResults
  blake2fResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x09) state.blake2fResults
  ecaddResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x06) state.ecaddResults
  ecaddFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x06) state.ecaddFailures
  ecmulResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x07) state.ecmulResults
  ecmulFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x07) state.ecmulFailures
  ecpairingResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x08) state.ecpairingResults
  ecpairingFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x08) state.ecpairingFailures
  pointEvaluationProofsSound :
    ExternalBytesSetSound (spec.bytesPrecompile 0x0a ·
      SolidCoreYulCore.BytecodeMultiContract.pointEvaluationOutput)
      state.pointEvaluationProofs
  pointEvaluationFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0a) state.pointEvaluationFailures
  p256VerifyProofsSound :
    ExternalBytesSetSound (spec.bytesPrecompile 0x100 ·
      SolidCoreYulCore.BytecodeMultiContract.p256VerifyOutput)
      state.p256VerifyProofs
  p256VerifyFailuresSound :
    ExternalBytesSetSound (spec.precompileSuccessNoOutput 0x100)
      state.p256VerifyFailures
  blsG1AddResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x0b) state.blsG1AddResults
  blsG1AddFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0b) state.blsG1AddFailures
  blsG1MsmResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x0c) state.blsG1MsmResults
  blsG1MsmFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0c) state.blsG1MsmFailures
  blsG2AddResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x0d) state.blsG2AddResults
  blsG2AddFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0d) state.blsG2AddFailures
  blsG2MsmResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x0e) state.blsG2MsmResults
  blsG2MsmFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0e) state.blsG2MsmFailures
  blsPairingResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x0f) state.blsPairingResults
  blsPairingFailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x0f) state.blsPairingFailures
  blsMapFpToG1ResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x10) state.blsMapFpToG1Results
  blsMapFpToG1FailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x10) state.blsMapFpToG1Failures
  blsMapFp2ToG2ResultsSound :
    ExternalBytesSound (spec.bytesPrecompile 0x11) state.blsMapFp2ToG2Results
  blsMapFp2ToG2FailuresSound :
    ExternalBytesSetSound (spec.precompileFailure 0x11) state.blsMapFp2ToG2Failures

structure Program where
  code : Bytes
  entry : Pc
  deriving Repr

structure WF (_program : Program) : Prop where
  codeWellformed : True := by trivial
  entryValid : True := by trivial

abbrev Behavior := L05_Bytecode.Behavior

/--
Bounded executable runner configuration. `callDepth`, `stepFuel`, and `fuel`
are Lean recursion/fuel bounds for total execution, not the EVM's 1024-frame
call-stack rule. `gas` is the EVM gas available to the target execution.
Public adequacy statements should keep these obligations separate: gas/OOG is
part of the executable target behavior, while the Lean fuel fields must be
assumed large enough for the execution they compare.
-/
structure ExecutionConfig where
  gas : Gas := 1000000
  callDepth : Nat := 16
  stepFuel : Nat := 200000
  fuel : Nat := 200000
  deriving Repr

def defaultExecutionConfig : ExecutionConfig := {}

/--
Public L07 execution entrypoint. Forge parity and spine claims should route
through this wrapper so they exercise the same metered multi-contract EVM.
This is the transaction-level entrypoint: child frames use raw `runFuel`
internally, while this wrapper clears transient storage and finalizes destroyed
account views at the transaction boundary.
-/
def runMetered (callDepth stepFuel fuel : Nat)
    (state : MeteredState) : MeteredState :=
  SolidCoreYulCore.BytecodeMultiContract.runTransaction
    callDepth stepFuel fuel state

theorem runMetered_eq_bytecodeMultiContract_runTransaction
    (callDepth stepFuel fuel : Nat) (state : MeteredState) :
    runMetered callDepth stepFuel fuel state =
      SolidCoreYulCore.BytecodeMultiContract.runTransaction
        callDepth stepFuel fuel state := by
  rfl

def Program.ofBytecode (bytecode : L05_Bytecode.Artifact) : Program :=
  { code := bytecode.bytes
    entry := bytecode.decoded.entry }

def Program.initialEvmState (program : Program) : EvmState :=
  { SolidCoreYulCore.BytecodeEvm.State.empty with
    code := program.code
    pc := program.entry.value }

theorem Program.initialEvmState_addressEnvelopeWellformed
    (program : Program) :
    AddressEnvelopeWellformed program.initialEvmState := by
  cases program
  constructor <;>
    simp [Program.initialEvmState, SolidCoreYulCore.BytecodeEvm.State.empty,
      IsCanonicalAddress, SolidCoreYulCore.BytecodeEvm.addressWord,
      SharedSemantics.External.addressWord,
      SharedSemantics.External.addressModulus, SharedSemantics.norm,
      SharedSemantics.wordModulus, AccountMapAddressesCanonical]

/--
The bounded Lean runner reached a target stopping state before exhausting its
fuel. This is only a totality/bounding assumption for the executable wrapper; it
does not assert any separate gas-model equivalence.
-/
def Program.FuelBoundsSufficient
    (program : Program) (config : ExecutionConfig) : Prop :=
  SolidCoreYulCore.BytecodeGas.MeteredState.stopped
    (runMetered config.callDepth config.stepFuel config.fuel
      (SolidCoreYulCore.BytecodeGas.MeteredState.ofStateOsaka
        program.initialEvmState config.gas)) = true

/--
Assumptions a future bytecode-to-EVM adequacy theorem should quantify over
when it relies on the public L07 executable target. Host-provided hashes and
precompile facts, transaction-envelope wellformedness, and Lean fuel sufficiency
are explicit target-side obligations rather than hidden compiler conveniences.
-/
structure TargetAssumptions
    (spec : HostSpec) (program : Program) (config : ExecutionConfig) :
    Prop where
  hostTablesSound : HostAssumptions spec program.initialEvmState
  addressEnvelopeWellformed :
    AddressEnvelopeWellformed program.initialEvmState
  fuelBoundsSufficient :
    program.FuelBoundsSufficient config

def Program.initialState (program : Program)
    (gas : Gas := defaultExecutionConfig.gas) : MeteredState :=
  SolidCoreYulCore.BytecodeGas.MeteredState.ofStateOsaka
    program.initialEvmState gas

def Program.runWithConfig (program : Program)
    (config : ExecutionConfig := defaultExecutionConfig) : MeteredState :=
  runMetered config.callDepth config.stepFuel config.fuel
    (program.initialState config.gas)

theorem Program.FuelBoundsSufficient.runWithConfig_stopped
    {program : Program} {config : ExecutionConfig}
    (hFuel : program.FuelBoundsSufficient config) :
    SolidCoreYulCore.BytecodeGas.MeteredState.stopped
      (program.runWithConfig config) = true := by
  simpa [Program.FuelBoundsSufficient, Program.runWithConfig,
    Program.initialState] using hFuel

theorem TargetAssumptions.runWithConfig_stopped
    {spec : HostSpec} {program : Program} {config : ExecutionConfig}
    (assumptions : TargetAssumptions spec program config) :
    SolidCoreYulCore.BytecodeGas.MeteredState.stopped
      (program.runWithConfig config) = true :=
  Program.FuelBoundsSufficient.runWithConfig_stopped
    assumptions.fuelBoundsSufficient

def Program.runWithFuel (program : Program) (fuel : Nat) : MeteredState :=
  runMetered defaultExecutionConfig.callDepth fuel fuel program.initialState

def Program.RunsToStopWithConfig
    (program : Program) (config : ExecutionConfig) : Prop :=
  (program.runWithConfig config).evm.halt? =
    some SolidCoreYulCore.BytecodeEvm.HaltKind.stopped

def Program.RunsToReturnWord0WithConfig
    (program : Program) (config : ExecutionConfig) : Prop :=
  (program.runWithConfig config).evm.halt? =
      some SolidCoreYulCore.BytecodeEvm.HaltKind.returned ∧
    (program.runWithConfig config).evm.output =
      SolidCoreYulCore.BytecodeEvm.wordToBytes32 0

def Program.RunsToStop (program : Program) : Prop :=
  program.RunsToStopWithConfig defaultExecutionConfig

def Program.RunsToReturnWord0 (program : Program) : Prop :=
  program.RunsToReturnWord0WithConfig defaultExecutionConfig

inductive SemanticsWithConfig :
    Program -> ExecutionConfig -> Behavior -> Prop where
  | stopped {program : Program} {config : ExecutionConfig} :
      program.RunsToStopWithConfig config ->
      SemanticsWithConfig program config L01_ValidSolidity.Behavior.stopped
  | returnedWord0 {program : Program} {config : ExecutionConfig} :
      program.RunsToReturnWord0WithConfig config ->
      SemanticsWithConfig program config
        (L01_ValidSolidity.Behavior.returnedWord 0)

abbrev Semantics (program : Program) (behavior : Behavior) : Prop :=
  SemanticsWithConfig program defaultExecutionConfig behavior

def Program.stop : Program :=
  Program.ofBytecode L05_Bytecode.Artifact.stop

def Program.returnWord0 : Program :=
  Program.ofBytecode L05_Bytecode.Artifact.returnWord0

theorem Program.stop_wf : WF Program.stop := by
  exact {}

theorem Program.stop_runsToStop : Program.stop.RunsToStop := by
  unfold Program.RunsToStop Program.RunsToStopWithConfig
  change
    (Program.stop.runWithConfig defaultExecutionConfig).evm.halt? =
      some SolidCoreYulCore.BytecodeEvm.HaltKind.stopped
  native_decide

theorem Program.stop_fuelBoundsSufficient :
    Program.stop.FuelBoundsSufficient defaultExecutionConfig := by
  unfold Program.FuelBoundsSufficient
  native_decide

theorem Program.stop_semantics :
    Semantics Program.stop L01_ValidSolidity.Behavior.stopped := by
  exact SemanticsWithConfig.stopped Program.stop_runsToStop

theorem Program.returnWord0_wf : WF Program.returnWord0 := by
  exact {}

theorem Program.returnWord0_runsToReturnWord0 :
    Program.returnWord0.RunsToReturnWord0 := by
  unfold Program.RunsToReturnWord0 Program.RunsToReturnWord0WithConfig
  constructor
  · change
      (Program.returnWord0.runWithConfig defaultExecutionConfig).evm.halt? =
        some SolidCoreYulCore.BytecodeEvm.HaltKind.returned
    native_decide
  · change
      (Program.returnWord0.runWithConfig defaultExecutionConfig).evm.output =
        SolidCoreYulCore.BytecodeEvm.wordToBytes32 0
    native_decide

theorem Program.returnWord0_fuelBoundsSufficient :
    Program.returnWord0.FuelBoundsSufficient defaultExecutionConfig := by
  unfold Program.FuelBoundsSufficient
  native_decide

theorem Program.returnWord0_semantics :
    Semantics Program.returnWord0
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  exact SemanticsWithConfig.returnedWord0 Program.returnWord0_runsToReturnWord0

theorem Program.ofBytecode_stop_semantics
    {bytecode : L05_Bytecode.Artifact}
    (hStop : bytecode.IsStop) :
    Semantics (Program.ofBytecode bytecode)
      L01_ValidSolidity.Behavior.stopped := by
  rcases hStop with ⟨hBytes, hDecoded, _hEntry, _hInstrs⟩
  apply SemanticsWithConfig.stopped
  simpa [Semantics, Program.RunsToStop, Program.RunsToStopWithConfig,
    Program.runWithConfig, runMetered, Program.initialState,
    Program.initialEvmState, Program.ofBytecode,
    hBytes, hDecoded, L05_Bytecode.DecodedProgram.stop,
    L05_Bytecode.Pc.zero] using Program.stop_runsToStop

theorem Program.ofBytecode_stop_fuelBoundsSufficient
    {bytecode : L05_Bytecode.Artifact}
    (hStop : bytecode.IsStop) :
    (Program.ofBytecode bytecode).FuelBoundsSufficient
      defaultExecutionConfig := by
  rcases hStop with ⟨hBytes, hDecoded, _hEntry, _hInstrs⟩
  simpa [Program.FuelBoundsSufficient, Program.initialEvmState,
    Program.ofBytecode, hBytes, hDecoded,
    L05_Bytecode.DecodedProgram.stop, L05_Bytecode.Pc.zero]
    using Program.stop_fuelBoundsSufficient

theorem Program.ofBytecode_returnWord0_semantics
    {bytecode : L05_Bytecode.Artifact}
    (hReturn : bytecode.IsReturnWord0) :
    Semantics (Program.ofBytecode bytecode)
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  rcases hReturn with ⟨hBytes, hDecoded, _hEntry⟩
  apply SemanticsWithConfig.returnedWord0
  simpa [Semantics, Program.RunsToReturnWord0,
    Program.RunsToReturnWord0WithConfig, Program.runWithConfig, runMetered,
    Program.initialState, Program.initialEvmState, Program.ofBytecode,
    hBytes, hDecoded, L05_Bytecode.DecodedProgram.returnWord0,
    L05_Bytecode.Pc.zero] using Program.returnWord0_runsToReturnWord0

theorem Program.ofBytecode_returnWord0_fuelBoundsSufficient
    {bytecode : L05_Bytecode.Artifact}
    (hReturn : bytecode.IsReturnWord0) :
    (Program.ofBytecode bytecode).FuelBoundsSufficient
      defaultExecutionConfig := by
  rcases hReturn with ⟨hBytes, hDecoded, _hEntry⟩
  simpa [Program.FuelBoundsSufficient, Program.initialEvmState,
    Program.ofBytecode, hBytes, hDecoded,
    L05_Bytecode.DecodedProgram.returnWord0, L05_Bytecode.Pc.zero]
    using Program.returnWord0_fuelBoundsSufficient

end L07_MeteredEvm
end Spine
end SolidCore

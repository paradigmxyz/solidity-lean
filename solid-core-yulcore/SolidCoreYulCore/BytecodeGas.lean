import SolidCoreYulCore.BytecodeEvm

namespace SolidCoreYulCore
namespace BytecodeGas

open BytecodeEvm

/--
Gas metering for the bytecode EVM is deliberately layered on top of the
gasless interpreter. Existing proofs can continue to use `BytecodeEvm.step`,
while this module supplies a metered wrapper with a pluggable cost model.

The default model below targets Osaka, the execution-layer fork in the live
Fusaka network upgrade. Transaction validation, precompile execution bodies,
and consensus-layer blob scheduling remain outside this single-contract
bytecode interpreter, but their fork constants are recorded here.
-/

abbrev Gas := Nat
abbrev StorageAccessKey := Word × Word

inductive GasError where
  | outOfGas (needed remaining : Gas)
deriving DecidableEq, Repr

structure MeteredState where
  evm : State := State.empty
  gasRemaining : Gas := 0
  gasUsed : Gas := 0
  gasError? : Option GasError := none
  originalAccounts : AccountMap := []
  accessedAddresses : List Word := []
  accessedStorageKeys : List StorageAccessKey := []
  refund : Int := 0
deriving DecidableEq, Repr

structure MeterEffects where
  cost : Gas := 0
  refundDelta : Int := 0
  accessedAddresses : List Word := []
  accessedStorageKeys : List StorageAccessKey := []
  childGas? : Option Gas := none
deriving DecidableEq, Repr

def MeteredState.ofState (evm : State) (gasRemaining : Gas) : MeteredState :=
  { evm := evm, gasRemaining := gasRemaining, originalAccounts := evm.accounts }

def MeteredState.stopped (state : MeteredState) : Bool :=
  state.gasError?.isSome || state.evm.halt?.isSome || state.evm.error?.isSome

structure CostModel where
  opcodeCost : Opcode → MeteredState → MeterEffects
  invalidOpcodeCost : Byte → MeteredState → MeterEffects :=
    fun _ _ => {}

namespace GasConst

def zero : Gas := 0
def base : Gas := 2
def verylow : Gas := 3
def low : Gas := 5
def mid : Gas := 8
def high : Gas := 10
def jumpdest : Gas := 1

def warmAccess : Gas := 100
def coldAccountAccess : Gas := 2600
def coldStorageAccess : Gas := 2100

def storageSet : Gas := 20000
def coldStorageWrite : Gas := 5000

def callValueTransfer : Gas := 9000
def callStipend : Gas := 2300
def newAccount : Gas := 25000

def codeDepositPerByte : Gas := 200
def codeInitPerWord : Gas := 2
def authPerEmptyAccount : Gas := 25000
def refundAuthPerExistingAccount : Gas := 12500

def memory : Gas := 3
def fastStep : Gas := 5
def copy : Gas := 3
def keccak : Gas := 30
def keccakWord : Gas := 6
def log : Gas := 375
def logTopic : Gas := 375
def logData : Gas := 8
def refundStorageClear : Gas := 4800

def create : Gas := 32000
def selfdestruct : Gas := 5000
def selfdestructNewAccount : Gas := 25000

def expBase : Gas := 10
def expPerByte : Gas := 50

def precompileEcrecover : Gas := 3000
def precompileP256Verify : Gas := 6900
def precompileSha256Base : Gas := 60
def precompileSha256PerWord : Gas := 12
def precompileRipemd160Base : Gas := 600
def precompileRipemd160PerWord : Gas := 120
def precompileIdentityBase : Gas := 15
def precompileIdentityPerWord : Gas := 3
def precompileBlake2fPerRound : Gas := 1
def precompilePointEvaluation : Gas := 50000
def precompileBlsG1Add : Gas := 375
def precompileBlsG1Mul : Gas := 12000
def precompileBlsG1Map : Gas := 5500
def precompileBlsG2Add : Gas := 600
def precompileBlsG2Mul : Gas := 22500
def precompileBlsG2Map : Gas := 23800
def precompileEcadd : Gas := 150
def precompileEcmul : Gas := 6000
def precompileEcpairingBase : Gas := 45000
def precompileEcpairingPerPoint : Gas := 34000

def perBlob : Gas := 2 ^ 17
def blobScheduleTarget : Gas := 6
def blobTargetGasPerBlock : Gas := perBlob * blobScheduleTarget
def blobBaseCost : Gas := 2 ^ 13
def blobScheduleMax : Gas := 9
def blobMinGasprice : Gas := 1
def blobBaseFeeUpdateFraction : Gas := 5007716

def txBase : Gas := 21000
def txCreate : Gas := 32000
def txDataTokenStandard : Gas := 4
def txDataTokenFloor : Gas := 10
def txAccessListAddress : Gas := 2400
def txAccessListStorageKey : Gas := 1900
def txMaxGasLimit : Gas := 16777216
def defaultBlockGasLimit : Gas := 60000000

def limitAdjustmentFactor : Gas := 1024
def limitMinimum : Gas := 5000
def osakaMainnetTimestamp : Gas := 1764798551

end GasConst

def wordIn (value : Word) : List Word → Bool
  | [] => false
  | candidate :: rest =>
      if norm candidate = norm value then true else wordIn value rest

def insertWordSet (value : Word) (values : List Word) : List Word :=
  if wordIn value values then values else norm value :: values

def storageKeyIn (key : StorageAccessKey) : List StorageAccessKey → Bool
  | [] => false
  | candidate :: rest =>
      if norm candidate.1 = norm key.1 ∧ norm candidate.2 = norm key.2 then
        true
      else
        storageKeyIn key rest

def insertStorageKeySet
    (key : StorageAccessKey) (keys : List StorageAccessKey) :
    List StorageAccessKey :=
  if storageKeyIn key keys then keys else (norm key.1, norm key.2) :: keys

def addAccessedAddresses (addresses : List Word) (state : MeteredState) :
    MeteredState :=
  { state with
    accessedAddresses :=
      addresses.foldl (fun acc address => insertWordSet address acc)
        state.accessedAddresses }

def addAccessedStorageKeys
    (keys : List StorageAccessKey) (state : MeteredState) : MeteredState :=
  { state with
    accessedStorageKeys :=
      keys.foldl (fun acc key => insertStorageKeySet key acc)
        state.accessedStorageKeys }

def applyMeterEffects (effects : MeterEffects) (state : MeteredState) :
    MeteredState :=
  { addAccessedStorageKeys effects.accessedStorageKeys
      (addAccessedAddresses effects.accessedAddresses state) with
    refund := state.refund + effects.refundDelta }

def precompileAddresses : List Word :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0x100]

def initialOsakaAccessedAddresses (state : State) : List Word :=
  precompileAddresses.foldl
    (fun acc address => insertWordSet address acc)
    [norm state.call.address, norm state.tx.origin, norm state.block.coinbase]

def MeteredState.ofStateOsaka
    (evm : State) (gasRemaining : Gas) : MeteredState :=
  { MeteredState.ofState evm gasRemaining with
    accessedAddresses := initialOsakaAccessedAddresses evm }

def stackWordD (state : State) (index : Nat) : Word :=
  norm ((state.stack[index]?).getD 0)

def byteLengthAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, value =>
      if value = 0 then 0 else 1 + byteLengthAux fuel (value / 256)

def bytesForWord (value : Word) : Gas :=
  byteLengthAux 32 (norm value)

def wordsForBytes (bytes : Nat) : Gas :=
  (bytes + 31) / 32

def initCodeCost (initCodeLength : Nat) : Gas :=
  GasConst.codeInitPerWord * wordsForBytes initCodeLength

def calldataTokenCount : Bytes → Gas
  | [] => 0
  | value :: rest =>
      (if byte value = 0 then 1 else 4) + calldataTokenCount rest

def calldataFloorGasCost (calldata : Bytes) : Gas :=
  GasConst.txBase + calldataTokenCount calldata * GasConst.txDataTokenFloor

def intrinsicGasCost
    (calldata : Bytes) (isCreate : Bool)
    (accessListAddressCount accessListStorageKeyCount authorizationCount : Nat) :
    Gas :=
  GasConst.txBase +
    calldataTokenCount calldata * GasConst.txDataTokenStandard +
    (if isCreate then GasConst.txCreate + initCodeCost calldata.length else 0) +
    accessListAddressCount * GasConst.txAccessListAddress +
    accessListStorageKeyCount * GasConst.txAccessListStorageKey +
    authorizationCount * GasConst.authPerEmptyAccount

def linearPrecompileGas (base perWord inputLength : Gas) : Gas :=
  base + perWord * wordsForBytes inputLength

def bitLength256 (value : Word) : Gas :=
  256 - norm (clzWord value)

def modexpInputWithinOsakaBounds
    (baseLength exponentLength modulusLength : Gas) : Bool :=
  decide
    (baseLength <= 1024 ∧ exponentLength <= 1024 ∧ modulusLength <= 1024)

def modexpComplexity (baseLength modulusLength : Gas) : Gas :=
  let maxLength := max baseLength modulusLength
  let words := (maxLength + 7) / 8
  if maxLength > 32 then 2 * words ^ 2 else 16

def modexpIterations (exponentLength exponentHead : Gas) : Gas :=
  let headBits := bitLength256 exponentHead
  let headPart := if headBits = 0 then 0 else headBits - 1
  let count :=
    if exponentLength <= 32 ∧ norm exponentHead = 0 then
      0
    else if exponentLength <= 32 then
      headPart
    else
      16 * (exponentLength - 32) + headPart
  max count 1

def modexpGasCost
    (baseLength modulusLength exponentLength exponentHead : Gas) : Gas :=
  max 500
    (modexpComplexity baseLength modulusLength *
      modexpIterations exponentLength exponentHead)

def memoryCostForBytes (bytes : Nat) : Gas :=
  let words := wordsForBytes bytes
  GasConst.memory * words + (words * words) / 512

def expandedMemorySize (memory : Memory) (ranges : List (Word × Word)) : Nat :=
  ranges.foldl
    (fun size range =>
      if norm range.2 = 0 then
        size
      else
        max size (norm range.1 + norm range.2))
    memory.size

def memoryExpansionCostForRanges
    (memory : Memory) (ranges : List (Word × Word)) : Gas :=
  memoryCostForBytes (expandedMemorySize memory ranges) -
    memoryCostForBytes memory.size

def memoryRangesForOpcode (opcode : Opcode) (state : State) :
    List (Word × Word) :=
  match opcode with
  | Opcode.keccak256 => [(stackWordD state 0, stackWordD state 1)]
  | Opcode.calldatacopy => [(stackWordD state 0, stackWordD state 2)]
  | Opcode.codecopy => [(stackWordD state 0, stackWordD state 2)]
  | Opcode.extcodecopy => [(stackWordD state 1, stackWordD state 3)]
  | Opcode.returndatacopy => [(stackWordD state 0, stackWordD state 2)]
  | Opcode.mload => [(stackWordD state 0, 32)]
  | Opcode.mstore => [(stackWordD state 0, 32)]
  | Opcode.mstore8 => [(stackWordD state 0, 1)]
  | Opcode.mcopy =>
      [ (stackWordD state 0, stackWordD state 2),
        (stackWordD state 1, stackWordD state 2) ]
  | Opcode.log _ => [(stackWordD state 0, stackWordD state 1)]
  | Opcode.create => [(stackWordD state 1, stackWordD state 2)]
  | Opcode.call =>
      [ (stackWordD state 3, stackWordD state 4),
        (stackWordD state 5, stackWordD state 6) ]
  | Opcode.callcode =>
      [ (stackWordD state 3, stackWordD state 4),
        (stackWordD state 5, stackWordD state 6) ]
  | Opcode.returnOp => [(stackWordD state 0, stackWordD state 1)]
  | Opcode.delegatecall =>
      [ (stackWordD state 2, stackWordD state 3),
        (stackWordD state 4, stackWordD state 5) ]
  | Opcode.create2 => [(stackWordD state 1, stackWordD state 2)]
  | Opcode.staticcall =>
      [ (stackWordD state 2, stackWordD state 3),
        (stackWordD state 4, stackWordD state 5) ]
  | Opcode.revert => [(stackWordD state 0, stackWordD state 1)]
  | _ => []

def accountIsEmpty (account : Account) : Bool :=
  decide
    (account.nonce = 0 ∧ account.balance = 0 ∧ account.code = [] ∧
      account.codeHash = 0)

def accountAlive (state : State) (address : Word) : Bool :=
  match accountAt? state address with
  | none => false
  | some account => !accountIsEmpty account

def originalStorageValue
    (state : MeteredState) (address key : Word) : Word :=
  if (rawAccount state.evm address).createdInTransaction then
    0
  else
    match lookupAccount? state.originalAccounts address with
    | none => 0
    | some account => (lookupWord? account.storage key).getD 0

def currentStorageValue (state : MeteredState) (address key : Word) : Word :=
  (lookupWord? (rawAccount state.evm address).storage key).getD 0

def accountAccessCost (state : MeteredState) (address : Word) : Gas :=
  if wordIn address state.accessedAddresses then
    GasConst.warmAccess
  else
    GasConst.coldAccountAccess

def storageAccessCost
    (state : MeteredState) (address key : Word) : Gas :=
  if storageKeyIn (address, key) state.accessedStorageKeys then
    GasConst.warmAccess
  else
    GasConst.coldStorageAccess

def accountAccessEffect (address : Word) (state : MeteredState) :
    MeterEffects :=
  { cost := accountAccessCost state address,
    accessedAddresses := [address] }

def delegatedAddress? (state : State) (address : Word) : Option Word :=
  let code := accountCode state address
  if code.length = 23 ∧ code.take 3 = [0xef, 0x01, 0x00] then
    some (bytesToWordBE (code.drop 3))
  else
    none

def accountAccessWithDelegationEffect
    (address : Word) (state : MeteredState) : MeterEffects :=
  let first := accountAccessEffect address state
  let stateAfterFirst := addAccessedAddresses [address] state
  match delegatedAddress? state.evm address with
  | none => first
  | some delegated =>
      { first with
        cost := first.cost + accountAccessCost stateAfterFirst delegated,
        accessedAddresses := delegated :: first.accessedAddresses }

def osakaStaticCost : Opcode → Gas
  | Opcode.stop => GasConst.zero
  | Opcode.add => GasConst.verylow
  | Opcode.mul => GasConst.low
  | Opcode.sub => GasConst.verylow
  | Opcode.div => GasConst.low
  | Opcode.sdiv => GasConst.low
  | Opcode.modOp => GasConst.low
  | Opcode.smod => GasConst.low
  | Opcode.addmod => GasConst.mid
  | Opcode.mulmod => GasConst.mid
  | Opcode.exp => GasConst.expBase
  | Opcode.signextend => GasConst.low
  | Opcode.lt => GasConst.verylow
  | Opcode.gt => GasConst.verylow
  | Opcode.slt => GasConst.verylow
  | Opcode.sgt => GasConst.verylow
  | Opcode.eq => GasConst.verylow
  | Opcode.iszero => GasConst.verylow
  | Opcode.andOp => GasConst.verylow
  | Opcode.orOp => GasConst.verylow
  | Opcode.xor => GasConst.verylow
  | Opcode.notOp => GasConst.verylow
  | Opcode.byteOp => GasConst.verylow
  | Opcode.shl => GasConst.verylow
  | Opcode.shr => GasConst.verylow
  | Opcode.sar => GasConst.verylow
  | Opcode.clz => GasConst.low
  | Opcode.keccak256 => GasConst.keccak
  | Opcode.address => GasConst.base
  | Opcode.balance => GasConst.zero
  | Opcode.origin => GasConst.base
  | Opcode.caller => GasConst.base
  | Opcode.callvalue => GasConst.base
  | Opcode.calldataload => GasConst.verylow
  | Opcode.calldatasize => GasConst.base
  | Opcode.calldatacopy => GasConst.verylow
  | Opcode.codesize => GasConst.base
  | Opcode.codecopy => GasConst.verylow
  | Opcode.gasprice => GasConst.base
  | Opcode.extcodesize => GasConst.zero
  | Opcode.extcodecopy => GasConst.zero
  | Opcode.returndatasize => GasConst.base
  | Opcode.returndatacopy => GasConst.verylow
  | Opcode.extcodehash => GasConst.zero
  | Opcode.blockhash => 20
  | Opcode.coinbase => GasConst.base
  | Opcode.timestamp => GasConst.base
  | Opcode.number => GasConst.base
  | Opcode.prevrandao => GasConst.base
  | Opcode.gaslimit => GasConst.base
  | Opcode.chainid => GasConst.base
  | Opcode.selfbalance => GasConst.fastStep
  | Opcode.basefee => GasConst.base
  | Opcode.blobhash => GasConst.verylow
  | Opcode.blobbasefee => GasConst.base
  | Opcode.pop => GasConst.base
  | Opcode.mload => GasConst.verylow
  | Opcode.mstore => GasConst.verylow
  | Opcode.mstore8 => GasConst.verylow
  | Opcode.sload => GasConst.zero
  | Opcode.sstore => GasConst.zero
  | Opcode.jump => GasConst.mid
  | Opcode.jumpi => GasConst.high
  | Opcode.pc => GasConst.base
  | Opcode.msize => GasConst.base
  | Opcode.gas => GasConst.base
  | Opcode.jumpdest => GasConst.jumpdest
  | Opcode.tload => GasConst.warmAccess
  | Opcode.tstore => GasConst.warmAccess
  | Opcode.mcopy => GasConst.verylow
  | Opcode.push 0 => GasConst.base
  | Opcode.push _ => GasConst.verylow
  | Opcode.dup _ => GasConst.verylow
  | Opcode.swap _ => GasConst.verylow
  | Opcode.log _ => GasConst.log
  | Opcode.create => GasConst.create
  | Opcode.call => GasConst.zero
  | Opcode.callcode => GasConst.zero
  | Opcode.returnOp => GasConst.zero
  | Opcode.delegatecall => GasConst.zero
  | Opcode.create2 => GasConst.create
  | Opcode.staticcall => GasConst.zero
  | Opcode.revert => GasConst.zero
  | Opcode.invalid => GasConst.zero
  | Opcode.selfdestruct => GasConst.zero

def osakaDynamicCost : Opcode → State → Gas
  | Opcode.exp, state =>
      GasConst.expPerByte * bytesForWord (stackWordD state 1)
  | Opcode.keccak256, state =>
      GasConst.keccakWord * wordsForBytes (stackWordD state 1)
  | Opcode.calldatacopy, state =>
      GasConst.copy * wordsForBytes (stackWordD state 2)
  | Opcode.codecopy, state =>
      GasConst.copy * wordsForBytes (stackWordD state 2)
  | Opcode.returndatacopy, state =>
      GasConst.copy * wordsForBytes (stackWordD state 2)
  | Opcode.mcopy, state =>
      GasConst.copy * wordsForBytes (stackWordD state 2)
  | Opcode.log topics, state =>
      GasConst.logTopic * topics + GasConst.logData * norm (stackWordD state 1)
  | _, _ => 0

def simpleOpcodeEffects (opcode : Opcode) (state : MeteredState) :
    MeterEffects :=
  { cost :=
      osakaStaticCost opcode +
        osakaDynamicCost opcode state.evm +
        memoryExpansionCostForRanges state.evm.memory
          (memoryRangesForOpcode opcode state.evm) }

def sloadEffects (state : MeteredState) : MeterEffects :=
  let key := stackWordD state.evm 0
  { cost := storageAccessCost state state.evm.call.address key,
    accessedStorageKeys := [(state.evm.call.address, key)] }

def sstoreRefundDelta
    (original current newValue : Word) : Int :=
  if norm current = norm newValue then
    0
  else
    let clearRefund :=
      if norm original ≠ 0 ∧ norm current ≠ 0 ∧ norm newValue = 0 then
        Int.ofNat GasConst.refundStorageClear
      else
        0
    let recreateDebit :=
      if norm original ≠ 0 ∧ norm current = 0 then
        -(Int.ofNat GasConst.refundStorageClear)
      else
        0
    let resetRefund :=
      if norm original = norm newValue then
        if norm original = 0 then
          Int.ofNat (GasConst.storageSet - GasConst.warmAccess)
        else
          Int.ofNat
            (GasConst.coldStorageWrite - GasConst.coldStorageAccess -
              GasConst.warmAccess)
      else
        0
    clearRefund + recreateDebit + resetRefund

def sstoreEffects (state : MeteredState) : MeterEffects :=
  if state.gasRemaining <= GasConst.callStipend then
    { cost := GasConst.callStipend + 1 }
  else
    let address := state.evm.call.address
    let key := stackWordD state.evm 0
    let newValue := stackWordD state.evm 1
    let original := originalStorageValue state address key
    let current := currentStorageValue state address key
    let coldCost :=
      if storageKeyIn (address, key) state.accessedStorageKeys then
        0
      else
        GasConst.coldStorageAccess
    let writeCost :=
      if norm original = norm current ∧ norm current ≠ norm newValue then
        if norm original = 0 then
          GasConst.storageSet
        else
          GasConst.coldStorageWrite - GasConst.coldStorageAccess
      else
        GasConst.warmAccess
    { cost := coldCost + writeCost,
      refundDelta := sstoreRefundDelta original current newValue,
      accessedStorageKeys := [(address, key)] }

structure MessageCallGas where
  cost : Gas
  subcall : Gas
deriving DecidableEq, Repr

def maxMessageCallGas (gas : Gas) : Gas :=
  gas - gas / 64

def calculateMessageCallGas
    (value requestedGas gasLeft memoryCost extraGas : Gas) : MessageCallGas :=
  let stipend := if value = 0 then 0 else GasConst.callStipend
  if gasLeft < extraGas + memoryCost then
    { cost := requestedGas + extraGas, subcall := requestedGas + stipend }
  else
    let childGas :=
      min requestedGas (maxMessageCallGas (gasLeft - memoryCost - extraGas))
    { cost := childGas + extraGas, subcall := childGas + stipend }

def callEffects
    (targetIndex valueIndex : Nat) (chargesNewAccount : Bool)
    (usesDelegation : Bool) (state : MeteredState) : MeterEffects :=
  let target := stackWordD state.evm targetIndex
  let value := stackWordD state.evm valueIndex
  let requestedGas := stackWordD state.evm 0
  let memoryCost :=
    memoryExpansionCostForRanges state.evm.memory
      (memoryRangesForOpcode Opcode.call state.evm)
  let access :=
    if usesDelegation then
      accountAccessWithDelegationEffect target state
    else
      accountAccessEffect target state
  let createCost :=
    if chargesNewAccount && norm value ≠ 0 && !accountAlive state.evm target then
      GasConst.newAccount
    else
      0
  let transferCost := if norm value = 0 then 0 else GasConst.callValueTransfer
  let callGas :=
    calculateMessageCallGas (norm value) requestedGas state.gasRemaining
      memoryCost (access.cost + createCost + transferCost)
  { access with
    cost := callGas.cost + memoryCost,
    childGas? := some callGas.subcall }

def callNoValueEffects
    (targetIndex : Nat) (usesDelegation : Bool) (opcode : Opcode)
    (state : MeteredState) : MeterEffects :=
  let target := stackWordD state.evm targetIndex
  let requestedGas := stackWordD state.evm 0
  let memoryCost :=
    memoryExpansionCostForRanges state.evm.memory
      (memoryRangesForOpcode opcode state.evm)
  let access :=
    if usesDelegation then
      accountAccessWithDelegationEffect target state
    else
      accountAccessEffect target state
  let callGas :=
    calculateMessageCallGas 0 requestedGas state.gasRemaining memoryCost
      access.cost
  { access with
    cost := callGas.cost + memoryCost,
    childGas? := some callGas.subcall }

def createEffects (kind : ExternalCreateKind) (state : MeteredState) :
    MeterEffects :=
  let size := stackWordD state.evm 2
  let opcode :=
    match kind with
    | ExternalCreateKind.create => Opcode.create
    | ExternalCreateKind.create2 => Opcode.create2
  let memoryCost :=
    memoryExpansionCostForRanges state.evm.memory
      (memoryRangesForOpcode opcode state.evm)
  let hashCost :=
    match kind with
    | ExternalCreateKind.create => 0
    | ExternalCreateKind.create2 =>
        GasConst.keccakWord * wordsForBytes size
  let initialCost :=
    GasConst.create + memoryCost + initCodeCost size + hashCost
  if initialCost <= state.gasRemaining then
    let childGas := maxMessageCallGas (state.gasRemaining - initialCost)
    { cost := initialCost + childGas, childGas? := some childGas }
  else
    { cost := initialCost }

def selfdestructEffects (state : MeteredState) : MeterEffects :=
  let beneficiary := stackWordD state.evm 0
  let access := accountAccessEffect beneficiary state
  let currentBalance := (rawAccount state.evm state.evm.call.address).balance
  let newAccountCost :=
    if !accountAlive state.evm beneficiary && norm currentBalance ≠ 0 then
      GasConst.selfdestructNewAccount
    else
      0
  { access with cost := GasConst.selfdestruct + access.cost + newAccountCost }

def extcodecopyEffects (state : MeteredState) : MeterEffects :=
  let address := stackWordD state.evm 0
  let copyCost := GasConst.copy * wordsForBytes (stackWordD state.evm 3)
  let memoryCost :=
    memoryExpansionCostForRanges state.evm.memory
      (memoryRangesForOpcode Opcode.extcodecopy state.evm)
  let access := accountAccessEffect address state
  { access with cost := access.cost + copyCost + memoryCost }

def osakaOpcodeEffects (opcode : Opcode) (state : MeteredState) :
    MeterEffects :=
  match opcode with
  | Opcode.balance => accountAccessEffect (stackWordD state.evm 0) state
  | Opcode.extcodesize => accountAccessEffect (stackWordD state.evm 0) state
  | Opcode.extcodehash => accountAccessEffect (stackWordD state.evm 0) state
  | Opcode.extcodecopy => extcodecopyEffects state
  | Opcode.sload => sloadEffects state
  | Opcode.sstore => sstoreEffects state
  | Opcode.call => callEffects 1 2 true true state
  | Opcode.callcode => callEffects 1 2 false true state
  | Opcode.delegatecall =>
      callNoValueEffects 1 true Opcode.delegatecall state
  | Opcode.staticcall =>
      callNoValueEffects 1 true Opcode.staticcall state
  | Opcode.create => createEffects ExternalCreateKind.create state
  | Opcode.create2 => createEffects ExternalCreateKind.create2 state
  | Opcode.selfdestruct => selfdestructEffects state
  | _ => simpleOpcodeEffects opcode state

def osakaCostModel : CostModel :=
  { opcodeCost := osakaOpcodeEffects }

def defaultCostModel : CostModel :=
  osakaCostModel

def chargeGas (cost : Gas) (state : MeteredState) : Option MeteredState :=
  if cost <= state.gasRemaining then
    some
      { state with
        gasRemaining := state.gasRemaining - cost,
        gasUsed := state.gasUsed + cost }
  else
    none

def setOutOfGas (cost : Gas) (state : MeteredState) : MeteredState :=
  { state with
    evm := { state.evm with halt? := some HaltKind.exceptional },
    gasRemaining := 0,
    gasUsed := state.gasUsed + state.gasRemaining,
    gasError? := some (GasError.outOfGas cost state.gasRemaining) }

def refundGas (amount : Gas) (state : MeteredState) : MeteredState :=
  { state with
    gasRemaining := state.gasRemaining + amount,
    gasUsed := state.gasUsed - amount }

def exceptionalHalt (state : MeteredState) : Bool :=
  state.evm.error?.isSome ||
    match state.evm.halt? with
    | some HaltKind.exceptional => true
    | _ => false

def consumeRemainingGasIfExceptional (state : MeteredState) : MeteredState :=
  if exceptionalHalt state then
    { state with
      gasUsed := state.gasUsed + state.gasRemaining,
      gasRemaining := 0 }
  else
    state

def stepGasOpcode (state : State) (gasRemaining : Gas) : State :=
  pushOrError state (state.pc + 1) gasRemaining

def setCallActionGas (gas : Gas) : ExternalAction → ExternalAction
  | ExternalAction.call call => ExternalAction.call { call with gas := gas }
  | action => action

def patchLatestExternalActionGas (gas : Gas) (state : State) : State :=
  match state.externalActions with
  | [] => state
  | action :: rest =>
      { state with externalActions := setCallActionGas gas action :: rest }

def returnedChildGas (effects : MeterEffects) (before : MeteredState) : Gas :=
  match effects.childGas?, before.evm.externalResults with
  | some childGas, result :: _ => min childGas (norm result.gasRemaining)
  | _, _ => 0

def finalizeAfterOpcode
    (effects : MeterEffects) (before after : MeteredState) : MeteredState :=
  let withPatchedAction :=
    match effects.childGas? with
    | none => after
    | some childGas =>
        { after with evm := patchLatestExternalActionGas childGas after.evm }
  let withReturnedGas := refundGas (returnedChildGas effects before) withPatchedAction
  consumeRemainingGasIfExceptional withReturnedGas

def applyChargedOpcode
    (opcode : Opcode) (effects : MeterEffects) (state : MeteredState) :
    MeteredState :=
  let withEffects := applyMeterEffects effects state
  let stepped :=
    if opcode = Opcode.gas then
      { withEffects with evm := stepGasOpcode withEffects.evm withEffects.gasRemaining }
    else
      { withEffects with evm := stepOpcode opcode withEffects.evm }
  finalizeAfterOpcode effects state stepped

def meteredStepOpcode
    (model : CostModel) (opcode : Opcode) (state : MeteredState) :
    MeteredState :=
  let effects := model.opcodeCost opcode state
  match chargeGas effects.cost state with
  | some charged => applyChargedOpcode opcode effects charged
  | none => setOutOfGas effects.cost state

def meteredStepInvalidOpcode
    (model : CostModel) (op : Byte) (state : MeteredState) : MeteredState :=
  let effects := model.invalidOpcodeCost op state
  match chargeGas effects.cost state with
  | some charged =>
      consumeRemainingGasIfExceptional
        { applyMeterEffects effects charged with evm := step charged.evm }
  | none => setOutOfGas effects.cost state

def meteredStep (model : CostModel) (state : MeteredState) : MeteredState :=
  if state.stopped then
    state
  else
    match state.evm.code[state.evm.pc]? with
    | none => { state with evm := step state.evm }
    | some op =>
        match decodeOpcode op with
        | some opcode => meteredStepOpcode model opcode state
        | none => meteredStepInvalidOpcode model op state

def meteredRunFuel (model : CostModel) : Nat → MeteredState → MeteredState
  | 0, state => state
  | fuel + 1, state =>
      if state.stopped then
        state
      else
        meteredRunFuel model fuel (meteredStep model state)

def runWithGas
    (model : CostModel) (fuel gasRemaining : Nat) (state : State) :
    MeteredState :=
  meteredRunFuel model fuel (MeteredState.ofState state gasRemaining)

def runWithOsakaGas (fuel gasRemaining : Nat) (state : State) :
    MeteredState :=
  meteredRunFuel osakaCostModel fuel
    (MeteredState.ofStateOsaka state gasRemaining)

theorem meteredStepOpcode_projects_nonGas_noChild
    (model : CostModel) (opcode : Opcode) (state : MeteredState)
    (hNotGas : opcode ≠ Opcode.gas)
    (hNoChild : (model.opcodeCost opcode state).childGas? = none)
    (hEnough : (model.opcodeCost opcode state).cost <= state.gasRemaining) :
    (meteredStepOpcode model opcode state).evm =
      stepOpcode opcode state.evm := by
  simp [meteredStepOpcode, chargeGas, applyChargedOpcode,
    finalizeAfterOpcode, returnedChildGas, refundGas,
    consumeRemainingGasIfExceptional, applyMeterEffects,
    addAccessedAddresses, addAccessedStorageKeys, hEnough, hNotGas, hNoChild]
  split <;> rfl

theorem chargeGas_gasUsed_of_enough
    (cost : Gas) (state : MeteredState)
    (hEnough : cost <= state.gasRemaining) :
    (chargeGas cost state).map (fun charged => charged.gasUsed) =
      some (state.gasUsed + cost) := by
  simp [chargeGas, hEnough]

def meteredAddExample : MeteredState :=
  meteredStepOpcode defaultCostModel Opcode.add
    { MeteredState.ofState { State.empty with stack := [2, 6] } 3 with
      gasUsed := 4 }

example : meteredAddExample.evm.stack = [8] := by
  native_decide

example : meteredAddExample.gasRemaining = 0 := by
  native_decide

example : meteredAddExample.gasUsed = 7 := by
  native_decide

example :
    (meteredStepOpcode defaultCostModel Opcode.add
      (MeteredState.ofState { State.empty with stack := [2, 6] } 2)).gasError? =
      some (GasError.outOfGas 3 2) := by
  native_decide

example :
    (meteredStep defaultCostModel
      (MeteredState.ofState { State.empty with code := [0x5a] } 10)).evm.stack =
      [8] := by
  native_decide

example :
    (meteredStep defaultCostModel
      (MeteredState.ofState { State.empty with code := [0x5a] } 10)).gasUsed =
      2 := by
  native_decide

def meteredMstoreExample : MeteredState :=
  runWithGas defaultCostModel 4 11
    { State.empty with code := [0x60, 0x2a, 0x5f, 0x52, 0x00] }

example : meteredMstoreExample.evm.memory.size = 32 := by
  native_decide

example : meteredMstoreExample.gasRemaining = 0 := by
  native_decide

example : meteredMstoreExample.gasUsed = 11 := by
  native_decide

example :
    (runWithGas defaultCostModel 3 8
      { State.empty with code := [0x60, 0x2a, 0x5f, 0x52] }).gasError? =
      some (GasError.outOfGas 6 3) := by
  native_decide

example :
    (meteredStepOpcode defaultCostModel Opcode.add
      (MeteredState.ofState { State.empty with stack := [2, 6] } 3)).evm =
      stepOpcode Opcode.add { State.empty with stack := [2, 6] } := by
  native_decide

example :
    (osakaOpcodeEffects Opcode.exp
      (MeteredState.ofState { State.empty with stack := [2, 256] } 1000)).cost =
      110 := by
  native_decide

example :
    (osakaOpcodeEffects Opcode.clz
      (MeteredState.ofState { State.empty with stack := [1] } 1000)).cost =
      5 := by
  native_decide

example : calldataTokenCount [0, 1, 2] = 9 := by
  native_decide

example : calldataFloorGasCost [0, 1, 2] = 21090 := by
  native_decide

example : intrinsicGasCost [0, 1, 2] false 1 2 0 = 27236 := by
  native_decide

example : linearPrecompileGas 60 12 33 = 84 := by
  native_decide

example : modexpInputWithinOsakaBounds 1024 1024 1024 = true := by
  native_decide

example : modexpInputWithinOsakaBounds 1025 1 1 = false := by
  native_decide

example : modexpGasCost 0 0 0 0 = 500 := by
  native_decide

example : modexpGasCost 64 64 1 2 = 500 := by
  native_decide

def coldSloadExample : MeteredState :=
  meteredStepOpcode osakaCostModel Opcode.sload
    (MeteredState.ofState
      { State.empty with
        stack := [7],
        call := { ({} : CallContext) with address := 1 },
        accounts := [(1, { ({} : Account) with storage := [(7, 42)] })] }
      2100)

example : coldSloadExample.evm.stack = [42] := by
  native_decide

example : coldSloadExample.gasUsed = 2100 := by
  native_decide

example :
    storageKeyIn (1, 7) coldSloadExample.accessedStorageKeys = true := by
  native_decide

def warmSloadExample : MeteredState :=
  meteredStepOpcode osakaCostModel Opcode.sload
    { MeteredState.ofState
        { State.empty with
          stack := [7],
          call := { ({} : CallContext) with address := 1 },
          accounts := [(1, { ({} : Account) with storage := [(7, 42)] })] }
        100 with
      accessedStorageKeys := [(1, 7)] }

example : warmSloadExample.gasUsed = 100 := by
  native_decide

def sstoreClearExample : MeteredState :=
  meteredStepOpcode osakaCostModel Opcode.sstore
    (MeteredState.ofState
      { State.empty with
        stack := [7, 0],
        call := { ({} : CallContext) with address := 1 },
        accounts := [(1, { ({} : Account) with storage := [(7, 5)] })] }
      5000)

example : sstoreClearExample.gasUsed = 5000 := by
  native_decide

example : sstoreClearExample.refund = 4800 := by
  native_decide

def callGasExampleState : State :=
  { State.empty with
    stack := [1000, 2, 0, 0, 0, 0, 0],
    call := { ({} : CallContext) with address := 1 },
    accounts := [(2, { ({} : Account) with nonce := 1 })],
    externalResults := [{ success := true, gasRemaining := 123 }] }

def callGasExample : MeteredState :=
  meteredStepOpcode osakaCostModel Opcode.call
    { MeteredState.ofStateOsaka callGasExampleState 10000 with
      accessedAddresses := [] }

example : callGasExample.gasUsed = 3477 := by
  native_decide

example : callGasExample.gasRemaining = 6523 := by
  native_decide

example :
    callGasExample.evm.externalActions =
      [ExternalAction.call
        { kind := ExternalCallKind.call,
          gas := 1000,
          to := 2,
          value := 0,
          input := [],
          retOffset := 0,
          retSize := 0,
          caller := 1,
          address := 2,
          isStatic := false }] := by
  native_decide

end BytecodeGas
end SolidCoreYulCore

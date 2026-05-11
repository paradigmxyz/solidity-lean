import SolidCore.Spine.L05_Bytecode.Syntax
import SolidCoreYulCore.BytecodeEvm

namespace SolidCore
namespace Spine
namespace L06_Evm
namespace Syntax

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := SolidCoreYulCore.BytecodeEvm.Byte
abbrev Bytes := SolidCoreYulCore.BytecodeEvm.Bytes
abbrev Opcode := SolidCoreYulCore.BytecodeEvm.Opcode
abbrev Pc := L05_Bytecode.Syntax.Pc

structure Address where
  value : Word
  deriving Repr

structure Account where
  nonce : Nat := 0
  balance : Word := 0
  code : Bytes := []
  storage : List (Word × Word) := []
  transientStorage : List (Word × Word) := []
  destroyed : Bool := false
  deriving Repr

structure AccessSet where
  warmAddresses : List Address := []
  warmStorage : List (Address × Word) := []
  deriving Repr

structure World where
  accounts : List (Address × Account) := []
  accessSet : AccessSet := {}
  refunds : Nat := 0
  deriving Repr

structure BlockContext where
  coinbase : Address
  timestamp : Word := 0
  number : Word := 0
  prevrandao : Word := 0
  gaslimit : Word := 0
  chainid : Word := 1
  basefee : Word := 0
  blobbasefee : Word := 0
  blockhashes : List (Word × Word) := []
  deriving Repr

structure TxContext where
  origin : Address
  gasprice : Word := 0
  blobhashes : List Word := []
  deriving Repr

inductive CallKind where
  | call
  | callcode
  | delegatecall
  | staticcall
  deriving Repr

inductive CreateKind where
  | create
  | create2
  deriving Repr

structure Message where
  kind : CallKind := CallKind.call
  caller : Address
  address : Address
  codeAddress : Address
  value : Word := 0
  calldata : Bytes := []
  gas : Nat := 0
  static : Bool := false
  depth : Nat := 0
  deriving Repr

structure Machine where
  pc : Pc
  gas : Nat := 0
  stack : List Word := []
  memory : Bytes := []
  returndata : Bytes := []
  code : Bytes := []
  deriving Repr

structure Log where
  address : Address
  topics : List Word := []
  data : Bytes := []
  deriving Repr

inductive HaltReason where
  | stop
  | returnOp : Bytes -> HaltReason
  | revert : Bytes -> HaltReason
  | invalid
  | outOfGas
  | stackUnderflow
  | stackOverflow
  | badJumpDest
  | staticViolation
  | callDepthExceeded
  deriving Repr

structure Frame where
  message : Message
  machine : Machine
  logs : List Log := []
  journal : List (Address × Word × Word) := []
  deriving Repr

structure State where
  world : World
  block : BlockContext
  tx : TxContext
  frames : List Frame := []
  deriving Repr

inductive StepResult where
  | running : State -> StepResult
  | halted : State -> HaltReason -> StepResult
  | needsHostCall : State -> Message -> StepResult
  | needsCreate : State -> CreateKind -> Message -> Bytes -> StepResult
  deriving Repr

structure Program where
  code : Bytes
  entry : Pc
  deriving Repr

end Syntax
end L06_Evm
end Spine
end SolidCore

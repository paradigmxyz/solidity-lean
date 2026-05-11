import SolidCore.Spine.L03_GeneratedYul.Syntax

namespace SolidCore
namespace Spine
namespace L04_StackCfg
namespace Syntax

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := Nat

structure Label where
  value : Nat
  deriving Repr

structure FunctionId where
  value : Nat
  deriving Repr

inductive Atom where
  | word : Word -> Atom
  | label : Label -> Atom
  | function : FunctionId -> Atom
  deriving Repr

inductive PrimOp where
  | add
  | mul
  | sub
  | div
  | sdiv
  | modOp
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | andOp
  | orOp
  | xor
  | notOp
  | byteOp
  | shl
  | shr
  | sar
  | keccak256
  | mload
  | mstore
  | mstore8
  | sload
  | sstore
  | calldataload
  | calldatacopy
  | returndatacopy
  | codecopy
  | extcodecopy
  | log : Nat -> PrimOp
  | create
  | create2
  | call
  | callcode
  | delegatecall
  | staticcall
  | selfdestruct
  deriving Repr

inductive EnvOp where
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldatasize
  | codesize
  | gasprice
  | extcodesize
  | returndatasize
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | pc
  | msize
  | gas
  deriving Repr

structure Shuffle where
  inputs : Nat
  outputs : List Nat := []
  deriving Repr

inductive PseudoInstr where
  | shuffle : Shuffle -> PseudoInstr
  | dropMany : Nat -> PseudoInstr
  | copyTop : Nat -> PseudoInstr
  | materializeDataOffset : L03_GeneratedYul.Syntax.DataLabel -> PseudoInstr
  | materializeDataSize : L03_GeneratedYul.Syntax.DataLabel -> PseudoInstr
  deriving Repr

inductive Instr where
  | push : Atom -> Instr
  | dup : Nat -> Instr
  | swap : Nat -> Instr
  | pop : Instr
  | op : PrimOp -> Instr
  | env : EnvOp -> Instr
  | pseudo : PseudoInstr -> Instr
  deriving Repr

inductive Term where
  | jump : Label -> Term
  | jumpi : Label -> Label -> Term
  | switch : List (Word × Label) -> Label -> Term
  | call : FunctionId -> Nat -> Nat -> Label -> Term
  | returnOp
  | revert
  | stop
  | invalid
  deriving Repr

structure StackSignature where
  inputDepth : Nat
  outputDepth : Option Nat := none
  maxExtraDepth : Nat := 0
  deriving Repr

structure Block where
  label : Label
  signature : StackSignature
  body : List Instr := []
  term : Term
  deriving Repr

structure Function where
  id : FunctionId
  entry : Label
  params : Nat := 0
  returns : Nat := 0
  blocks : List Block := []
  deriving Repr

structure Program where
  entry : Label
  blocks : List Block := []
  functions : List Function := []
  deriving Repr

end Syntax
end L04_StackCfg
end Spine
end SolidCore

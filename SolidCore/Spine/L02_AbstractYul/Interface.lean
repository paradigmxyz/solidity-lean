import SolidCore.Spine.L01_ValidSolidity.Interface

namespace SolidCore
namespace Spine
namespace L02_AbstractYul

abbrev Word := L01_ValidSolidity.Word
abbrev Name := L01_ValidSolidity.Name

structure ProcId where
  value : Nat
  deriving Repr

structure EntryId where
  value : Nat
  deriving Repr

structure LocalId where
  value : Nat
  deriving Repr

inductive Ty where
  | unit
  | bool
  | word
  | address
  | bytes
  | tuple : List Ty -> Ty
  deriving Repr

inductive EnvRead where
  | address
  | caller
  | callvalue
  | calldataSize
  | returndataSize
  | origin
  | coinbase
  | timestamp
  | number
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | gas
  deriving Repr

inductive UnaryOp where
  | iszero
  | bitNot
  | negChecked
  | negUnchecked
  deriving Repr

inductive BinaryOp where
  | addChecked
  | subChecked
  | mulChecked
  | addUnchecked
  | subUnchecked
  | mulUnchecked
  | div
  | mod
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | sar
  | lt
  | gt
  | slt
  | sgt
  | eq
  deriving Repr

inductive Expr where
  | word : Word -> Expr
  | bool : Bool -> Expr
  | local : LocalId -> Expr
  | tuple : List Expr -> Expr
  | select : Expr -> Nat -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | env : EnvRead -> Expr
  | storageRead : L01_ValidSolidity.StorageId -> List Expr -> Expr
  | calldataRead : Expr -> Ty -> Expr
  | memoryRead : Expr -> Ty -> Expr
  | keccak : List Expr -> Expr
  deriving Repr

inductive ExternalCallKind where
  | call
  | staticcall
  | delegatecall
  deriving Repr

structure ExternalCall where
  kind : ExternalCallKind
  target : Expr
  value : Option Expr := none
  calldata : Expr
  gas : Option Expr := none
  expectedReturns : List Ty := []
  deriving Repr

inductive Rhs where
  | expr : Expr -> Rhs
  | procCall : ProcId -> List Expr -> Rhs
  | externalCall : ExternalCall -> Rhs
  | allocateBytes : Expr -> Rhs
  | abiEncode : List Expr -> Rhs
  | abiDecode : Expr -> List Ty -> Rhs
  deriving Repr

inductive Effect where
  | storageWrite : L01_ValidSolidity.StorageId -> List Expr -> Expr -> Effect
  | memoryWrite : Expr -> Expr -> Ty -> Effect
  | emitEvent : L01_ValidSolidity.EventId -> List Expr -> List Expr -> Effect
  | returnDataCopy : Expr -> Expr -> Expr -> Effect
  | selfdestruct : Expr -> Effect
  deriving Repr

inductive Completion where
  | returnValues : List Expr -> Completion
  | revertError : L01_ValidSolidity.ErrorId -> List Expr -> Completion
  | panic : Word -> Completion
  | rawReturn : Expr -> Expr -> Completion
  | rawRevert : Expr -> Expr -> Completion
  | break
  | continue
  deriving Repr

inductive Stmt where
  | skip
  | block : List Stmt -> Stmt
  | let1 : LocalId -> Ty -> Rhs -> Stmt
  | letMany : List (LocalId × Ty) -> Rhs -> Stmt
  | assign : LocalId -> Rhs -> Stmt
  | assignMany : List LocalId -> Rhs -> Stmt
  | effect : Effect -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | loop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | complete : Completion -> Stmt
  deriving Repr

structure Binding where
  id : LocalId
  ty : Ty
  sourceName : Option Name := none
  deriving Repr

structure Proc where
  id : ProcId
  sourceFunction : Option L01_ValidSolidity.FunctionId := none
  params : List Binding := []
  returns : List Binding := []
  body : Stmt
  deriving Repr

structure Entry where
  id : EntryId
  sourceFunction : L01_ValidSolidity.FunctionId
  params : List Binding := []
  body : Stmt
  payable : Bool := false
  deriving Repr

structure Program where
  entries : List Entry := []
  procs : List Proc := []
  init : Option ProcId := none
  deriving Repr

structure WF (_program : Program) : Prop where
  localsScoped : True := by trivial
  procsClosed : True := by trivial
  completionsScoped : True := by trivial
  effectsTyped : True := by trivial

end L02_AbstractYul
end Spine
end SolidCore

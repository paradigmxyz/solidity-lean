import SolidCore.Spine.L00_SourceSolidity.Interface

namespace SolidCore
namespace Spine
namespace L01_ValidSolidity

abbrev Name := L00_SourceSolidity.Name
abbrev Word := L00_SourceSolidity.Word

structure ContractId where
  value : Nat
  deriving Repr

structure FunctionId where
  value : Nat
  deriving Repr

structure ModifierId where
  value : Nat
  deriving Repr

structure EventId where
  value : Nat
  deriving Repr

structure ErrorId where
  value : Nat
  deriving Repr

structure StructId where
  value : Nat
  deriving Repr

structure EnumId where
  value : Nat
  deriving Repr

structure StorageId where
  value : Nat
  deriving Repr

structure LocalId where
  value : Nat
  deriving Repr

structure ParamId where
  value : Nat
  deriving Repr

structure ReturnId where
  value : Nat
  deriving Repr

inductive DataLocation where
  | storage
  | memory
  | calldata
  deriving Repr

inductive Visibility where
  | public_
  | private_
  | internal_
  | external_
  deriving Repr

inductive StateMutability where
  | pure
  | view
  | nonpayable
  | payable
  deriving Repr

inductive Ty where
  | bool
  | address : Bool -> Ty
  | uint : Nat -> Ty
  | int : Nat -> Ty
  | bytesN : Nat -> Ty
  | bytes
  | string
  | array : Ty -> Option Nat -> DataLocation -> Ty
  | mapping : Ty -> Ty -> Ty
  | tuple : List Ty -> Ty
  | struct : StructId -> Ty
  | enum : EnumId -> Ty
  | contract : ContractId -> Ty
  | function : List Ty -> List Ty -> StateMutability -> Visibility -> Ty
  deriving Repr

inductive BindingId where
  | local : LocalId -> BindingId
  | param : ParamId -> BindingId
  | ret : ReturnId -> BindingId
  deriving Repr

inductive Literal where
  | bool : Bool -> Literal
  | word : Word -> Literal
  | string : String -> Literal
  | bytes : List Nat -> Literal
  | address : Word -> Literal
  deriving Repr

inductive UnaryOp where
  | logicalNot
  | bitNot
  | neg
  deriving Repr

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | mod
  | exp
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | sar
  | lt
  | gt
  | le
  | ge
  | eq
  | ne
  | boolAnd
  | boolOr
  deriving Repr

inductive AssignOp where
  | assign
  | addAssign
  | subAssign
  | mulAssign
  | divAssign
  | modAssign
  | bitAndAssign
  | bitOrAssign
  | bitXorAssign
  | shlAssign
  | shrAssign
  | sarAssign
  deriving Repr

inductive CallKind where
  | internal : FunctionId -> CallKind
  | external : FunctionId -> CallKind
  | modifierCall : ModifierId -> CallKind
  | constructor : ContractId -> CallKind
  | typeConversion : Ty -> CallKind
  | lowLevelCall
  | lowLevelDelegateCall
  | lowLevelStaticCall
  | builtin : Name -> CallKind
  deriving Repr

mutual

inductive Expr where
  | literal : Ty -> Literal -> Expr
  | read : Ty -> LValue -> Expr
  | functionRef : Ty -> FunctionId -> Expr
  | eventRef : Ty -> EventId -> Expr
  | errorRef : Ty -> ErrorId -> Expr
  | unary : Ty -> UnaryOp -> Expr -> Expr
  | binary : Ty -> BinaryOp -> Expr -> Expr -> Expr
  | ternary : Ty -> Expr -> Expr -> Expr -> Expr
  | tuple : Ty -> List TupleExprItem -> Expr
  | array : Ty -> List Expr -> Expr
  | call : Ty -> CallKind -> List Expr -> Expr
  | callWithValue : Ty -> CallKind -> Expr -> List Expr -> Expr
  | memberValue : Ty -> Expr -> Name -> Expr
  | assignment : Ty -> LValue -> AssignOp -> Expr -> Expr
  deriving Repr

inductive LValue where
  | binding : BindingId -> Ty -> LValue
  | storage : StorageId -> Ty -> LValue
  | tuple : List TupleLValueItem -> Ty -> LValue
  | index : LValue -> Expr -> Ty -> LValue
  | member : LValue -> Name -> Ty -> LValue
  deriving Repr

inductive TupleExprItem where
  | hole
  | value : Expr -> TupleExprItem
  deriving Repr

inductive TupleLValueItem where
  | hole
  | value : LValue -> TupleLValueItem
  deriving Repr

end

structure Parameter where
  id : ParamId
  sourceName : Option Name := none
  ty : Ty
  location : Option DataLocation := none
  deriving Repr

structure ReturnVar where
  id : ReturnId
  sourceName : Option Name := none
  ty : Ty
  location : Option DataLocation := none
  deriving Repr

structure LocalDecl where
  id : LocalId
  sourceName : Option Name := none
  ty : Ty
  location : Option DataLocation := none
  init : Option Expr := none
  deriving Repr

mutual

inductive Stmt where
  | skip
  | block : List LocalDecl -> List Stmt -> Stmt
  | expr : Expr -> Stmt
  | assign : LValue -> AssignOp -> Expr -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : List LocalDecl -> Option Expr -> Option Stmt -> Stmt -> Stmt
  | tryCatch : Expr -> List CatchClause -> Stmt
  | emitEvent : EventId -> List Expr -> Stmt
  | revert : ErrorId -> List Expr -> Stmt
  | returnValues : List Expr -> Stmt
  | break
  | continue
  | unchecked : Stmt -> Stmt
  | modifierPlaceholder
  deriving Repr

inductive CatchClause where
  | clause : Option ErrorId -> List Parameter -> Stmt -> CatchClause
  deriving Repr

end

structure ModifierInvocation where
  id : ModifierId
  args : List Expr := []
  deriving Repr

structure StorageDecl where
  id : StorageId
  sourceName : Name
  ty : Ty
  constant : Bool := false
  immutable : Bool := false
  init : Option Expr := none
  deriving Repr

structure EventParam where
  sourceName : Option Name := none
  ty : Ty
  indexed : Bool := false
  deriving Repr

structure EventDecl where
  id : EventId
  sourceName : Name
  params : List EventParam := []
  anonymous : Bool := false
  deriving Repr

structure ErrorDecl where
  id : ErrorId
  sourceName : Name
  params : List Parameter := []
  deriving Repr

structure StructField where
  sourceName : Name
  ty : Ty
  deriving Repr

structure StructDecl where
  id : StructId
  sourceName : Name
  fields : List StructField := []
  deriving Repr

structure EnumDecl where
  id : EnumId
  sourceName : Name
  cases : List Name := []
  deriving Repr

structure FunctionDecl where
  id : FunctionId
  sourceName : Option Name := none
  contract : ContractId
  params : List Parameter := []
  returns : List ReturnVar := []
  visibility : Visibility
  mutability : StateMutability
  modifiers : List ModifierInvocation := []
  body : Option Stmt := none
  virtual : Bool := false
  overrides : List FunctionId := []
  deriving Repr

structure ModifierDecl where
  id : ModifierId
  sourceName : Name
  contract : ContractId
  params : List Parameter := []
  body : Option Stmt := none
  virtual : Bool := false
  overrides : List ModifierId := []
  deriving Repr

structure ContractDecl where
  id : ContractId
  sourceName : Name
  bases : List ContractId := []
  linearizedBases : List ContractId := []
  storage : List StorageDecl := []
  functions : List FunctionDecl := []
  modifiers : List ModifierDecl := []
  events : List EventDecl := []
  errors : List ErrorDecl := []
  structs : List StructDecl := []
  enums : List EnumDecl := []
  deriving Repr

structure Program where
  contracts : List ContractDecl := []
  entryContract : Option ContractId := none
  deriving Repr

structure WF (_program : Program) : Prop where
  namesResolved : True := by trivial
  typesChecked : True := by trivial
  declarationsChecked : True := by trivial
  acceptedFragment : True := by trivial

end L01_ValidSolidity
end Spine
end SolidCore

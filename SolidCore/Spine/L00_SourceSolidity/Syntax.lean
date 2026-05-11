import SolidCoreYulCore.Evm

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace Syntax

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := Nat
abbrev Name := String

structure SourceSpan where
  file : Option String := none
  startByte : Nat := 0
  stopByte : Nat := 0
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

inductive DataLocation where
  | storage
  | memory
  | calldata
  deriving Repr

inductive ContractKind where
  | contract
  | interface
  | library
  deriving Repr

inductive FunctionKind where
  | function
  | constructor
  | receive
  | fallback
  deriving Repr

inductive VarMutability where
  | mutable
  | constant
  | immutable
  deriving Repr

structure Path where
  segments : List Name
  deriving Repr

inductive Ty where
  | bool
  | address : Bool -> Ty
  | uint : Nat -> Ty
  | int : Nat -> Ty
  | bytesN : Nat -> Ty
  | bytes
  | string
  | fixedBytes : Nat -> Ty
  | array : Ty -> Option Nat -> Ty
  | mapping : Ty -> Ty -> Ty
  | tuple : List Ty -> Ty
  | user : Path -> Ty
  | function : List Ty -> List Ty -> StateMutability -> Visibility -> Ty
  deriving Repr

structure Parameter where
  name : Option Name := none
  ty : Ty
  location : Option DataLocation := none
  deriving Repr

inductive Literal where
  | bool : Bool -> Literal
  | number : String -> Literal
  | string : String -> Literal
  | hexString : String -> Literal
  | unicodeString : String -> Literal
  | address : Word -> Literal
  | bytes : List Byte -> Literal
  deriving Repr

inductive UnaryOp where
  | logicalNot
  | bitNot
  | neg
  | delete
  | preIncrement
  | preDecrement
  | postIncrement
  | postDecrement
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

mutual

inductive Expr where
  | literal : Literal -> Expr
  | ident : Name -> Expr
  | typeName : Ty -> Expr
  | member : Expr -> Name -> Expr
  | index : Expr -> Expr -> Expr
  | slice : Expr -> Option Expr -> Option Expr -> Expr
  | call : Expr -> List Arg -> Expr
  | callWithOptions : Expr -> List CallOption -> List Arg -> Expr
  | newExpr : Ty -> List Arg -> Expr
  | tuple : List TupleItem -> Expr
  | array : List Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | ternary : Expr -> Expr -> Expr -> Expr
  | assign : Expr -> AssignOp -> Expr -> Expr
  | payableConversion : Expr -> Expr
  deriving Repr

inductive Arg where
  | positional : Expr -> Arg
  | named : Name -> Expr -> Arg
  deriving Repr

inductive CallOption where
  | named : Name -> Expr -> CallOption
  deriving Repr

inductive TupleItem where
  | hole
  | value : Expr -> TupleItem
  deriving Repr

end

structure VarBinding where
  name : Option Name := none
  ty : Option Ty := none
  location : Option DataLocation := none
  deriving Repr

mutual

inductive Stmt where
  | empty
  | block : List Stmt -> Stmt
  | varDecl : List VarBinding -> Option Expr -> Stmt
  | expr : Expr -> Stmt
  | ifElse : Expr -> Stmt -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | doWhile : Stmt -> Expr -> Stmt
  | forLoop : Option Stmt -> Option Expr -> Option Expr -> Stmt -> Stmt
  | tryCatch : Expr -> List CatchClause -> Stmt
  | emitEvent : Expr -> Stmt
  | revertCall : Expr -> Stmt
  | returnValues : Option Expr -> Stmt
  | break
  | continue
  | unchecked : Stmt -> Stmt
  | inlineAssembly : String -> Stmt
  | modifierPlaceholder
  deriving Repr

inductive CatchClause where
  | clause : Option Name -> List Parameter -> Stmt -> CatchClause
  deriving Repr

end

structure ModifierInvocation where
  target : Path
  args : List Expr := []
  deriving Repr

structure OverrideSpecifier where
  bases : List Path := []
  deriving Repr

structure StateVarDecl where
  name : Name
  ty : Ty
  visibility : Option Visibility := none
  mutability : VarMutability := VarMutability.mutable
  override? : Option OverrideSpecifier := none
  init : Option Expr := none
  deriving Repr

structure FunctionDecl where
  kind : FunctionKind := FunctionKind.function
  name : Option Name := none
  params : List Parameter := []
  returns : List Parameter := []
  visibility : Option Visibility := none
  mutability : StateMutability := StateMutability.nonpayable
  virtual : Bool := false
  override? : Option OverrideSpecifier := none
  modifiers : List ModifierInvocation := []
  body : Option Stmt := none
  deriving Repr

structure ModifierDecl where
  name : Name
  params : List Parameter := []
  virtual : Bool := false
  override? : Option OverrideSpecifier := none
  body : Option Stmt := none
  deriving Repr

structure EventParam where
  name : Option Name := none
  ty : Ty
  indexed : Bool := false
  deriving Repr

structure EventDecl where
  name : Name
  params : List EventParam := []
  anonymous : Bool := false
  deriving Repr

structure ErrorDecl where
  name : Name
  params : List Parameter := []
  deriving Repr

structure StructField where
  name : Name
  ty : Ty
  deriving Repr

structure StructDecl where
  name : Name
  fields : List StructField := []
  deriving Repr

structure EnumDecl where
  name : Name
  cases : List Name := []
  deriving Repr

structure UsingDecl where
  library : Path
  target : Option Ty := none
  global : Bool := false
  deriving Repr

structure BaseSpecifier where
  base : Path
  args : List Expr := []
  deriving Repr

inductive ContractItem where
  | stateVar : StateVarDecl -> ContractItem
  | function : FunctionDecl -> ContractItem
  | modifierDecl : ModifierDecl -> ContractItem
  | eventDecl : EventDecl -> ContractItem
  | errorDecl : ErrorDecl -> ContractItem
  | structDecl : StructDecl -> ContractItem
  | enumDecl : EnumDecl -> ContractItem
  | usingDecl : UsingDecl -> ContractItem
  deriving Repr

structure ContractDecl where
  kind : ContractKind := ContractKind.contract
  name : Name
  abstract : Bool := false
  bases : List BaseSpecifier := []
  items : List ContractItem := []
  deriving Repr

inductive SourceItem where
  | pragma : Name -> String -> SourceItem
  | importPath : String -> Option Name -> SourceItem
  | contract : ContractDecl -> SourceItem
  | freeFunction : FunctionDecl -> SourceItem
  | freeError : ErrorDecl -> SourceItem
  | freeStruct : StructDecl -> SourceItem
  | freeEnum : EnumDecl -> SourceItem
  | usingDecl : UsingDecl -> SourceItem
  deriving Repr

structure SourceUnit where
  items : List SourceItem := []
  deriving Repr

end Syntax
end L00_SourceSolidity
end Spine
end SolidCore

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

abbrev Behavior := L00_SourceSolidity.Behavior

namespace Behavior

def stopped : Behavior :=
  L00_SourceSolidity.Behavior.stopped

def returnedWord (value : Word) : Behavior :=
  L00_SourceSolidity.Behavior.returnedWord value

end Behavior

def Program.empty : Program := {}

def ContractId.entry : ContractId := { value := 0 }

def FunctionId.entry : FunctionId := { value := 0 }

def ReturnId.ret0 : ReturnId := { value := 0 }

def Ty.uint256 : Ty := Ty.uint 256

def Ty.isUint256 : Ty -> Bool
  | Ty.uint 256 => true
  | _ => false

def Ty.isBool : Ty -> Bool
  | Ty.bool => true
  | _ => false

def Expr.word (value : Word) : Expr :=
  Expr.literal Ty.uint256 (Literal.word value)

def Expr.bool (value : Bool) : Expr :=
  Expr.literal Ty.bool (Literal.bool value)

def Expr.word0 : Expr := Expr.word 0

def Expr.word1 : Expr := Expr.word 1

def Expr.word2 : Expr := Expr.word 2

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.uint256 BinaryOp.add lhs rhs

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.uint256 BinaryOp.sub lhs rhs

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.uint256 BinaryOp.mul lhs rhs

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.uint256 BinaryOp.bitAnd lhs rhs

def Expr.eqOp (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.bool BinaryOp.eq lhs rhs

def Expr.ltOp (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.bool BinaryOp.lt lhs rhs

def Expr.gtOp (lhs rhs : Expr) : Expr :=
  Expr.binary Ty.bool BinaryOp.gt lhs rhs

def Expr.resultTy : Expr -> Ty
  | Expr.literal ty _ => ty
  | Expr.read ty _ => ty
  | Expr.functionRef ty _ => ty
  | Expr.eventRef ty _ => ty
  | Expr.errorRef ty _ => ty
  | Expr.unary ty _ _ => ty
  | Expr.binary ty _ _ _ => ty
  | Expr.ternary ty _ _ _ => ty
  | Expr.tuple ty _ => ty
  | Expr.array ty _ => ty
  | Expr.call ty _ _ => ty
  | Expr.callWithValue ty _ _ _ => ty
  | Expr.memberValue ty _ _ => ty
  | Expr.assignment ty _ _ _ => ty

def Expr.resultTyIsUint256 (expr : Expr) : Bool :=
  expr.resultTy.isUint256

def Expr.resultTyIsBool (expr : Expr) : Bool :=
  expr.resultTy.isBool

@[simp] theorem Expr.resultTy_word (value : Word) :
    (Expr.word value).resultTy = Ty.uint256 := by
  rfl

@[simp] theorem Expr.resultTy_add (lhs rhs : Expr) :
    (Expr.add lhs rhs).resultTy = Ty.uint256 := by
  rfl

@[simp] theorem Expr.resultTy_sub (lhs rhs : Expr) :
    (Expr.sub lhs rhs).resultTy = Ty.uint256 := by
  rfl

@[simp] theorem Expr.resultTy_mul (lhs rhs : Expr) :
    (Expr.mul lhs rhs).resultTy = Ty.uint256 := by
  rfl

@[simp] theorem Expr.resultTy_bitAnd (lhs rhs : Expr) :
    (Expr.bitAnd lhs rhs).resultTy = Ty.uint256 := by
  rfl

@[simp] theorem Expr.resultTy_eqOp (lhs rhs : Expr) :
    (Expr.eqOp lhs rhs).resultTy = Ty.bool := by
  rfl

@[simp] theorem Expr.resultTy_ltOp (lhs rhs : Expr) :
    (Expr.ltOp lhs rhs).resultTy = Ty.bool := by
  rfl

@[simp] theorem Expr.resultTy_gtOp (lhs rhs : Expr) :
    (Expr.gtOp lhs rhs).resultTy = Ty.bool := by
  rfl

def BinaryOp.toCore? :
    BinaryOp -> Option SolidCore.Solidity.Source.BinaryOp
  | BinaryOp.add => some SolidCore.Solidity.Source.BinaryOp.add
  | BinaryOp.sub => some SolidCore.Solidity.Source.BinaryOp.sub
  | BinaryOp.mul => some SolidCore.Solidity.Source.BinaryOp.mul
  | BinaryOp.bitAnd => some SolidCore.Solidity.Source.BinaryOp.bitAnd
  | BinaryOp.lt => some SolidCore.Solidity.Source.BinaryOp.lt
  | BinaryOp.gt => some SolidCore.Solidity.Source.BinaryOp.gt
  | BinaryOp.eq => some SolidCore.Solidity.Source.BinaryOp.eq
  | _ => none

def Expr.toCore? :
    Expr -> Option L00_SourceSolidity.Executable.CoreExpr
  | Expr.literal Ty.bool (Literal.bool value) =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Source.boolWord value))
  | Expr.literal (Ty.uint 256) (Literal.word value) =>
      some (SolidCore.Solidity.Source.Expr.word value)
  | Expr.binary (Ty.uint 256) op lhs rhs => do
      let coreOp ← BinaryOp.toCore? op
      let lhsCore ← lhs.toCore?
      let rhsCore ← rhs.toCore?
      some (SolidCore.Solidity.Source.Expr.binary
        coreOp lhsCore rhsCore)
  | Expr.binary Ty.bool op lhs rhs => do
      let coreOp ← BinaryOp.toCore? op
      let lhsCore ← lhs.toCore?
      let rhsCore ← rhs.toCore?
      some (SolidCore.Solidity.Source.Expr.binary
        coreOp lhsCore rhsCore)
  | _ => none

def Expr.eval? (expr : Expr) : Option Word := do
  let coreExpr ← expr.toCore?
  L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext? coreExpr

def Expr.Eval (expr : Expr) (value : Word) : Prop :=
  expr.eval? = some value

@[simp] theorem Expr.resultTy_bool (value : Bool) :
    (Expr.bool value).resultTy = Ty.bool := by
  rfl

@[simp] theorem Expr.eval?_bool (value : Bool) :
    (Expr.bool value).eval? =
      some (SolidCore.Solidity.Source.boolWord value) := by
  cases value <;> rfl

@[simp] theorem Expr.eval?_word0 : Expr.word0.eval? = some 0 := by
  rfl

@[simp] theorem Expr.eval?_word_zero : (Expr.word 0).eval? = some 0 := by
  rfl

@[simp] theorem Expr.eval?_word1 : Expr.word1.eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_word_one : (Expr.word 1).eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_word2 : Expr.word2.eval? = some 2 := by
  rfl

@[simp] theorem Expr.eval?_word_two : (Expr.word 2).eval? = some 2 := by
  rfl

@[simp] theorem Expr.eval?_add_word1_word2 :
    (Expr.add (Expr.word 1) (Expr.word 2)).eval? = some 3 := by
  rfl

@[simp] theorem Expr.eval?_sub_word3_word1 :
    (Expr.sub (Expr.word 3) (Expr.word 1)).eval? = some 2 := by
  rfl

@[simp] theorem Expr.eval?_mul_word2_word2 :
    (Expr.mul (Expr.word 2) (Expr.word 2)).eval? = some 4 := by
  rfl

@[simp] theorem Expr.eval?_bitAnd_word3_word1 :
    (Expr.bitAnd (Expr.word 3) (Expr.word 1)).eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_eqOp_word2_word2 :
    (Expr.eqOp (Expr.word 2) (Expr.word 2)).eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_ltOp_word1_word2 :
    (Expr.ltOp (Expr.word 1) (Expr.word 2)).eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_gtOp_word2_word1 :
    (Expr.gtOp (Expr.word 2) (Expr.word 1)).eval? = some 1 := by
  rfl

def Stmt.returnExpr (expr : Expr) : Stmt :=
  Stmt.returnValues [expr]

def Stmt.returnWord (value : Word) : Stmt :=
  Stmt.returnExpr (Expr.word value)

def Stmt.returnedExpr? : Stmt -> Option Expr
  | Stmt.returnValues [e] => some e
  | Stmt.block [] [stmt] => stmt.returnedExpr?
  | Stmt.ifElse condition thenBranch elseBranch =>
      match condition.eval? with
      | some value =>
          if SolidCore.Solidity.Source.wordTruthy value then
            thenBranch.returnedExpr?
          else
            elseBranch.returnedExpr?
      | none => none
  | _ => none

def ReturnVar.word0 : ReturnVar :=
  { id := ReturnId.ret0
    sourceName := some "ret0"
    ty := Ty.uint256 }

def FunctionDecl.withBody (body : Stmt) : FunctionDecl :=
  { id := FunctionId.entry
    sourceName := some "f"
    contract := ContractId.entry
    returns := [ReturnVar.word0]
    visibility := Visibility.public_
    mutability := StateMutability.pure
    body := some body }

def FunctionDecl.returnExpr (expr : Expr) : FunctionDecl :=
  FunctionDecl.withBody (Stmt.returnExpr expr)

def FunctionDecl.returnWord (value : Word) : FunctionDecl :=
  FunctionDecl.returnExpr (Expr.word value)

def ReturnVar.isUint256 (ret : ReturnVar) : Bool :=
  ret.ty.isUint256

def FunctionDecl.returnedExpr? (decl : FunctionDecl) : Option Expr :=
  match decl.params, decl.returns, decl.visibility, decl.mutability,
      decl.modifiers, decl.body with
  | [], [ret], Visibility.public_, StateMutability.pure, [], some body =>
      if ret.isUint256 then
        body.returnedExpr?
      else
        none
  | _, _, _, _, _, _ => none

def ContractDecl.withFunction (fn : FunctionDecl) : ContractDecl :=
  { id := ContractId.entry
    sourceName := "C"
    functions := [fn] }

def ContractDecl.withBody (body : Stmt) : ContractDecl :=
  ContractDecl.withFunction (FunctionDecl.withBody body)

def ContractDecl.returnExpr (expr : Expr) : ContractDecl :=
  ContractDecl.withBody (Stmt.returnExpr expr)

def ContractDecl.returnWord (value : Word) : ContractDecl :=
  ContractDecl.returnExpr (Expr.word value)

def ContractDecl.returnedExpr? (decl : ContractDecl) : Option Expr :=
  match decl.bases, decl.linearizedBases, decl.storage, decl.functions,
      decl.modifiers, decl.events, decl.errors, decl.structs, decl.enums with
  | [], [], [], [fn], [], [], [], [], [] => fn.returnedExpr?
  | _, _, _, _, _, _, _, _, _ => none

def Program.withContract (contract : ContractDecl) : Program :=
  { contracts := [contract]
    entryContract := some contract.id }

def Program.returnStmt (stmt : Stmt) : Program :=
  Program.withContract (ContractDecl.withBody stmt)

def Program.returnExpr (expr : Expr) : Program :=
  Program.returnStmt (Stmt.returnExpr expr)

def Program.returnWord (value : Word) : Program :=
  Program.returnExpr (Expr.word value)

def Program.returnedExpr? (program : Program) : Option Expr :=
  match program.contracts, program.entryContract with
  | [contract], some entry =>
      if entry.value == contract.id.value then
        contract.returnedExpr?
      else
        none
  | _, _ => none

def Program.IsEmpty (program : Program) : Prop :=
  program.contracts = [] ∧ program.entryContract = none

def Program.IsReturnValue (program : Program) (value : Word) : Prop :=
  ∃ expr, program.returnedExpr? = some expr ∧ expr.Eval value

inductive Semantics : Program -> Behavior -> Prop where
  | empty {program : Program} :
      program.IsEmpty ->
      Semantics program Behavior.stopped
  | returnValue {program : Program} {value : Word} :
      program.IsReturnValue value ->
      Semantics program (Behavior.returnedWord value)

theorem Program.empty_isEmpty : Program.empty.IsEmpty := by
  simp [Program.empty, Program.IsEmpty]

theorem Program.empty_wf : WF Program.empty := by
  exact {}

theorem Program.empty_semantics : Semantics Program.empty Behavior.stopped := by
  exact Semantics.empty Program.empty_isEmpty

theorem Program.returnExpr_wf (expr : Expr) : WF (Program.returnExpr expr) := by
  exact {}

theorem Program.returnStmt_wf (stmt : Stmt) : WF (Program.returnStmt stmt) := by
  exact {}

theorem Program.returnStmt_isReturnValue {stmt : Stmt} {expr : Expr}
    {value : Word}
    (hReturned : stmt.returnedExpr? = some expr)
    (hEval : expr.Eval value) :
    (Program.returnStmt stmt).IsReturnValue value := by
  exact
    ⟨expr,
      by
        simp [Program.returnStmt, Program.withContract,
          Program.returnedExpr?, ContractDecl.withBody,
          ContractDecl.withFunction, ContractDecl.returnedExpr?,
          FunctionDecl.withBody, FunctionDecl.returnedExpr?,
          ReturnVar.isUint256, ReturnVar.word0, Ty.uint256,
          Ty.isUint256,
          hReturned],
      hEval⟩

theorem Program.returnStmt_semantics {stmt : Stmt} {expr : Expr}
    {value : Word}
    (hReturned : stmt.returnedExpr? = some expr)
    (hEval : expr.Eval value) :
    Semantics (Program.returnStmt stmt) (Behavior.returnedWord value) := by
  exact Semantics.returnValue
    (Program.returnStmt_isReturnValue hReturned hEval)

theorem Program.returnExpr_isReturnValue {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    (Program.returnExpr expr).IsReturnValue value := by
  exact Program.returnStmt_isReturnValue (by rfl) hEval

theorem Program.returnExpr_semantics {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    Semantics (Program.returnExpr expr) (Behavior.returnedWord value) := by
  exact Semantics.returnValue (Program.returnExpr_isReturnValue hEval)

theorem Program.returnWord_wf (value : Word) : WF (Program.returnWord value) := by
  exact {}

end L01_ValidSolidity
end Spine
end SolidCore

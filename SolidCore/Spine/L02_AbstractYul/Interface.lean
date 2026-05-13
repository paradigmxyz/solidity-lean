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

def Ty.isWord : Ty -> Bool
  | Ty.word => true
  | _ => false

def Ty.isBool : Ty -> Bool
  | Ty.bool => true
  | _ => false

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

abbrev Behavior := L01_ValidSolidity.Behavior

def Program.empty : Program := {}

def EntryId.entry : EntryId := { value := 0 }

def Expr.word0 : Expr := Expr.word 0

def Expr.word1 : Expr := Expr.word 1

def Expr.word2 : Expr := Expr.word 2

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.addChecked lhs rhs

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.subChecked lhs rhs

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.mulChecked lhs rhs

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.bitAnd lhs rhs

def Expr.eqOp (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.eq lhs rhs

def Expr.ltOp (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.lt lhs rhs

def Expr.gtOp (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.gt lhs rhs

def Expr.resultTy? : Expr -> Option Ty
  | Expr.word _ => some Ty.word
  | Expr.bool _ => some Ty.bool
  | Expr.binary BinaryOp.addChecked lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.word
      | _, _ => none
  | Expr.binary BinaryOp.subChecked lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.word
      | _, _ => none
  | Expr.binary BinaryOp.mulChecked lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.word
      | _, _ => none
  | Expr.binary BinaryOp.bitAnd lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.word
      | _, _ => none
  | Expr.binary BinaryOp.eq lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.bool
      | some Ty.bool, some Ty.bool => some Ty.bool
      | _, _ => none
  | Expr.binary BinaryOp.lt lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.bool
      | _, _ => none
  | Expr.binary BinaryOp.gt lhs rhs =>
      match lhs.resultTy?, rhs.resultTy? with
      | some Ty.word, some Ty.word => some Ty.bool
      | _, _ => none
  | _ => none

def Expr.resultTyIsWord (expr : Expr) : Bool :=
  match expr.resultTy? with
  | some ty => ty.isWord
  | none => false

def Expr.resultTyIsBool (expr : Expr) : Bool :=
  match expr.resultTy? with
  | some ty => ty.isBool
  | none => false

def BinaryOp.toCore? :
    BinaryOp -> Option SolidCore.Solidity.Source.BinaryOp
  | BinaryOp.addChecked => some SolidCore.Solidity.Source.BinaryOp.add
  | BinaryOp.subChecked => some SolidCore.Solidity.Source.BinaryOp.sub
  | BinaryOp.mulChecked => some SolidCore.Solidity.Source.BinaryOp.mul
  | BinaryOp.bitAnd => some SolidCore.Solidity.Source.BinaryOp.bitAnd
  | BinaryOp.lt => some SolidCore.Solidity.Source.BinaryOp.lt
  | BinaryOp.gt => some SolidCore.Solidity.Source.BinaryOp.gt
  | BinaryOp.eq => some SolidCore.Solidity.Source.BinaryOp.eq
  | _ => none

def Expr.toCore? :
    Expr -> Option L00_SourceSolidity.Executable.CoreExpr
  | Expr.word value =>
      some (SolidCore.Solidity.Source.Expr.word value)
  | Expr.bool value =>
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Source.boolWord value))
  | Expr.binary op lhs rhs => do
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

@[simp] theorem Expr.resultTy?_word (value : Word) :
    (Expr.word value).resultTy? = some Ty.word := by
  rfl

@[simp] theorem Expr.resultTy?_bool (value : Bool) :
    (Expr.bool value).resultTy? = some Ty.bool := by
  rfl

@[simp] theorem Expr.resultTy?_add_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.add lhs rhs).resultTy? = some Ty.word := by
  simp [Expr.add, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_sub_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.sub lhs rhs).resultTy? = some Ty.word := by
  simp [Expr.sub, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_mul_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.mul lhs rhs).resultTy? = some Ty.word := by
  simp [Expr.mul, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_bitAnd_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.bitAnd lhs rhs).resultTy? = some Ty.word := by
  simp [Expr.bitAnd, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_eqOp_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.eqOp lhs rhs).resultTy? = some Ty.bool := by
  simp [Expr.eqOp, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_eqOp_bool
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.bool)
    (hRhs : rhs.resultTy? = some Ty.bool) :
    (Expr.eqOp lhs rhs).resultTy? = some Ty.bool := by
  simp [Expr.eqOp, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_ltOp_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.ltOp lhs rhs).resultTy? = some Ty.bool := by
  simp [Expr.ltOp, Expr.resultTy?, hLhs, hRhs]

@[simp] theorem Expr.resultTy?_gtOp_word
    {lhs rhs : Expr}
    (hLhs : lhs.resultTy? = some Ty.word)
    (hRhs : rhs.resultTy? = some Ty.word) :
    (Expr.gtOp lhs rhs).resultTy? = some Ty.bool := by
  simp [Expr.gtOp, Expr.resultTy?, hLhs, hRhs]

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
  Stmt.complete (Completion.returnValues [expr])

def Stmt.returnWord (value : Word) : Stmt :=
  Stmt.returnExpr (Expr.word value)

def Stmt.returnedExpr? : Stmt -> Option Expr
  | Stmt.complete (Completion.returnValues [expr]) => some expr
  | Stmt.block [stmt] => stmt.returnedExpr?
  | Stmt.ifElse condition thenBranch elseBranch =>
      match condition.eval? with
      | some value =>
          if SolidCore.Solidity.Source.wordTruthy value then
            thenBranch.returnedExpr?
          else
            elseBranch.returnedExpr?
      | none => none
  | _ => none

def Entry.withSourceBody
    (sourceFunction : L01_ValidSolidity.FunctionId) (body : Stmt) :
    Entry :=
  { id := EntryId.entry
    sourceFunction := sourceFunction
    body := body }

def Entry.withBody (body : Stmt) : Entry :=
  Entry.withSourceBody L01_ValidSolidity.FunctionId.entry body

def Entry.returnStmt (stmt : Stmt) : Entry :=
  Entry.withBody stmt

def Entry.returnExpr (expr : Expr) : Entry :=
  Entry.returnStmt (Stmt.returnExpr expr)

def Entry.returnWord (value : Word) : Entry :=
  Entry.returnExpr (Expr.word value)

def Entry.returnedExpr? (entry : Entry) : Option Expr :=
  match entry.params, entry.body with
  | [], body => body.returnedExpr?
  | _, _ => none

def Program.withEntry (entry : Entry) : Program :=
  { entries := [entry]
    procs := []
    init := none }

def Program.returnStmt (stmt : Stmt) : Program :=
  Program.withEntry (Entry.returnStmt stmt)

def Program.returnExpr (expr : Expr) : Program :=
  Program.returnStmt (Stmt.returnExpr expr)

def Program.returnWord (value : Word) : Program :=
  Program.returnExpr (Expr.word value)

def Program.returnedExpr? (program : Program) : Option Expr :=
  match program.entries, program.procs, program.init with
  | [entry], [], none => entry.returnedExpr?
  | _, _, _ => none

def Program.IsEmpty (program : Program) : Prop :=
  program.entries = [] ∧ program.procs = [] ∧ program.init = none

def Program.IsReturnValue (program : Program) (value : Word) : Prop :=
  ∃ expr, program.returnedExpr? = some expr ∧ expr.Eval value

inductive Semantics : Program -> Behavior -> Prop where
  | empty {program : Program} :
      program.IsEmpty ->
      Semantics program L01_ValidSolidity.Behavior.stopped
  | returnValue {program : Program} {value : Word} :
      program.IsReturnValue value ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord value)

theorem Program.empty_isEmpty : Program.empty.IsEmpty := by
  simp [Program.empty, Program.IsEmpty]

theorem Program.empty_wf : WF Program.empty := by
  exact {}

theorem Program.empty_semantics :
    Semantics Program.empty L01_ValidSolidity.Behavior.stopped := by
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
          simp [Program.returnStmt, Program.withEntry,
            Program.returnedExpr?, Entry.returnStmt, Entry.withBody,
            Entry.withSourceBody,
            Entry.returnedExpr?, hReturned],
      hEval⟩

theorem Program.returnStmt_semantics {stmt : Stmt} {expr : Expr}
    {value : Word}
    (hReturned : stmt.returnedExpr? = some expr)
    (hEval : expr.Eval value) :
    Semantics (Program.returnStmt stmt)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnValue
    (Program.returnStmt_isReturnValue hReturned hEval)

theorem Program.returnExpr_isReturnValue {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    (Program.returnExpr expr).IsReturnValue value := by
  exact Program.returnStmt_isReturnValue (by rfl) hEval

theorem Program.returnExpr_semantics {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    Semantics (Program.returnExpr expr)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnValue (Program.returnExpr_isReturnValue hEval)

theorem Program.returnWord_wf (value : Word) : WF (Program.returnWord value) := by
  exact {}

end L02_AbstractYul
end Spine
end SolidCore

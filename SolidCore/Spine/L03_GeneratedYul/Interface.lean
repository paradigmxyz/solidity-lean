import SharedSemantics.Word
import SolidCore.Spine.L02_AbstractYul.Interface
import SolidCoreYulCore.Evm

namespace SolidCore
namespace Spine
namespace L03_GeneratedYul

abbrev Word := SharedSemantics.Word
abbrev Byte := Nat
abbrev Name := Nat
abbrev DataLabel := Nat
abbrev Builtin := SolidCoreYulCore.Evm.Builtin
abbrev Env := List (Name × Word)
abbrev Memory := List (Word × Word)

inductive MemoryRegion where
  | scratch
  | freePointer
  | calldata
  | returndata
  | abiInput
  | abiOutput
  | revertOutput
  deriving Repr

structure StorageSlot where
  base : Word
  keys : List Word := []
  deriving Repr

structure LayoutItem where
  sourceStorage : L01_ValidSolidity.StorageId
  slot : StorageSlot
  deriving Repr

structure AbiItem where
  sourceFunction : L01_ValidSolidity.FunctionId
  selector : Word
  calldataTypes : List L02_AbstractYul.Ty := []
  returndataTypes : List L02_AbstractYul.Ty := []
  deriving Repr

structure EventItem where
  sourceEvent : L01_ValidSolidity.EventId
  topic0 : Option Word := none
  indexedCount : Nat := 0
  deriving Repr

structure ErrorItem where
  sourceError : L01_ValidSolidity.ErrorId
  selector : Word
  deriving Repr

inductive Expr where
  | word : Word -> Expr
  | var : Name -> Expr
  | builtin : Builtin -> List Expr -> Expr
  | call : Name -> List Expr -> Expr
  | dataSize : DataLabel -> Expr
  | dataOffset : DataLabel -> Expr
  deriving Repr

inductive Stmt where
  | skip
  | expr : Expr -> Stmt
  | let1 : Name -> Option Expr -> Stmt
  | letMany : List Name -> Option (List Expr) -> Stmt
  | assign : Name -> Expr -> Stmt
  | assignMany : List Name -> List Expr -> Stmt
  | function : Name -> List Name -> List Name -> Stmt -> Stmt
  | block : List Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break
  | continue
  | leave
  deriving Repr

structure FunctionDef where
  name : Name
  params : List Name := []
  returns : List Name := []
  body : Stmt
  deriving Repr

structure DataSegment where
  label : DataLabel
  bytes : List Byte := []
  deriving Repr

structure Object where
  code : Stmt
  functions : List FunctionDef := []
  data : List DataSegment := []
  subobjects : List (DataLabel × Object) := []
  deriving Repr

structure Profile where
  layout : List LayoutItem := []
  abi : List AbiItem := []
  events : List EventItem := []
  errors : List ErrorItem := []
  memoryRegions : List MemoryRegion := []
  emittedHelpers : List Name := []
  deriving Repr

structure Program where
  object : Object
  profile : Profile := {}
  deriving Repr

def Object.CodeOnly (object : Object) : Prop :=
  object.functions = [] ∧
    object.data = [] ∧
    object.subobjects = []

def Profile.IsEmpty (profile : Profile) : Prop :=
  profile.layout = [] ∧
    profile.abi = [] ∧
    profile.events = [] ∧
    profile.errors = [] ∧
    profile.memoryRegions = [] ∧
    profile.emittedHelpers = []

structure WF (program : Program) : Prop where
  objectCodeOnly : program.object.CodeOnly
  profileEmpty : program.profile.IsEmpty

abbrev Behavior := L02_AbstractYul.Behavior

def Object.stop : Object :=
  { code := Stmt.skip }

def Profile.empty : Profile := {}

def Program.stop : Program :=
  { object := Object.stop
    profile := Profile.empty }

def Expr.word0 : Expr := Expr.word 0

def Expr.word1 : Expr := Expr.word 1

def Expr.word2 : Expr := Expr.word 2

def Expr.word3 : Expr := Expr.word 3

def Expr.word32 : Expr := Expr.word 32

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.add [lhs, rhs]

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs]

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs]

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.andOp [lhs, rhs]

def Expr.iszero (value : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.iszero [value]

def Expr.eqOp (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs]

def Expr.ltOp (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.ltOp [lhs, rhs]

def Expr.gtOp (lhs rhs : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.gtOp [lhs, rhs]

def Expr.mload (offset : Expr) : Expr :=
  Expr.builtin SolidCoreYulCore.Evm.Builtin.mload [offset]

def Expr.add1And2 : Expr :=
  Expr.add Expr.word1 Expr.word2

def Expr.mul2And3 : Expr :=
  Expr.mul Expr.word2 Expr.word3

def Expr.sub3And1 : Expr :=
  Expr.sub Expr.word3 Expr.word1

def Expr.bitAnd3And1 : Expr :=
  Expr.bitAnd Expr.word3 Expr.word1

def Expr.iszero0 : Expr :=
  Expr.iszero Expr.word0

def Expr.eq2And2 : Expr :=
  Expr.eqOp Expr.word2 Expr.word2

def Expr.lt1And2 : Expr :=
  Expr.ltOp Expr.word1 Expr.word2

def Expr.gt2And1 : Expr :=
  Expr.gtOp Expr.word2 Expr.word1

def Env.lookup? : Env -> Name -> Option Word
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate == name then some value else Env.lookup? rest name

def Env.contains (env : Env) (name : Name) : Bool :=
  (Env.lookup? env name).isSome

def Env.declare? (env : Env) (name : Name) (value : Word) : Option Env :=
  if Env.contains env name then none else some ((name, value) :: env)

def Env.assign? : Env -> Name -> Word -> Option Env
  | [], _, _ => none
  | (candidate, current) :: rest, name, value =>
      if candidate == name then
        some ((candidate, value) :: rest)
      else
        match Env.assign? rest name value with
        | some rest' => some ((candidate, current) :: rest')
        | none => none

def Memory.lookup? : Memory -> Word -> Option Word
  | [], _ => none
  | (candidate, value) :: rest, offset =>
      if SharedSemantics.norm candidate == SharedSemantics.norm offset then
        some value
      else
        Memory.lookup? rest offset

def Memory.store (memory : Memory) (offset value : Word) : Memory :=
  (SharedSemantics.norm offset, SharedSemantics.norm value) :: memory

structure State where
  env : Env := []
  memory : Memory := []
  deriving Repr

def State.empty : State := {}

def Expr.evalWith? (env : Env) : Expr -> Option Word
  | Expr.word value =>
      some (SharedSemantics.norm value)
  | Expr.var name =>
      Env.lookup? env name
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.add [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.addWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.mulWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.subWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.andOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.andWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.iszero [value] => do
      let word ← value.evalWith? env
      some (SharedSemantics.iszeroWord word)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.eqWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.ltOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.ltWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.gtOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWith? env
      let rhsValue ← rhs.evalWith? env
      some (SharedSemantics.gtWord lhsValue rhsValue)
  | _ => none

def Expr.eval? (expr : Expr) : Option Word :=
  expr.evalWith? []

def Expr.Eval (expr : Expr) (value : Word) : Prop :=
  expr.eval? = some value

theorem Expr.eval?_word (value : Word) :
    (Expr.word value).eval? = some (SharedSemantics.norm value) := by
  rfl

theorem Expr.word_eval_norm (value : Word) :
    (Expr.word value).Eval (SharedSemantics.norm value) := by
  simpa [Expr.Eval] using Expr.eval?_word value

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

@[simp] theorem Expr.eval?_word3 : Expr.word3.eval? = some 3 := by
  rfl

@[simp] theorem Expr.eval?_word_three : (Expr.word 3).eval? = some 3 := by
  rfl

@[simp] theorem Expr.eval?_add1And2 :
    Expr.add1And2.eval? = some 3 := by
  rfl

@[simp] theorem Expr.eval?_add_word1_word2 :
    (Expr.add (Expr.word 1) (Expr.word 2)).eval? = some 3 := by
  rfl

@[simp] theorem Expr.eval?_mul2And3 :
    Expr.mul2And3.eval? = some 6 := by
  rfl

@[simp] theorem Expr.eval?_sub3And1 :
    Expr.sub3And1.eval? = some 2 := by
  rfl

@[simp] theorem Expr.eval?_bitAnd3And1 :
    Expr.bitAnd3And1.eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_iszero0 :
    Expr.iszero0.eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_eq2And2 :
    Expr.eq2And2.eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_lt1And2 :
    Expr.lt1And2.eval? = some 1 := by
  rfl

@[simp] theorem Expr.eval?_gt2And1 :
    Expr.gt2And1.eval? = some 1 := by
  rfl

mutual

def Stmt.neutral? : Stmt -> Bool
  | Stmt.skip => true
  | Stmt.expr sourceExpr => sourceExpr.eval?.isSome
  | Stmt.block stmts => Stmt.neutralStmts? stmts
  | _ => false

def Stmt.neutralStmts? : List Stmt -> Bool
  | [] => true
  | stmt :: rest => stmt.neutral? && Stmt.neutralStmts? rest

end

@[simp] theorem Stmt.neutral?_mstore_word
    (offset : Word) (storedExpr : Expr) :
    (Stmt.expr
      (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
        [Expr.word offset, storedExpr])).neutral? = false := by
  rfl

def Stmt.returnExpr (expr : Expr) : Stmt :=
  Stmt.block
    [ Stmt.expr
        (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
          [Expr.word0, expr])
    , Stmt.expr
        (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp
          [Expr.word0, Expr.word32]) ]

def Stmt.returnWord (value : Word) : Stmt :=
  Stmt.returnExpr (Expr.word value)

def Stmt.returnWord0 : Stmt :=
  Stmt.returnWord 0

def Stmt.returnWord3 : Stmt :=
  Stmt.returnWord 3

def Stmt.returnAdd1And2 : Stmt :=
  Stmt.returnExpr Expr.add1And2

def Stmt.mstore (offset value : Expr) : Stmt :=
  Stmt.expr
    (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore [offset, value])

def Stmt.returnMemory (offset size : Expr) : Stmt :=
  Stmt.expr
    (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp [offset, size])

mutual

def Stmt.returnedExpr? : Stmt -> Option Expr
  | Stmt.block stmts => Stmt.returnedExprs? stmts
  | Stmt.switch condition [(0, zeroBranch)] (some defaultBranch) =>
      match condition.eval? with
      | some value =>
          if SharedSemantics.norm value == 0 then
            zeroBranch.returnedExpr?
          else
            defaultBranch.returnedExpr?
      | none => none
  | _ => none

def Stmt.returnedExprs? : List Stmt -> Option Expr
  | [stmt] => stmt.returnedExpr?
  | stmt :: next :: rest =>
      if stmt.neutral? then
        Stmt.returnedExprs? (next :: rest)
      else
        match stmt, next, rest with
        | Stmt.expr
            (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
              [Expr.word offset, storedExpr]),
          Stmt.expr
            (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp
              [Expr.word returnOffset, Expr.word returnSize]),
          [] =>
            if offset == 0 && returnOffset == 0 && returnSize == 32 then
              some storedExpr
            else
              none
        | _, _, _ => none
  | _ => none

end

@[simp] theorem Stmt.returnedExpr?_skip :
    Stmt.returnedExpr? Stmt.skip = none := by
  rfl

def Expr.evalListWith? (env : Env) : List Expr -> Option (List Word)
  | [] => some []
  | expr :: rest => do
      let value ← expr.evalWith? env
      let values ← Expr.evalListWith? env rest
      some (value :: values)

def Env.declareMany? : Env -> List Name -> List Word -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values => do
      let env' ← Env.declare? env name value
      Env.declareMany? env' names values
  | _, _, _ => none

def Env.declareZeros? (env : Env) (names : List Name) : Option Env :=
  Env.declareMany? env names (List.replicate names.length 0)

def Env.assignMany? : Env -> List Name -> List Word -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values => do
      let env' ← Env.assign? env name value
      Env.assignMany? env' names values
  | _, _, _ => none

def Stmt.stepLocal? (env : Env) : Stmt -> Option Env
  | Stmt.skip => some env
  | Stmt.expr sourceExpr =>
      match sourceExpr.evalWith? env with
      | some _ => some env
      | none => none
  | Stmt.let1 name none =>
      Env.declare? env name 0
  | Stmt.let1 name (some sourceExpr) => do
      let value ← sourceExpr.evalWith? env
      Env.declare? env name value
  | Stmt.letMany names none =>
      Env.declareZeros? env names
  | Stmt.letMany names (some exprs) => do
      let values ← Expr.evalListWith? env exprs
      Env.declareMany? env names values
  | Stmt.assign name sourceExpr => do
      let value ← sourceExpr.evalWith? env
      Env.assign? env name value
  | Stmt.assignMany names exprs => do
      let values ← Expr.evalListWith? env exprs
      Env.assignMany? env names values
  | _ => none

mutual

def Stmt.returnedExprWithLocals? (env : Env) : Stmt -> Option Expr
  | Stmt.block stmts => Stmt.returnedExprsWithLocals? env stmts
  | Stmt.switch condition [(0, zeroBranch)] (some defaultBranch) =>
      match condition.evalWith? env with
      | some value =>
          if SharedSemantics.norm value == 0 then
            zeroBranch.returnedExprWithLocals? env
          else
            defaultBranch.returnedExprWithLocals? env
      | none => none
  | _ => none

def Stmt.returnedExprsWithLocals? (env : Env) : List Stmt -> Option Expr
  | [stmt] => stmt.returnedExprWithLocals? env
  | stmt :: next :: rest =>
      match Stmt.stepLocal? env stmt with
      | some env' =>
          Stmt.returnedExprsWithLocals? env' (next :: rest)
      | none =>
          match stmt, next, rest with
          | Stmt.expr
              (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
                [Expr.word offset, storedExpr]),
            Stmt.expr
              (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp
                [Expr.word returnOffset, Expr.word returnSize]),
            [] =>
              if offset == 0 && returnOffset == 0 && returnSize == 32 then
                match storedExpr.evalWith? env with
                | some value => some (Expr.word value)
                | none => none
              else
                none
          | _, _, _ => none
  | _ => none

end

@[simp] theorem Stmt.returnedExprWithLocals?_skip (env : Env) :
    Stmt.returnedExprWithLocals? env Stmt.skip = none := by
  rfl

def Expr.evalWithState? (state : State) : Expr -> Option Word
  | Expr.word value =>
      some (SharedSemantics.norm value)
  | Expr.var name =>
      Env.lookup? state.env name
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.add [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.addWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.mulWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.subWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.andOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.andWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.iszero [value] => do
      let word ← value.evalWithState? state
      some (SharedSemantics.iszeroWord word)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.eqWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.ltOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.ltWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.gtOp [lhs, rhs] => do
      let lhsValue ← lhs.evalWithState? state
      let rhsValue ← rhs.evalWithState? state
      some (SharedSemantics.gtWord lhsValue rhsValue)
  | Expr.builtin SolidCoreYulCore.Evm.Builtin.mload [offsetExpr] => do
      let offset ← offsetExpr.evalWithState? state
      Memory.lookup? state.memory offset
  | _ => none

def Expr.evalListWithState? (state : State) :
    List Expr -> Option (List Word)
  | [] => some []
  | expr :: rest => do
      let value ← expr.evalWithState? state
      let values ← Expr.evalListWithState? state rest
      some (value :: values)

def Stmt.stepState? (state : State) : Stmt -> Option State
  | Stmt.skip => some state
  | Stmt.expr
      (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
        [offsetExpr, storedExpr]) => do
      let offset ← offsetExpr.evalWithState? state
      let value ← storedExpr.evalWithState? state
      some { state with memory := Memory.store state.memory offset value }
  | Stmt.expr sourceExpr =>
      match sourceExpr.evalWithState? state with
      | some _ => some state
      | none => none
  | Stmt.let1 name none =>
      match Env.declare? state.env name 0 with
      | some env' => some { state with env := env' }
      | none => none
  | Stmt.let1 name (some sourceExpr) => do
      let value ← sourceExpr.evalWithState? state
      let env' ← Env.declare? state.env name value
      some { state with env := env' }
  | Stmt.letMany names none =>
      match Env.declareZeros? state.env names with
      | some env' => some { state with env := env' }
      | none => none
  | Stmt.letMany names (some exprs) => do
      let values ← Expr.evalListWithState? state exprs
      let env' ← Env.declareMany? state.env names values
      some { state with env := env' }
  | Stmt.assign name sourceExpr => do
      let value ← sourceExpr.evalWithState? state
      let env' ← Env.assign? state.env name value
      some { state with env := env' }
  | Stmt.assignMany names exprs => do
      let values ← Expr.evalListWithState? state exprs
      let env' ← Env.assignMany? state.env names values
      some { state with env := env' }
  | _ => none

mutual

def Stmt.returnedExprWithState? (state : State) : Stmt -> Option Expr
  | Stmt.block stmts => Stmt.returnedExprsWithState? state stmts
  | Stmt.ifThen condition thenBranch =>
      match condition.evalWithState? state with
      | some value =>
          if SharedSemantics.norm value == 0 then
            none
          else
            thenBranch.returnedExprWithState? state
      | none => none
  | Stmt.switch condition [(0, zeroBranch)] (some defaultBranch) =>
      match condition.evalWithState? state with
      | some value =>
          if SharedSemantics.norm value == 0 then
            zeroBranch.returnedExprWithState? state
          else
            defaultBranch.returnedExprWithState? state
      | none => none
  | _ => none

def Stmt.returnedExprsWithState? (state : State) : List Stmt -> Option Expr
  | [] => none
  | [stmt] =>
      match stmt with
      | Stmt.expr
          (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp
            [offsetExpr, sizeExpr]) => do
          let offset ← offsetExpr.evalWithState? state
          let size ← sizeExpr.evalWithState? state
          if SharedSemantics.norm size == 32 then
            match Memory.lookup? state.memory offset with
            | some value => some (Expr.word value)
            | none => none
          else
            none
      | _ => stmt.returnedExprWithState? state
  | Stmt.ifThen condition thenBranch :: rest =>
      match condition.evalWithState? state with
      | some value =>
          if SharedSemantics.norm value == 0 then
            Stmt.returnedExprsWithState? state rest
          else
            thenBranch.returnedExprWithState? state
      | none => none
  | Stmt.forLoop init condition _post body :: rest =>
      match Stmt.stepState? state init with
      | some state' =>
          match condition.evalWithState? state' with
          | some value =>
              if SharedSemantics.norm value == 0 then
                Stmt.returnedExprsWithState? state' rest
              else
                body.returnedExprWithState? state'
          | none => none
      | none => none
  | stmt :: next :: rest =>
      match Stmt.stepState? state stmt with
      | some state' => Stmt.returnedExprsWithState? state' (next :: rest)
      | none => none

end

@[simp] theorem Stmt.returnedExprWithState?_skip (state : State) :
    Stmt.returnedExprWithState? state Stmt.skip = none := by
  rfl

def Object.returnWord (value : Word) : Object :=
  { code := Stmt.returnWord value }

def Object.returnStmt (stmt : Stmt) : Object :=
  { code := stmt }

def Object.returnExpr (expr : Expr) : Object :=
  Object.returnStmt (Stmt.returnExpr expr)

def Object.returnWord0 : Object :=
  Object.returnWord 0

def Object.returnWord3 : Object :=
  Object.returnWord 3

def Object.returnAdd1And2 : Object :=
  Object.returnExpr Expr.add1And2

def Program.returnWord (value : Word) : Program :=
  { object := Object.returnWord value
    profile := Profile.empty }

def Program.returnStmt (stmt : Stmt) : Program :=
  { object := Object.returnStmt stmt
    profile := Profile.empty }

def Program.returnExpr (expr : Expr) : Program :=
  Program.returnStmt (Stmt.returnExpr expr)

def Program.returnWord0 : Program :=
  Program.returnWord 0

def Program.returnWord3 : Program :=
  Program.returnWord 3

def Program.returnAdd1And2 : Program :=
  Program.returnExpr Expr.add1And2

def Object.IsStop (object : Object) : Prop :=
  object.code = Stmt.skip ∧
    object.functions = [] ∧
    object.data = [] ∧
    object.subobjects = []

def Program.IsStop (program : Program) : Prop :=
  program.object.IsStop ∧ program.profile.IsEmpty

def Object.returnedExpr? (object : Object) : Option Expr :=
  match object.functions, object.data, object.subobjects with
  | [], [], [] =>
      match object.code.returnedExpr? with
      | some expr => some expr
      | none =>
          match object.code.returnedExprWithLocals? [] with
          | some expr => some expr
          | none => object.code.returnedExprWithState? State.empty
  | _, _, _ => none

def Program.returnedExpr? (program : Program) : Option Expr :=
  match program.profile.layout, program.profile.abi, program.profile.events,
      program.profile.errors, program.profile.memoryRegions,
      program.profile.emittedHelpers with
  | [], [], [], [], [], [] => program.object.returnedExpr?
  | _, _, _, _, _, _ => none

def Program.IsReturnValue (program : Program) (value : Word) : Prop :=
  ∃ expr, program.returnedExpr? = some expr ∧ expr.Eval value

def Object.IsReturnWord (object : Object) (value : Word) : Prop :=
  object.code = Stmt.returnWord value ∧
    object.functions = [] ∧
    object.data = [] ∧
    object.subobjects = []

def Object.IsReturnWord0 (object : Object) : Prop :=
  object.IsReturnWord 0

def Object.IsReturnWord3 (object : Object) : Prop :=
  object.IsReturnWord 3

def Program.IsReturnWord (program : Program) (value : Word) : Prop :=
  program.object.IsReturnWord value ∧ program.profile.IsEmpty

def Program.IsReturnWord0 (program : Program) : Prop :=
  program.IsReturnWord 0

def Program.IsReturnWord3 (program : Program) : Prop :=
  program.IsReturnWord 3

inductive Semantics : Program -> Behavior -> Prop where
  | stop {program : Program} :
      program.IsStop ->
      Semantics program L01_ValidSolidity.Behavior.stopped
  | returnWord0 {program : Program} :
      program.IsReturnWord0 ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord 0)
  | returnWord3 {program : Program} :
      program.IsReturnWord3 ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord 3)
  | returnValue {program : Program} {value : Word} :
      program.IsReturnValue value ->
      Semantics program (L01_ValidSolidity.Behavior.returnedWord value)

theorem Object.stop_isStop : Object.stop.IsStop := by
  simp [Object.stop, Object.IsStop]

theorem Profile.empty_isEmpty : Profile.empty.IsEmpty := by
  simp [Profile.empty, Profile.IsEmpty]

theorem Program.stop_isStop : Program.stop.IsStop := by
  exact ⟨Object.stop_isStop, Profile.empty_isEmpty⟩

theorem Program.stop_wf : WF Program.stop := by
  exact
    { objectCodeOnly := by
        simp [Program.stop, Object.stop, Object.CodeOnly]
      profileEmpty := by
        simp [Program.stop, Profile.empty, Profile.IsEmpty] }

theorem Program.wf_of_isStop {program : Program}
    (hStop : program.IsStop) :
    WF program := by
  rcases hStop with ⟨hObject, hProfile⟩
  rcases hObject with ⟨_hCode, hFunctions, hData, hSubobjects⟩
  exact
    { objectCodeOnly := ⟨hFunctions, hData, hSubobjects⟩
      profileEmpty := hProfile }

theorem Program.stop_semantics :
    Semantics Program.stop L01_ValidSolidity.Behavior.stopped := by
  exact Semantics.stop Program.stop_isStop

theorem Program.stop_not_isReturnValue {value : Word} :
    ¬ Program.stop.IsReturnValue value := by
  intro hReturn
  rcases hReturn with ⟨expr, hReturned, _hEval⟩
  simp [Program.stop, Program.returnedExpr?, Object.stop,
    Object.returnedExpr?, State.empty, Profile.empty] at hReturned

theorem Program.ne_stop_of_returnedExpr
    {program : Program} {expr : Expr}
    (hReturned : program.returnedExpr? = some expr) :
    program ≠ Program.stop := by
  intro hProgram
  subst program
  simp [Program.stop, Program.returnedExpr?, Object.stop,
    Object.returnedExpr?, State.empty, Profile.empty] at hReturned

theorem Program.eq_stop_of_isStop {program : Program}
    (hStop : program.IsStop) :
    program = Program.stop := by
  rcases hStop with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              rfl

theorem Program.returnStmt_wf (stmt : Stmt) : WF (Program.returnStmt stmt) := by
  exact
    { objectCodeOnly := by
        simp [Program.returnStmt, Object.returnStmt, Object.CodeOnly]
      profileEmpty := by
        simp [Program.returnStmt, Profile.empty, Profile.IsEmpty] }

theorem Program.wf_of_returnedExpr
    {program : Program} {expr : Expr}
    (hReturned : program.returnedExpr? = some expr) :
    WF program := by
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases layout with
              | cons _ _ =>
                  simp [Program.returnedExpr?] at hReturned
              | nil =>
                  cases abi with
                  | cons _ _ =>
                      simp [Program.returnedExpr?] at hReturned
                  | nil =>
                      cases events with
                      | cons _ _ =>
                          simp [Program.returnedExpr?] at hReturned
                      | nil =>
                          cases errors with
                          | cons _ _ =>
                              simp [Program.returnedExpr?] at hReturned
                          | nil =>
                              cases memoryRegions with
                              | cons _ _ =>
                                  simp [Program.returnedExpr?] at hReturned
                              | nil =>
                                  cases emittedHelpers with
                                  | cons _ _ =>
                                      simp [Program.returnedExpr?] at hReturned
                                  | nil =>
                                      cases functions with
                                      | cons _ _ =>
                                          simp [Program.returnedExpr?,
                                            Object.returnedExpr?] at hReturned
                                      | nil =>
                                          cases data with
                                          | cons _ _ =>
                                              simp [Program.returnedExpr?,
                                                Object.returnedExpr?]
                                                at hReturned
                                          | nil =>
                                              cases subobjects with
                                              | cons _ _ =>
                                                  simp [Program.returnedExpr?,
                                                    Object.returnedExpr?]
                                                    at hReturned
                                              | nil =>
                                                  exact
                                                    { objectCodeOnly := by
                                                        simp [Object.CodeOnly]
                                                      profileEmpty := by
                                                        simp [Profile.IsEmpty] }

theorem Program.returnStmt_isReturnValue {stmt : Stmt} {expr : Expr}
    {value : Word}
    (hReturned : stmt.returnedExpr? = some expr)
    (hEval : expr.Eval value) :
    (Program.returnStmt stmt).IsReturnValue value := by
  exact
    ⟨expr,
      by
        simp [Program.returnStmt, Program.returnedExpr?,
          Object.returnStmt, Object.returnedExpr?, Profile.empty,
          hReturned],
      hEval⟩

theorem Program.returnStmt_semantics {stmt : Stmt} {expr : Expr}
    {value : Word}
    (hReturned : stmt.returnedExpr? = some expr)
    (hEval : expr.Eval value) :
    Semantics (Program.returnStmt stmt)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnValue
    (Program.returnStmt_isReturnValue hReturned hEval)

theorem Program.returnExpr_wf (expr : Expr) : WF (Program.returnExpr expr) := by
  exact Program.returnStmt_wf (Stmt.returnExpr expr)

theorem Program.returnExpr_isReturnValue {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    (Program.returnExpr expr).IsReturnValue value := by
  exact Program.returnStmt_isReturnValue (by rfl) hEval

theorem Program.returnExpr_semantics {expr : Expr} {value : Word}
    (hEval : expr.Eval value) :
    Semantics (Program.returnExpr expr)
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  exact Semantics.returnValue (Program.returnExpr_isReturnValue hEval)

def Stmt.let1ReturnVar (name : Name) (value : Word) : Stmt :=
  Stmt.block
    [ Stmt.let1 name (some (Expr.word value))
    , Stmt.expr
        (Expr.builtin SolidCoreYulCore.Evm.Builtin.mstore
          [Expr.word 0, Expr.var name])
    , Stmt.expr
        (Expr.builtin SolidCoreYulCore.Evm.Builtin.returnOp
          [Expr.word 0, Expr.word 32]) ]

def Program.let1ReturnVar (name : Name) (value : Word) : Program :=
  Program.returnStmt (Stmt.let1ReturnVar name value)

theorem Program.let1ReturnVar_returnedExpr?
    (name : Name) (value : Word) :
    (Program.let1ReturnVar name value).returnedExpr? =
      some (Expr.word (SharedSemantics.norm value)) := by
  simp [Program.let1ReturnVar, Stmt.let1ReturnVar,
    Program.returnStmt, Program.returnedExpr?,
    Object.returnStmt, Object.returnedExpr?, Profile.empty,
    Stmt.returnedExpr?, Stmt.returnedExprs?,
    Stmt.returnedExprWithLocals?, Stmt.returnedExprsWithLocals?,
    Stmt.stepLocal?, Stmt.neutral?,
    Expr.evalWith?, Env.declare?, Env.contains, Env.lookup?]

theorem Program.let1ReturnVar_wf
    (name : Name) (value : Word) :
    WF (Program.let1ReturnVar name value) := by
  exact Program.returnStmt_wf (Stmt.let1ReturnVar name value)

theorem Program.let1ReturnVar_semantics
    (name : Name) (value : Word) :
    Semantics (Program.let1ReturnVar name value)
      (L01_ValidSolidity.Behavior.returnedWord
        (SharedSemantics.norm value)) := by
  have hEval :
      (Expr.word (SharedSemantics.norm value)).Eval
        (SharedSemantics.norm value) := by
    simpa [Expr.Eval, SharedSemantics.norm_norm] using
      Expr.word_eval_norm (SharedSemantics.norm value)
  exact Semantics.returnValue
    ⟨Expr.word (SharedSemantics.norm value),
      Program.let1ReturnVar_returnedExpr? name value, hEval⟩

def Stmt.memoryRoundTripReturn (value : Word) : Stmt :=
  Stmt.block
    [ Stmt.mstore Expr.word0 (Expr.word value)
    , Stmt.mstore Expr.word32 (Expr.mload Expr.word0)
    , Stmt.returnMemory Expr.word32 Expr.word32 ]

def Program.memoryRoundTripReturn (value : Word) : Program :=
  Program.returnStmt (Stmt.memoryRoundTripReturn value)

theorem Program.memoryRoundTripReturn_returnedExpr?
    (value : Word) :
    (Program.memoryRoundTripReturn value).returnedExpr? =
      some (Expr.word (SharedSemantics.norm value)) := by
  simp [Program.memoryRoundTripReturn, Stmt.memoryRoundTripReturn,
    Program.returnStmt, Program.returnedExpr?,
    Object.returnStmt, Object.returnedExpr?, Profile.empty,
    Stmt.returnedExpr?, Stmt.returnedExprs?,
    Stmt.returnedExprWithLocals?, Stmt.returnedExprsWithLocals?,
    Stmt.returnedExprWithState?, Stmt.returnedExprsWithState?,
    Stmt.stepLocal?, Stmt.stepState?, Stmt.mstore, Stmt.returnMemory,
    Stmt.neutral?, Expr.evalWith?, Expr.evalWithState?, Expr.mload,
    Memory.store, Memory.lookup?, State.empty, Expr.word0, Expr.word32,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem Program.memoryRoundTripReturn_wf
    (value : Word) :
    WF (Program.memoryRoundTripReturn value) := by
  exact Program.returnStmt_wf (Stmt.memoryRoundTripReturn value)

theorem Program.memoryRoundTripReturn_semantics
    (value : Word) :
    Semantics (Program.memoryRoundTripReturn value)
      (L01_ValidSolidity.Behavior.returnedWord
        (SharedSemantics.norm value)) := by
  have hEval :
      (Expr.word (SharedSemantics.norm value)).Eval
        (SharedSemantics.norm value) := by
    simpa [Expr.Eval, SharedSemantics.norm_norm] using
      Expr.word_eval_norm (SharedSemantics.norm value)
  exact Semantics.returnValue
    ⟨Expr.word (SharedSemantics.norm value),
      Program.memoryRoundTripReturn_returnedExpr? value, hEval⟩

def Stmt.ifZeroFallthroughReturn (value : Word) : Stmt :=
  Stmt.block
    [ Stmt.ifThen Expr.word0 (Stmt.returnWord 1)
    , Stmt.returnWord value ]

def Program.ifZeroFallthroughReturn (value : Word) : Program :=
  Program.returnStmt (Stmt.ifZeroFallthroughReturn value)

theorem Program.ifZeroFallthroughReturn_returnedExpr?
    (value : Word) :
    (Program.ifZeroFallthroughReturn value).returnedExpr? =
      some (Expr.word (SharedSemantics.norm value)) := by
  simp [Program.ifZeroFallthroughReturn, Stmt.ifZeroFallthroughReturn,
    Program.returnStmt, Program.returnedExpr?,
    Object.returnStmt, Object.returnedExpr?, Profile.empty,
    Stmt.returnWord, Stmt.returnExpr,
    Stmt.returnedExpr?, Stmt.returnedExprs?,
    Stmt.returnedExprWithLocals?, Stmt.returnedExprsWithLocals?,
    Stmt.returnedExprWithState?, Stmt.returnedExprsWithState?,
    Stmt.stepLocal?, Stmt.stepState?, Stmt.neutral?,
    Expr.evalWithState?, Memory.store, Memory.lookup?, State.empty,
    Expr.word0, Expr.word32, SharedSemantics.norm,
    SharedSemantics.wordModulus]

theorem Program.ifZeroFallthroughReturn_wf
    (value : Word) :
    WF (Program.ifZeroFallthroughReturn value) := by
  exact Program.returnStmt_wf (Stmt.ifZeroFallthroughReturn value)

theorem Program.ifZeroFallthroughReturn_semantics
    (value : Word) :
    Semantics (Program.ifZeroFallthroughReturn value)
      (L01_ValidSolidity.Behavior.returnedWord
        (SharedSemantics.norm value)) := by
  have hEval :
      (Expr.word (SharedSemantics.norm value)).Eval
        (SharedSemantics.norm value) := by
    simpa [Expr.Eval, SharedSemantics.norm_norm] using
      Expr.word_eval_norm (SharedSemantics.norm value)
  exact Semantics.returnValue
    ⟨Expr.word (SharedSemantics.norm value),
      Program.ifZeroFallthroughReturn_returnedExpr? value, hEval⟩

def Stmt.switchZeroReturn (value fallback : Word) : Stmt :=
  Stmt.switch Expr.word0
    [(0, Stmt.returnWord value)]
    (some (Stmt.returnWord fallback))

def Program.switchZeroReturn (value fallback : Word) : Program :=
  Program.returnStmt (Stmt.switchZeroReturn value fallback)

theorem Program.switchZeroReturn_returnedExpr?
    (value fallback : Word) :
    (Program.switchZeroReturn value fallback).returnedExpr? =
      some (Expr.word value) := by
  simp [Program.switchZeroReturn, Stmt.switchZeroReturn,
    Program.returnStmt, Program.returnedExpr?,
    Object.returnStmt, Object.returnedExpr?, Profile.empty,
    Stmt.returnWord, Stmt.returnExpr,
    Stmt.returnedExpr?, Stmt.returnedExprs?,
    Expr.eval?, Expr.evalWith?, Expr.word0, Expr.word32,
    SharedSemantics.norm, SharedSemantics.wordModulus]

theorem Program.switchZeroReturn_wf
    (value fallback : Word) :
    WF (Program.switchZeroReturn value fallback) := by
  exact Program.returnStmt_wf (Stmt.switchZeroReturn value fallback)

theorem Program.switchZeroReturn_semantics
    (value fallback : Word) :
    Semantics (Program.switchZeroReturn value fallback)
      (L01_ValidSolidity.Behavior.returnedWord
        (SharedSemantics.norm value)) := by
  exact Semantics.returnValue
    ⟨Expr.word value,
      Program.switchZeroReturn_returnedExpr? value fallback,
      Expr.word_eval_norm value⟩

theorem Program.isReturnValue_of_isReturnWord {program : Program}
    {value : Word}
    (hEval : (Expr.word value).Eval value)
    (hReturn : program.IsReturnWord value) :
    program.IsReturnValue value := by
  rcases hReturn with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  refine ⟨Expr.word value, ?_, hEval⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              simp [Program.returnedExpr?, Object.returnedExpr?,
                Stmt.returnedExpr?, Stmt.returnedExprs?,
                Stmt.neutral?, Expr.eval?, Expr.evalWith?,
                Expr.word0, Expr.word32]

theorem Program.isReturnValue_of_isReturnWord0 {program : Program}
    (hReturn : program.IsReturnWord0) :
    program.IsReturnValue 0 :=
  Program.isReturnValue_of_isReturnWord (by rfl) hReturn

theorem Program.isReturnValue_of_isReturnWord3 {program : Program}
    (hReturn : program.IsReturnWord3) :
    program.IsReturnValue 3 :=
  Program.isReturnValue_of_isReturnWord (by rfl) hReturn

theorem Program.isReturnValue_norm_of_isReturnWord {program : Program}
    {value : Word}
    (hReturn : program.IsReturnWord value) :
    program.IsReturnValue (SharedSemantics.norm value) := by
  rcases hReturn with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  refine ⟨Expr.word value, ?_, Expr.word_eval_norm value⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              simp [Program.returnedExpr?, Object.returnedExpr?,
                Stmt.returnedExpr?, Stmt.returnedExprs?,
                Stmt.neutral?, Expr.eval?, Expr.evalWith?,
                Expr.word0, Expr.word32]

theorem Program.IsReturnValue.value_eq {program : Program}
    {expr : Expr} {compiledValue sourceValue : Word}
    (hReturned : program.returnedExpr? = some expr)
    (hEval : expr.Eval compiledValue)
    (hSource : program.IsReturnValue sourceValue) :
    sourceValue = compiledValue := by
  rcases hSource with ⟨sourceExpr, hSourceReturned, hSourceEval⟩
  rw [hReturned] at hSourceReturned
  cases hSourceReturned
  simp [Expr.Eval] at hEval hSourceEval
  rw [hEval] at hSourceEval
  cases hSourceEval
  rfl

theorem Object.returnWord0_isReturnWord0 :
    Object.returnWord0.IsReturnWord0 := by
  simp [Object.returnWord0, Object.returnWord, Object.IsReturnWord0,
    Object.IsReturnWord]

theorem Object.returnWord_isReturnWord (value : Word) :
    (Object.returnWord value).IsReturnWord value := by
  simp [Object.returnWord, Object.IsReturnWord]

theorem Program.returnWord_isReturnWord (value : Word) :
    (Program.returnWord value).IsReturnWord value := by
  exact ⟨Object.returnWord_isReturnWord value, Profile.empty_isEmpty⟩

theorem Program.eq_returnWord_of_isReturnWord {program : Program}
    {value : Word}
    (hReturn : program.IsReturnWord value) :
    program = Program.returnWord value := by
  rcases hReturn with ⟨hObject, hProfile⟩
  rcases hObject with ⟨hCode, hFunctions, hData, hSubobjects⟩
  rcases hProfile with
    ⟨hLayout, hAbi, hEvents, hErrors, hMemoryRegions, hHelpers⟩
  cases program with
  | mk object profile =>
      cases object with
      | mk code functions data subobjects =>
          cases profile with
          | mk layout abi events errors memoryRegions emittedHelpers =>
              cases hCode
              cases hFunctions
              cases hData
              cases hSubobjects
              cases hLayout
              cases hAbi
              cases hEvents
              cases hErrors
              cases hMemoryRegions
              cases hHelpers
              rfl

theorem Program.returnWord0_isReturnWord0 :
    Program.returnWord0.IsReturnWord0 := by
  exact Program.returnWord_isReturnWord 0

theorem Program.returnWord_wf (value : Word) : WF (Program.returnWord value) := by
  exact Program.returnExpr_wf (Expr.word value)

theorem Program.returnWord_semantics_norm (value : Word) :
    Semantics (Program.returnWord value)
      (L01_ValidSolidity.Behavior.returnedWord
        (SharedSemantics.norm value)) := by
  exact Semantics.returnValue
    (Program.isReturnValue_norm_of_isReturnWord
      (Program.returnWord_isReturnWord value))

theorem Program.returnWord0_wf : WF Program.returnWord0 := by
  exact Program.returnWord_wf 0

theorem Program.returnWord0_semantics :
    Semantics Program.returnWord0
      (L01_ValidSolidity.Behavior.returnedWord 0) := by
  exact Semantics.returnWord0 Program.returnWord0_isReturnWord0

theorem Object.returnWord3_isReturnWord3 :
    Object.returnWord3.IsReturnWord3 := by
  simp [Object.returnWord3, Object.returnWord, Object.IsReturnWord3,
    Object.IsReturnWord]

theorem Program.returnWord3_isReturnWord3 :
    Program.returnWord3.IsReturnWord3 := by
  exact Program.returnWord_isReturnWord 3

theorem Program.returnWord3_wf : WF Program.returnWord3 := by
  exact Program.returnWord_wf 3

theorem Program.returnWord3_semantics :
    Semantics Program.returnWord3
      (L01_ValidSolidity.Behavior.returnedWord 3) := by
  exact Semantics.returnWord3 Program.returnWord3_isReturnWord3

theorem Program.returnAdd1And2_wf : WF Program.returnAdd1And2 := by
  exact Program.returnExpr_wf Expr.add1And2

theorem Program.returnAdd1And2_semantics :
    Semantics Program.returnAdd1And2
      (L01_ValidSolidity.Behavior.returnedWord 3) := by
  exact Program.returnExpr_semantics Expr.eval?_add1And2

end L03_GeneratedYul
end Spine
end SolidCore

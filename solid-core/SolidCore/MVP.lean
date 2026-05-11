import SolidCore.Compiler

namespace SolidCore
namespace Solidity
namespace MVP

abbrev YulValue := SolidCoreYulCore.FullYul.Value
abbrev YulStmt := SolidCoreYulCore.FullYul.Stmt
abbrev YulExpr := SolidCoreYulCore.FullYul.Expr
abbrev SymConfig := SolidCoreYulCore.SymYul.Config
abbrev SymResult := SolidCoreYulCore.SymYul.Result

structure State where
  returnValue : YulValue
  storage : SolidCoreYulCore.FullYul.AccountValueMap
  deriving DecidableEq, Repr

def State.toStorageState (state : State) : Core.Storage.State :=
  { returnValue := state.returnValue, storage := state.storage }

def State.toConfig (state : State) : SymConfig :=
  state.toStorageState.toConfig

def State.withReturn (state : State) (value : YulValue) : State :=
  { state with returnValue := value }

def State.withWordReturn (state : State) (value : Word) : State :=
  state.withReturn (SolidCoreYulCore.FullYul.Value.word value)

def State.storeValue (state : State) (slot : Expr) (value : YulValue) :
    State :=
  { state with
    storage :=
      storageWrite state.storage
        (SolidCoreYulCore.FullYul.Value.word slot.eval)
        value }

def State.store (state : State) (slot value : Expr) : State :=
  state.storeValue slot
    (SolidCoreYulCore.FullYul.Value.word value.eval)

def State.load (state : State) (slot : Expr) : YulValue :=
  match storageLookup? state.storage
      (SolidCoreYulCore.FullYul.Value.word slot.eval) with
  | some value => value
  | none =>
      SolidCoreYulCore.FullYul.Value.storageWord storageAccountZero
        (SolidCoreYulCore.FullYul.Value.word slot.eval)

def StateExpr.subValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.subWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.sub lhs rhs

def StateExpr.mulValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.mulWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.mul lhs rhs

def StateExpr.eqValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.eqWord lhs rhs)
  | lhs, rhs =>
      if lhs = rhs then
        SolidCoreYulCore.FullYul.Value.word 1
      else
        SolidCoreYulCore.FullYul.Value.binaryBuiltin
          SolidCoreYulCore.Evm.Builtin.eqOp lhs rhs

def StateExpr.ltValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.ltWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.ltOp lhs rhs

def StateExpr.gtValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.gtWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.gtOp lhs rhs

def StateExpr.andValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.andWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.andOp lhs rhs

def StateExpr.orValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.orWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.orOp lhs rhs

def StateExpr.xorValue (lhs rhs : YulValue) : YulValue :=
  match lhs, rhs with
  | SolidCoreYulCore.FullYul.Value.word lhs,
      SolidCoreYulCore.FullYul.Value.word rhs =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.xorWord lhs rhs)
  | lhs, rhs =>
      SolidCoreYulCore.FullYul.Value.binaryBuiltin
        SolidCoreYulCore.Evm.Builtin.xorOp lhs rhs

def StateExpr.notValue (value : YulValue) : YulValue :=
  match value with
  | SolidCoreYulCore.FullYul.Value.word word =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.notWord word)
  | value =>
      SolidCoreYulCore.FullYul.Value.unaryBuiltin
        SolidCoreYulCore.Evm.Builtin.notOp value

def StateExpr.iszeroValue (value : YulValue) : YulValue :=
  match value with
  | SolidCoreYulCore.FullYul.Value.word word =>
      SolidCoreYulCore.FullYul.Value.word
        (SolidCoreYulCore.iszeroWord word)
  | value =>
      SolidCoreYulCore.FullYul.Value.unaryBuiltin
        SolidCoreYulCore.Evm.Builtin.iszero value

theorem StateExpr.ifSomePair
    {α β : Type} (p : Prop) [Decidable p]
    (thenValue elseValue : α) (state : β) :
    (if p then some (thenValue, state) else some (elseValue, state)) =
      some ((if p then thenValue else elseValue), state) := by
  by_cases h : p <;> simp [h]

theorem StateExpr.evalEvmBuiltin_sub_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.sub [lhs, rhs] state =
      some (StateExpr.subValue lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem StateExpr.evalEvmBuiltin_mul_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.mul [lhs, rhs] state =
      some (StateExpr.mulValue lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem StateExpr.evalEvmBuiltin_eq_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.eqOp [lhs, rhs] state =
      some (StateExpr.eqValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_eq_values]
  cases lhs <;> cases rhs <;> try rfl
  all_goals
    simp [StateExpr.eqValue, StateExpr.ifSomePair]

theorem StateExpr.evalEvmBuiltin_lt_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.ltOp [lhs, rhs] state =
      some (StateExpr.ltValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_lt_values]
  cases lhs <;> cases rhs <;>
    rfl

theorem StateExpr.evalEvmBuiltin_gt_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.gtOp [lhs, rhs] state =
      some (StateExpr.gtValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_gt_values]
  cases lhs <;> cases rhs <;>
    rfl

theorem StateExpr.evalEvmBuiltin_and_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.andOp [lhs, rhs] state =
      some (StateExpr.andValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_and_values]
  cases lhs <;> cases rhs <;>
    rfl

theorem StateExpr.evalEvmBuiltin_or_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.orOp [lhs, rhs] state =
      some (StateExpr.orValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_or_values]
  cases lhs <;> cases rhs <;>
    rfl

theorem StateExpr.evalEvmBuiltin_xor_values
    (state : SolidCoreYulCore.FullYul.EvmState)
    (lhs rhs : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.xorOp [lhs, rhs] state =
      some (StateExpr.xorValue lhs rhs, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_xor_values]
  cases lhs <;> cases rhs <;>
    rfl

theorem StateExpr.evalEvmBuiltin_not_values
    (state : SolidCoreYulCore.FullYul.EvmState) (value : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.notOp [value] state =
      some (StateExpr.notValue value, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_not_values]
  cases value <;>
    rfl

theorem StateExpr.evalEvmBuiltin_iszero_values
    (state : SolidCoreYulCore.FullYul.EvmState) (value : YulValue) :
    SolidCoreYulCore.FullYul.evalEvmBuiltin
        SolidCoreYulCore.Evm.Builtin.iszero [value] state =
      some (StateExpr.iszeroValue value, state) := by
  rw [SolidCoreYulCore.FullYul.evalEvmBuiltin_iszero_values]
  cases value <;>
    rfl

inductive StateExpr where
  | pure : Expr -> StateExpr
  | load : Expr -> StateExpr
  | add : StateExpr -> StateExpr -> StateExpr
  | sub : StateExpr -> StateExpr -> StateExpr
  | mul : StateExpr -> StateExpr -> StateExpr
  | eq : StateExpr -> StateExpr -> StateExpr
  | lt : StateExpr -> StateExpr -> StateExpr
  | gt : StateExpr -> StateExpr -> StateExpr
  | bitAnd : StateExpr -> StateExpr -> StateExpr
  | bitOr : StateExpr -> StateExpr -> StateExpr
  | bitXor : StateExpr -> StateExpr -> StateExpr
  | bitNot : StateExpr -> StateExpr
  | iszero : StateExpr -> StateExpr
  deriving DecidableEq, Repr

def StateExpr.eval (state : State) : StateExpr -> YulValue
  | StateExpr.pure expr =>
      SolidCoreYulCore.FullYul.Value.word expr.eval
  | StateExpr.load slot =>
      state.load slot
  | StateExpr.add lhs rhs =>
      Core.Storage.addValue (lhs.eval state) (rhs.eval state)
  | StateExpr.sub lhs rhs =>
      StateExpr.subValue (lhs.eval state) (rhs.eval state)
  | StateExpr.mul lhs rhs =>
      StateExpr.mulValue (lhs.eval state) (rhs.eval state)
  | StateExpr.eq lhs rhs =>
      StateExpr.eqValue (lhs.eval state) (rhs.eval state)
  | StateExpr.lt lhs rhs =>
      StateExpr.ltValue (lhs.eval state) (rhs.eval state)
  | StateExpr.gt lhs rhs =>
      StateExpr.gtValue (lhs.eval state) (rhs.eval state)
  | StateExpr.bitAnd lhs rhs =>
      StateExpr.andValue (lhs.eval state) (rhs.eval state)
  | StateExpr.bitOr lhs rhs =>
      StateExpr.orValue (lhs.eval state) (rhs.eval state)
  | StateExpr.bitXor lhs rhs =>
      StateExpr.xorValue (lhs.eval state) (rhs.eval state)
  | StateExpr.bitNot expr =>
      StateExpr.notValue (expr.eval state)
  | StateExpr.iszero expr =>
      StateExpr.iszeroValue (expr.eval state)

def StateExpr.toFullYul : StateExpr -> YulExpr
  | StateExpr.pure expr => expr.toFullYul
  | StateExpr.load slot =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.sload
        [slot.toFullYul]
  | StateExpr.add lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.add
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.sub lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.sub
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.mul lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.mul
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.eq lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.eqOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.lt lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.ltOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.gt lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.gtOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.bitAnd lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.andOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.bitOr lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.orOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.bitXor lhs rhs =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.xorOp
        [lhs.toFullYul, rhs.toFullYul]
  | StateExpr.bitNot expr =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.notOp
        [expr.toFullYul]
  | StateExpr.iszero expr =>
      SolidCoreYulCore.FullYul.Expr.builtin
        SolidCoreYulCore.Evm.Builtin.iszero
        [expr.toFullYul]

def StateExpr.hasLoad? : StateExpr -> Bool
  | StateExpr.pure _ => false
  | StateExpr.load _ => true
  | StateExpr.add lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.sub lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.mul lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.eq lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.lt lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.gt lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.bitAnd lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.bitOr lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.bitXor lhs rhs => lhs.hasLoad? || rhs.hasLoad?
  | StateExpr.bitNot expr => expr.hasLoad?
  | StateExpr.iszero expr => expr.hasLoad?

inductive Result where
  | normal : State -> Result
  | returned : State -> Result
  | reverted : State -> Result
  deriving DecidableEq, Repr

def Result.revertConfig (state : State) : SymConfig :=
  { state.toConfig with
    evm :=
      (SolidCoreYulCore.FullYul.haltWith
        SolidCoreYulCore.Evm.HaltKind.reverted
        (SolidCoreYulCore.FullYul.SymbolicBytes.memorySnapshot 0 0 0)
        (SolidCoreYulCore.FullYul.expandMemory state.toConfig.evm 0 0)) }

def Result.toSymYulResults : Result -> List SymResult
  | Result.normal state =>
      [SolidCoreYulCore.SymYul.normalResult state.toConfig]
  | Result.returned state =>
      [{ flow := SolidCoreYulCore.FullYul.Flow.left
         config := state.toConfig }]
  | Result.reverted state =>
      [{ flow := SolidCoreYulCore.FullYul.Flow.halted
         config := Result.revertConfig state }]

inductive Stmt where
  | skip : Stmt
  | discard : Expr -> Stmt
  | returnExpr : Expr -> Stmt
  | returnStateExpr : StateExpr -> Stmt
  | revert : Stmt
  | store : Expr -> Expr -> Stmt
  | storeStateExpr : Expr -> StateExpr -> Stmt
  | loadReturn : Expr -> Stmt
  | storeThenIfLoad : Expr -> Expr -> Stmt -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt
  | switch1 : Expr -> Word -> Stmt -> Stmt -> Stmt
  | switch2 (discr : Expr)
      (firstLabel : Word) (firstBranch : Stmt)
      (secondLabel : Word) (secondBranch defaultBranch : Stmt)
      (hDistinct :
        SolidCoreYulCore.norm firstLabel ≠ SolidCoreYulCore.norm secondLabel) :
      Stmt
  | forFalse : Stmt -> Stmt
  | forOnce : Stmt -> Stmt
  | forIf : Expr -> Stmt -> Stmt

def Stmt.eval (state : State) : Stmt -> Result
  | Stmt.skip => Result.normal state
  | Stmt.discard _ => Result.normal state
  | Stmt.returnExpr expr =>
      Result.returned (state.withWordReturn expr.eval)
  | Stmt.returnStateExpr expr =>
      Result.returned (state.withReturn (expr.eval state))
  | Stmt.revert => Result.reverted state
  | Stmt.store slot value =>
      Result.normal (state.store slot value)
  | Stmt.storeStateExpr slot value =>
      Result.normal (state.storeValue slot (value.eval state))
  | Stmt.loadReturn slot =>
      Result.returned (state.withReturn (state.load slot))
  | Stmt.storeThenIfLoad slot value body =>
      let stored := state.store slot value
      if SolidCoreYulCore.norm value.eval = 0 then
        Result.normal stored
      else
        body.eval stored
  | Stmt.seq first second =>
      match first.eval state with
      | Result.normal state' => second.eval state'
      | Result.returned state' => Result.returned state'
      | Result.reverted state' => Result.reverted state'
  | Stmt.ifThen cond body =>
      if SolidCoreYulCore.norm cond.eval = 0 then
        Result.normal state
      else
        body.eval state
  | Stmt.switch1 discr label branch defaultBranch =>
      if SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm label then
        branch.eval state
      else
        defaultBranch.eval state
  | Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch _ =>
      if SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm firstLabel then
        firstBranch.eval state
      else if
          SolidCoreYulCore.norm discr.eval =
            SolidCoreYulCore.norm secondLabel then
        secondBranch.eval state
      else
        defaultBranch.eval state
  | Stmt.forFalse _ => Result.normal state
  | Stmt.forOnce body => body.eval state
  | Stmt.forIf cond body =>
      if SolidCoreYulCore.norm cond.eval = 0 then
        Result.normal state
      else
        body.eval state

def Stmt.fuel : Stmt -> Nat
  | Stmt.skip => 1
  | Stmt.discard _ => 1
  | Stmt.returnExpr _ => 2
  | Stmt.returnStateExpr _ => 2
  | Stmt.revert => 1
  | Stmt.store _ _ => 1
  | Stmt.storeStateExpr _ _ => 1
  | Stmt.loadReturn _ => 2
  | Stmt.storeThenIfLoad _ _ body => body.fuel + 3
  | Stmt.seq first second => first.fuel + second.fuel + 1
  | Stmt.ifThen _ body => body.fuel + 1
  | Stmt.switch1 _ _ branch defaultBranch =>
      branch.fuel + defaultBranch.fuel + 1
  | Stmt.switch2 _ _ firstBranch _ secondBranch defaultBranch _ =>
      firstBranch.fuel + secondBranch.fuel + defaultBranch.fuel + 3
  | Stmt.forFalse body => body.fuel + 1
  | Stmt.forOnce body => body.fuel + 4
  | Stmt.forIf _ body => body.fuel + 4

abbrev Stmt.bodyThenBreakFullYul (body : YulStmt) : YulStmt :=
  SolidCoreYulCore.FullYul.Stmt.seq
    body
    SolidCoreYulCore.FullYul.Stmt.break

abbrev Stmt.singleIterationLoopFullYul
    (cond : YulExpr) (body : YulStmt) : YulStmt :=
  SolidCoreYulCore.FullYul.Stmt.forLoop
    SolidCoreYulCore.FullYul.Stmt.skip
    cond
    SolidCoreYulCore.FullYul.Stmt.skip
    (Stmt.bodyThenBreakFullYul body)

def Stmt.revertZeroFullYul : YulStmt :=
  SolidCoreYulCore.FullYul.Stmt.expr
    (SolidCoreYulCore.FullYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.revertOp
      [ SolidCoreYulCore.FullYul.Expr.value
          (SolidCoreYulCore.FullYul.Value.word 0)
      , SolidCoreYulCore.FullYul.Expr.value
          (SolidCoreYulCore.FullYul.Value.word 0) ])

abbrev Stmt.sloadFullYul (slot : Expr) : YulExpr :=
  SolidCoreYulCore.FullYul.Expr.builtin
    SolidCoreYulCore.Evm.Builtin.sload
    [slot.toFullYul]

abbrev Stmt.sstoreFullYul (slot value : Expr) : YulStmt :=
  SolidCoreYulCore.FullYul.Stmt.expr
    (SolidCoreYulCore.FullYul.Expr.builtin
      SolidCoreYulCore.Evm.Builtin.sstore
      [slot.toFullYul, value.toFullYul])

abbrev Stmt.localFrameBodyFullYul
    (init : Expr) (tail : YulStmt) : List YulStmt :=
  [SolidCoreYulCore.FullYul.Stmt.seq
    (SolidCoreYulCore.FullYul.Stmt.let1 localName
      (some init.toFullYul))
    tail]

abbrev Stmt.localFrameFullYul
    (init : Expr) (tail : YulStmt) : YulStmt :=
  SolidCoreYulCore.FullYul.Stmt.block
    (Stmt.localFrameBodyFullYul init tail)

def Stmt.toFullYul : Stmt -> YulStmt
  | Stmt.skip => SolidCoreYulCore.FullYul.Stmt.skip
  | Stmt.discard _ => SolidCoreYulCore.FullYul.Stmt.skip
  | Stmt.returnExpr expr =>
      SolidCoreYulCore.FullYul.Stmt.seq
        (SolidCoreYulCore.FullYul.Stmt.assign returnName expr.toFullYul)
        SolidCoreYulCore.FullYul.Stmt.leave
  | Stmt.returnStateExpr expr =>
      SolidCoreYulCore.FullYul.Stmt.seq
        (SolidCoreYulCore.FullYul.Stmt.assign returnName expr.toFullYul)
        SolidCoreYulCore.FullYul.Stmt.leave
  | Stmt.revert => Stmt.revertZeroFullYul
  | Stmt.store slot value =>
      Stmt.sstoreFullYul slot value
  | Stmt.storeStateExpr slot value =>
      SolidCoreYulCore.FullYul.Stmt.expr
        (SolidCoreYulCore.FullYul.Expr.builtin
          SolidCoreYulCore.Evm.Builtin.sstore
          [slot.toFullYul, value.toFullYul])
  | Stmt.loadReturn slot =>
      SolidCoreYulCore.FullYul.Stmt.seq
        (SolidCoreYulCore.FullYul.Stmt.assign returnName
          (Stmt.sloadFullYul slot))
        SolidCoreYulCore.FullYul.Stmt.leave
  | Stmt.storeThenIfLoad slot value body =>
      SolidCoreYulCore.FullYul.Stmt.seq
        (Stmt.sstoreFullYul slot value)
        (SolidCoreYulCore.FullYul.Stmt.ifThen
          (Stmt.sloadFullYul slot)
          body.toFullYul)
  | Stmt.seq first second =>
      SolidCoreYulCore.FullYul.Stmt.seq first.toFullYul second.toFullYul
  | Stmt.ifThen cond body =>
      SolidCoreYulCore.FullYul.Stmt.ifThen cond.toFullYul body.toFullYul
  | Stmt.switch1 discr label branch defaultBranch =>
      SolidCoreYulCore.FullYul.Stmt.switch discr.toFullYul
        [(SolidCoreYulCore.FullYul.Value.word
          (SolidCoreYulCore.norm label), branch.toFullYul)]
        (some defaultBranch.toFullYul)
  | Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch _ =>
      SolidCoreYulCore.FullYul.Stmt.switch discr.toFullYul
        [ ( SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm firstLabel)
          , firstBranch.toFullYul )
        , ( SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm secondLabel)
          , secondBranch.toFullYul ) ]
        (some defaultBranch.toFullYul)
  | Stmt.forFalse body =>
      SolidCoreYulCore.FullYul.Stmt.forLoop
        SolidCoreYulCore.FullYul.Stmt.skip
        (SolidCoreYulCore.FullYul.Expr.value
          (SolidCoreYulCore.FullYul.Value.word 0))
        SolidCoreYulCore.FullYul.Stmt.skip
        body.toFullYul
  | Stmt.forOnce body =>
      Stmt.singleIterationLoopFullYul
        (SolidCoreYulCore.FullYul.Expr.value
          (SolidCoreYulCore.FullYul.Value.word 1))
        body.toFullYul
  | Stmt.forIf cond body =>
      Stmt.singleIterationLoopFullYul cond.toFullYul body.toFullYul

def Stmt.loopIf (cond : Expr) (body : Stmt) : Stmt :=
  Stmt.ifThen cond (Stmt.forOnce body)

def Stmt.boundedWhile : Nat -> Expr -> Stmt -> Stmt
  | 0, _, _ => Stmt.skip
  | n + 1, cond, body =>
      Stmt.loopIf cond (Stmt.seq body (Stmt.boundedWhile n cond body))

def Stmt.switchCases (discr : Expr) : List (Word × Stmt) -> Stmt -> Stmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      Stmt.switch1 discr label branch
        (Stmt.switchCases discr rest defaultBranch)

def Expr.guardOK? : Expr -> Bool
  | Expr.lit _ => true
  | Expr.neg expr => Expr.guardOK? expr
  | Expr.add lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.sub lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.mul lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.exp lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.div lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.mod lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedDiv lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedMod lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.addmod lhs rhs modulus =>
      Expr.guardOK? lhs && Expr.guardOK? rhs && Expr.guardOK? modulus
  | Expr.mulmod lhs rhs modulus =>
      Expr.guardOK? lhs && Expr.guardOK? rhs && Expr.guardOK? modulus
  | Expr.bitAnd lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.bitOr lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.bitXor lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.bitNot expr => Expr.guardOK? expr
  | Expr.shl value shift => Expr.guardOK? value && Expr.guardOK? shift
  | Expr.shr value shift => Expr.guardOK? value && Expr.guardOK? shift
  | Expr.sar value shift => Expr.guardOK? value && Expr.guardOK? shift
  | Expr.byteAt index value => Expr.guardOK? index && Expr.guardOK? value
  | Expr.iszero expr => Expr.guardOK? expr
  | Expr.boolAnd lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.boolOr lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.eq lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.ne lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.lt lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.gt lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.le lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.ge lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedLt lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedGt lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedLe lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs
  | Expr.signedGe lhs rhs => Expr.guardOK? lhs && Expr.guardOK? rhs

def Expr.GuardOK (expr : Expr) : Prop :=
  Expr.guardOK? expr = true

abbrev Expr.ValueOK (expr : Expr) : Prop :=
  Expr.GuardOK expr

abbrev Expr.SlotOK (expr : Expr) : Prop :=
  Expr.GuardOK expr

theorem Expr.guardOK (expr : Expr) : Expr.GuardOK expr := by
  induction expr <;>
    simp_all [Expr.GuardOK, Expr.guardOK?]

theorem Expr.valueOK (expr : Expr) : Expr.ValueOK expr :=
  Expr.guardOK expr

theorem Expr.slotOK (expr : Expr) : Expr.SlotOK expr :=
  Expr.guardOK expr

def StateExpr.ok? : StateExpr -> Bool
  | StateExpr.pure expr => Expr.guardOK? expr
  | StateExpr.load slot => Expr.guardOK? slot
  | StateExpr.add lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.sub lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.mul lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.eq lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.lt lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.gt lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.bitAnd lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.bitOr lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.bitXor lhs rhs => lhs.ok? && rhs.ok?
  | StateExpr.bitNot expr => expr.ok?
  | StateExpr.iszero expr => expr.ok?

def StateExpr.OK (expr : StateExpr) : Prop :=
  expr.ok? = true

theorem StateExpr.ok (expr : StateExpr) : StateExpr.OK expr := by
  induction expr with
  | pure expr =>
      exact Expr.guardOK expr
  | load slot =>
      exact Expr.guardOK slot
  | add lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | sub lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | mul lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | eq lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | lt lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | gt lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | bitAnd lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | bitOr lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | bitXor lhs rhs lhs_ih rhs_ih =>
      dsimp [StateExpr.OK, StateExpr.ok?]
      rw [lhs_ih, rhs_ih]
      rfl
  | bitNot expr expr_ih =>
      exact expr_ih
  | iszero expr expr_ih =>
      exact expr_ih

inductive Stmt.MVP : Stmt -> Prop where
  | skip : Stmt.MVP Stmt.skip
  | discard {expr : Expr} :
      Expr.ValueOK expr ->
      Stmt.MVP (Stmt.discard expr)
  | returnExpr {expr : Expr} :
      Expr.ValueOK expr ->
      Stmt.MVP (Stmt.returnExpr expr)
  | returnStateExpr {expr : StateExpr} :
      StateExpr.OK expr ->
      Stmt.MVP (Stmt.returnStateExpr expr)
  | revert : Stmt.MVP Stmt.revert
  | store {slot value : Expr} :
      Expr.SlotOK slot ->
      Expr.ValueOK value ->
      Stmt.MVP (Stmt.store slot value)
  | storeStateExpr {slot : Expr} {value : StateExpr} :
      Expr.SlotOK slot ->
      StateExpr.OK value ->
      Stmt.MVP (Stmt.storeStateExpr slot value)
  | loadReturn {slot : Expr} :
      Expr.SlotOK slot ->
      Stmt.MVP (Stmt.loadReturn slot)
  | storeThenIfLoad {slot value : Expr} {body : Stmt} :
      Expr.SlotOK slot ->
      Expr.GuardOK value ->
      Stmt.MVP body ->
      Stmt.MVP (Stmt.storeThenIfLoad slot value body)
  | seq {first second : Stmt} :
      Stmt.MVP first ->
      Stmt.MVP second ->
      Stmt.MVP (Stmt.seq first second)
  | ifThen {cond : Expr} {body : Stmt} :
      Expr.GuardOK cond ->
      Stmt.MVP body ->
      Stmt.MVP (Stmt.ifThen cond body)
  | switch1 {discr : Expr} {label : Word}
      {branch defaultBranch : Stmt} :
      Expr.GuardOK discr ->
      Stmt.MVP branch ->
      Stmt.MVP defaultBranch ->
      Stmt.MVP (Stmt.switch1 discr label branch defaultBranch)
  | switch2 {discr : Expr}
      {firstLabel : Word} {firstBranch : Stmt}
      {secondLabel : Word} {secondBranch defaultBranch : Stmt}
      {hDistinct :
        SolidCoreYulCore.norm firstLabel ≠ SolidCoreYulCore.norm secondLabel} :
      Expr.GuardOK discr ->
      Stmt.MVP firstBranch ->
      Stmt.MVP secondBranch ->
      Stmt.MVP defaultBranch ->
      Stmt.MVP
        (Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
          defaultBranch hDistinct)
  | forFalse {body : Stmt} :
      Stmt.MVP body ->
      Stmt.MVP (Stmt.forFalse body)
  | forOnce {body : Stmt} :
      Stmt.MVP body ->
      Stmt.MVP (Stmt.forOnce body)
  | forIf {cond : Expr} {body : Stmt} :
      Expr.GuardOK cond ->
      Stmt.MVP body ->
      Stmt.MVP (Stmt.forIf cond body)

theorem Stmt.MVP.loopIf
    {cond : Expr} {body : Stmt}
    (hCond : Expr.GuardOK cond) (hBody : Stmt.MVP body) :
    Stmt.MVP (Stmt.loopIf cond body) :=
  Stmt.MVP.ifThen hCond (Stmt.MVP.forOnce hBody)

theorem Stmt.MVP.boundedWhile
    (bound : Nat) {cond : Expr} {body : Stmt}
    (hCond : Expr.GuardOK cond) (hBody : Stmt.MVP body) :
    Stmt.MVP (Stmt.boundedWhile bound cond body) := by
  induction bound with
  | zero =>
      exact Stmt.MVP.skip
  | succ bound ih =>
      exact
        Stmt.MVP.loopIf hCond
          (Stmt.MVP.seq hBody ih)

theorem Stmt.MVP.switchCases
    {discr : Expr} (cases : List (Word × Stmt)) {defaultBranch : Stmt}
    (hDiscr : Expr.GuardOK discr)
    (hCases :
      ∀ switchCase, switchCase ∈ cases -> Stmt.MVP switchCase.2)
    (hDefault : Stmt.MVP defaultBranch) :
    Stmt.MVP (Stmt.switchCases discr cases defaultBranch) := by
  induction cases with
  | nil =>
      simpa [Stmt.switchCases] using hDefault
  | cons head rest ih =>
      rcases head with ⟨label, branch⟩
      have hBranch : Stmt.MVP branch :=
        hCases (label, branch) (by simp)
      have hRest :
          ∀ switchCase, switchCase ∈ rest -> Stmt.MVP switchCase.2 := by
        intro switchCase hMem
        exact hCases switchCase (by simp [hMem])
      simp [Stmt.switchCases]
      exact Stmt.MVP.switch1 hDiscr hBranch (ih hRest)

def initialState : State :=
  { returnValue := SolidCoreYulCore.FullYul.Value.word 0, storage := [] }

def initialStaticContext : SolidCoreYulCore.FullYul.StaticContext :=
  Program.initialStaticContext

def Stmt.localStaticContext : SolidCoreYulCore.FullYul.StaticContext :=
  { initialStaticContext with
    vars := localName :: initialStaticContext.vars }

def Stmt.localFrameEntryConfig (state : State) (localValue : Word) :
    SymConfig :=
  { state.toConfig with
    env :=
      [ (localName, SolidCoreYulCore.FullYul.Value.word localValue)
      , (returnName, state.returnValue) ] }

def Stmt.localFrameTailReturnConfig
    (state : State) (localValue returnValue : Word) : SymConfig :=
  { state.toConfig with
    env :=
      [ (localName, SolidCoreYulCore.FullYul.Value.word localValue)
      , (returnName, SolidCoreYulCore.FullYul.Value.word returnValue) ] }

theorem currentSolidCore_word_valueOK (value : Word) :
    SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore.valueOK
      (SolidCoreYulCore.FullYul.Value.word value) :=
  SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreValue.word value

theorem currentSolidCore_value_word_compilerEmittable (value : Word) :
    SolidCoreYulCore.FullYul.CompilerEmittableExpr
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (SolidCoreYulCore.FullYul.Expr.value
        (SolidCoreYulCore.FullYul.Value.word value)) := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableExpr.value
      (currentSolidCore_word_valueOK value)

theorem currentSolidCore_exprs1_compilerEmittable
    {expr : SolidCoreYulCore.FullYul.Expr}
    (hExpr :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore expr) :
    SolidCoreYulCore.FullYul.CompilerEmittableExprs
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore [expr] := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
      hExpr
      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil

theorem currentSolidCore_exprs2_compilerEmittable
    {lhs rhs : SolidCoreYulCore.FullYul.Expr}
    (hLhs :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore lhs)
    (hRhs :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore rhs) :
    SolidCoreYulCore.FullYul.CompilerEmittableExprs
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore [lhs, rhs] := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
      hLhs
      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
        hRhs
        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)

theorem currentSolidCore_builtin1_compilerEmittable
    {builtin : SolidCoreYulCore.Evm.Builtin}
    (hBuiltin :
      SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin
        builtin)
    {arg : SolidCoreYulCore.FullYul.Expr}
    (hArg :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore arg) :
    SolidCoreYulCore.FullYul.CompilerEmittableExpr
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (SolidCoreYulCore.FullYul.Expr.builtin builtin [arg]) := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
      hBuiltin
      (currentSolidCore_exprs1_compilerEmittable hArg)

theorem currentSolidCore_builtin2_compilerEmittable
    {builtin : SolidCoreYulCore.Evm.Builtin}
    (hBuiltin :
      SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin
        builtin)
    {lhs rhs : SolidCoreYulCore.FullYul.Expr}
    (hLhs :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore lhs)
    (hRhs :
      SolidCoreYulCore.FullYul.CompilerEmittableExpr
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore rhs) :
    SolidCoreYulCore.FullYul.CompilerEmittableExpr
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (SolidCoreYulCore.FullYul.Expr.builtin builtin [lhs, rhs]) := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
      hBuiltin
      (currentSolidCore_exprs2_compilerEmittable hLhs hRhs)

theorem StateExpr.toFullYul_compilerEmittable (expr : StateExpr) :
    SolidCoreYulCore.FullYul.CompilerEmittableExpr
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      expr.toFullYul := by
  induction expr with
  | pure expr =>
      exact Expr.toFullYul_compilerEmittable expr
  | load slot =>
      exact
        currentSolidCore_builtin1_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sload
          (Expr.toFullYul_compilerEmittable slot)
  | add lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.add
          lhs_ih rhs_ih
  | sub lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sub
          lhs_ih rhs_ih
  | mul lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.mul
          lhs_ih rhs_ih
  | eq lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.eqOp
          lhs_ih rhs_ih
  | lt lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.ltOp
          lhs_ih rhs_ih
  | gt lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.gtOp
          lhs_ih rhs_ih
  | bitAnd lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.andOp
          lhs_ih rhs_ih
  | bitOr lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.orOp
          lhs_ih rhs_ih
  | bitXor lhs rhs lhs_ih rhs_ih =>
      exact
        currentSolidCore_builtin2_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.xorOp
          lhs_ih rhs_ih
  | bitNot expr expr_ih =>
      exact
        currentSolidCore_builtin1_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.notOp
          expr_ih
  | iszero expr expr_ih =>
      exact
        currentSolidCore_builtin1_compilerEmittable
          SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
          expr_ih

theorem StateExpr.toFullYul_staticChecked
    (ctx : SolidCoreYulCore.FullYul.StaticContext) (expr : StateExpr) :
    SolidCoreYulCore.FullYul.checkExpr ctx expr.toFullYul = true := by
  induction expr with
  | pure expr =>
      exact Expr.toFullYul_staticChecked ctx expr
  | load slot =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?,
        Expr.toFullYul_staticChecked]
  | add lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | sub lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | mul lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | eq lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | lt lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | gt lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | bitAnd lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | bitOr lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | bitXor lhs rhs lhs_ih rhs_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, lhs_ih, rhs_ih]
  | bitNot expr expr_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, expr_ih]
  | iszero expr expr_ih =>
      simp [StateExpr.toFullYul, SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?, expr_ih]

theorem State.evalExpr_sload (state : State) (slot : Expr) :
    SolidCoreYulCore.SymYul.evalExpr state.toConfig
        (StateExpr.load slot).toFullYul =
      some (state.load slot, state.toConfig) := by
  cases hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
        state.storage storageAccountZero
        (SolidCoreYulCore.FullYul.Value.word slot.eval) with
  | none =>
      have hEvalRaw :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.sload
              [SolidCoreYulCore.FullYul.Value.word slot.eval]
              ({ storage := state.storage } :
                SolidCoreYulCore.FullYul.EvmState) =
            some
              ( SolidCoreYulCore.FullYul.Value.storageWord
                  storageAccountZero
                  (SolidCoreYulCore.FullYul.Value.word slot.eval)
              , ({ storage := state.storage } :
                  SolidCoreYulCore.FullYul.EvmState) ) := by
        simpa [SolidCoreYulCore.FullYul.EvmState.empty] using
          evalEvmBuiltin_sload_accountZero_missing
            state.storage
            (SolidCoreYulCore.FullYul.Value.word slot.eval)
            hLookup
      have hEvalEvm :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.sload
              [SolidCoreYulCore.FullYul.Value.word slot.eval]
              state.toConfig.evm =
            some (state.load slot, state.toConfig.evm) := by
        simpa [State.toConfig, State.toStorageState,
          Core.Storage.State.toConfig, State.load, storageLookup?, hLookup,
          SolidCoreYulCore.FullYul.EvmState.empty] using hEvalRaw
      have hSlot := Expr.toFullYul_correct_env state.toConfig slot
      simp [StateExpr.toFullYul, SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, hSlot, hEvalEvm]
  | some value =>
      have hEvalRaw :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.sload
              [SolidCoreYulCore.FullYul.Value.word slot.eval]
              ({ storage := state.storage } :
                SolidCoreYulCore.FullYul.EvmState) =
            some
              ( value
              , ({ storage := state.storage } :
                  SolidCoreYulCore.FullYul.EvmState) ) := by
        simpa [SolidCoreYulCore.FullYul.EvmState.empty] using
          evalEvmBuiltin_sload_accountZero_present
            state.storage
            (SolidCoreYulCore.FullYul.Value.word slot.eval)
            value hLookup
      have hEvalEvm :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.sload
              [SolidCoreYulCore.FullYul.Value.word slot.eval]
              state.toConfig.evm =
            some (state.load slot, state.toConfig.evm) := by
        simpa [State.toConfig, State.toStorageState,
          Core.Storage.State.toConfig, State.load, storageLookup?, hLookup,
          SolidCoreYulCore.FullYul.EvmState.empty] using hEvalRaw
      have hSlot := Expr.toFullYul_correct_env state.toConfig slot
      simp [StateExpr.toFullYul, SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, hSlot, hEvalEvm]

theorem StateExpr.toFullYul_correct_env
    (state : State) (expr : StateExpr) :
    SolidCoreYulCore.SymYul.evalExpr state.toConfig expr.toFullYul =
      some (expr.eval state, state.toConfig) := by
  induction expr with
  | pure expr =>
      simpa [StateExpr.toFullYul, StateExpr.eval] using
        Expr.toFullYul_correct_env state.toConfig expr
  | load slot =>
      simpa [StateExpr.eval] using State.evalExpr_sload state slot
  | add lhs rhs lhs_ih rhs_ih =>
      have hAdd :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.add
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( Core.Storage.addValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        Core.Storage.evalEvmBuiltin_add_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hAdd]
  | sub lhs rhs lhs_ih rhs_ih =>
      have hSub :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.sub
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.subValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_sub_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hSub]
  | mul lhs rhs lhs_ih rhs_ih =>
      have hMul :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.mul
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.mulValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_mul_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hMul]
  | eq lhs rhs lhs_ih rhs_ih =>
      have hEq :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.eqOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.eqValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_eq_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hEq]
  | lt lhs rhs lhs_ih rhs_ih =>
      have hLt :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.ltOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.ltValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_lt_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hLt]
  | gt lhs rhs lhs_ih rhs_ih =>
      have hGt :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.gtOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.gtValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_gt_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hGt]
  | bitAnd lhs rhs lhs_ih rhs_ih =>
      have hAnd :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.andOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.andValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_and_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hAnd]
  | bitOr lhs rhs lhs_ih rhs_ih =>
      have hOr :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.orOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.orValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_or_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hOr]
  | bitXor lhs rhs lhs_ih rhs_ih =>
      have hXor :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.xorOp
              [lhs.eval state, rhs.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.xorValue (lhs.eval state) (rhs.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_xor_values
          state.toConfig.evm (lhs.eval state) (rhs.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, lhs_ih, rhs_ih, hXor]
  | bitNot expr expr_ih =>
      have hNot :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.notOp
              [expr.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.notValue (expr.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_not_values
          state.toConfig.evm (expr.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, expr_ih, hNot]
  | iszero expr expr_ih =>
      have hIszero :
          SolidCoreYulCore.FullYul.evalEvmBuiltin
              SolidCoreYulCore.Evm.Builtin.iszero
              [expr.eval state]
              state.toConfig.evm =
            some
              ( StateExpr.iszeroValue (expr.eval state)
              , state.toConfig.evm ) :=
        StateExpr.evalEvmBuiltin_iszero_values
          state.toConfig.evm (expr.eval state)
      simp [StateExpr.toFullYul, StateExpr.eval,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.evalExprs, expr_ih, hIszero]

theorem Stmt.localFrameFullYul_compilerEmittable
    (init : Expr) {tail : YulStmt}
    (hTail :
      SolidCoreYulCore.FullYul.CompilerEmittableStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        tail) :
    SolidCoreYulCore.FullYul.CompilerEmittableStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (Stmt.localFrameFullYul init tail) := by
  exact
    SolidCoreYulCore.FullYul.CompilerEmittableStmt.block
      (SolidCoreYulCore.FullYul.CompilerEmittableBlock.cons
        (SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
          (SolidCoreYulCore.FullYul.CompilerEmittableStmt.let1Some
            (name := localName)
            (Expr.toFullYul_compilerEmittable init))
          hTail)
        SolidCoreYulCore.FullYul.CompilerEmittableBlock.nil)

mutual
  theorem Stmt.toFullYul_compilerEmittable (stmt : Stmt) :
      SolidCoreYulCore.FullYul.CompilerEmittableStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        stmt.toFullYul := by
    induction stmt with
    | skip =>
        exact SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
    | discard expr =>
        exact SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
    | returnExpr expr =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.assign
              (name := returnName)
              (Expr.toFullYul_compilerEmittable expr))
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.leave
    | returnStateExpr expr =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.assign
              (name := returnName)
              (StateExpr.toFullYul_compilerEmittable expr))
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.leave
    | revert =>
        simpa [Stmt.toFullYul, Stmt.revertZeroFullYul] using
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.expr
            (currentSolidCore_builtin2_compilerEmittable
              SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.revertOp
              (currentSolidCore_value_word_compilerEmittable 0)
              (currentSolidCore_value_word_compilerEmittable 0))
    | store slot value =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.expr
            (currentSolidCore_builtin2_compilerEmittable
              SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
              (Expr.toFullYul_compilerEmittable slot)
              (Expr.toFullYul_compilerEmittable value))
    | storeStateExpr slot value =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.expr
            (currentSolidCore_builtin2_compilerEmittable
              SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
              (Expr.toFullYul_compilerEmittable slot)
              (StateExpr.toFullYul_compilerEmittable value))
    | loadReturn slot =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.assign
              (name := returnName)
              (currentSolidCore_builtin1_compilerEmittable
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sload
                (Expr.toFullYul_compilerEmittable slot)))
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.leave
    | storeThenIfLoad slot value _ body_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.expr
              (currentSolidCore_builtin2_compilerEmittable
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sstore
                (Expr.toFullYul_compilerEmittable slot)
                (Expr.toFullYul_compilerEmittable value)))
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.ifThen
              (currentSolidCore_builtin1_compilerEmittable
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sload
                (Expr.toFullYul_compilerEmittable slot))
              body_ih)
    | seq _ _ first_ih second_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
            first_ih second_ih
    | ifThen cond _ body_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.ifThen
            (Expr.toFullYul_compilerEmittable cond)
            body_ih
    | switch1 discr label _ _ branch_ih default_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.switch
            trivial
            (Expr.toFullYul_compilerEmittable discr)
            (SolidCoreYulCore.FullYul.CompilerEmittableSwitchCases.cons
              (currentSolidCore_word_valueOK (SolidCoreYulCore.norm label))
              branch_ih
              SolidCoreYulCore.FullYul.CompilerEmittableSwitchCases.nil)
            (SolidCoreYulCore.FullYul.CompilerEmittableOptionalStmt.some
              default_ih)
    | switch2 discr firstLabel _ secondLabel _ _ _
        first_ih second_ih default_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.switch
            trivial
            (Expr.toFullYul_compilerEmittable discr)
            (SolidCoreYulCore.FullYul.CompilerEmittableSwitchCases.cons
              (currentSolidCore_word_valueOK
                (SolidCoreYulCore.norm firstLabel))
              first_ih
              (SolidCoreYulCore.FullYul.CompilerEmittableSwitchCases.cons
                (currentSolidCore_word_valueOK
                  (SolidCoreYulCore.norm secondLabel))
                second_ih
                SolidCoreYulCore.FullYul.CompilerEmittableSwitchCases.nil))
            (SolidCoreYulCore.FullYul.CompilerEmittableOptionalStmt.some
              default_ih)
    | forFalse _ body_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.forLoop
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            (currentSolidCore_value_word_compilerEmittable 0)
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            body_ih
    | forOnce _ body_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.forLoop
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            (currentSolidCore_value_word_compilerEmittable 1)
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
              body_ih
              SolidCoreYulCore.FullYul.CompilerEmittableStmt.break)
    | forIf cond _ body_ih =>
        exact
          SolidCoreYulCore.FullYul.CompilerEmittableStmt.forLoop
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            (Expr.toFullYul_compilerEmittable cond)
            SolidCoreYulCore.FullYul.CompilerEmittableStmt.skip
            (SolidCoreYulCore.FullYul.CompilerEmittableStmt.seq
              body_ih
              SolidCoreYulCore.FullYul.CompilerEmittableStmt.break)
end

theorem Stmt.toFullYul_accepted_currentSolidCore
    (stmt : Stmt)
    (hChecked :
      SolidCoreYulCore.FullYul.checkStmtFuel stmt.fuel
          initialStaticContext false true stmt.toFullYul =
        some initialStaticContext) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      stmt.fuel initialStaticContext false true stmt.toFullYul
      initialStaticContext := by
  exact
    { emittable := Stmt.toFullYul_compilerEmittable stmt
      checked := hChecked }

theorem Stmt.fuel_pos (stmt : Stmt) : 0 < stmt.fuel := by
  induction stmt with
  | skip => simp [Stmt.fuel]
  | discard _ => simp [Stmt.fuel]
  | returnExpr _ => simp [Stmt.fuel]
  | returnStateExpr _ => simp [Stmt.fuel]
  | revert => simp [Stmt.fuel]
  | store _ _ => simp [Stmt.fuel]
  | storeStateExpr _ _ => simp [Stmt.fuel]
  | loadReturn _ => simp [Stmt.fuel]
  | storeThenIfLoad _ _ _ _ => simp [Stmt.fuel]
  | seq _ _ _ _ => simp [Stmt.fuel]
  | ifThen _ _ _ => simp [Stmt.fuel]
  | switch1 _ _ _ _ _ _ => simp [Stmt.fuel]
  | switch2 _ _ _ _ _ _ _ _ _ _ => simp [Stmt.fuel]
  | forFalse _ _ => simp [Stmt.fuel]
  | forOnce _ _ => simp [Stmt.fuel]
  | forIf _ _ _ => simp [Stmt.fuel]

theorem Stmt.predeclare_toFullYul
    (ctx : SolidCoreYulCore.FullYul.StaticContext) (stmt : Stmt) :
    SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs? ctx stmt.toFullYul =
      some ctx := by
  induction stmt generalizing ctx with
  | skip => rfl
  | discard _ => rfl
  | returnExpr _ => rfl
  | returnStateExpr _ => rfl
  | revert => rfl
  | store _ _ => rfl
  | storeStateExpr _ _ => rfl
  | loadReturn _ => rfl
  | storeThenIfLoad _ _ body body_ih =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?]
  | seq first second first_ih second_ih =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
        first_ih, second_ih]
  | ifThen _ _ _ => rfl
  | switch1 _ _ _ _ _ _ => rfl
  | switch2 _ _ _ _ _ _ _ _ _ _ => rfl
  | forFalse body _ =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?]
  | forOnce body _ =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?]
  | forIf _ body _ =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?]

theorem Stmt.localFrameFullYul_staticChecked_from
    (checkFuel : Nat) (inLoop : Bool) (init : Expr) {tail : YulStmt}
    (hFuel : 0 < checkFuel)
    (hPre :
      SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?
          initialStaticContext tail =
        some initialStaticContext)
    (hTail :
      SolidCoreYulCore.FullYul.checkStmtFuel
          checkFuel Stmt.localStaticContext inLoop true tail =
        some Stmt.localStaticContext) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (checkFuel + 3) initialStaticContext inLoop true
        (Stmt.localFrameFullYul init tail) =
      some initialStaticContext := by
  cases checkFuel with
  | zero => omega
  | succ checkFuel =>
  have hPre' :
      SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?
          { vars := [0], funcs := [] } tail =
        some { vars := [0], funcs := [] } := by
    simpa [initialStaticContext, Program.initialStaticContext, returnName]
      using hPre
  have hTail' :
      SolidCoreYulCore.FullYul.checkStmtFuel
          (Nat.succ checkFuel)
          { vars := [1, 0], funcs := [] }
          inLoop true tail =
        some { vars := [1, 0], funcs := [] } := by
    simpa [Stmt.localStaticContext, initialStaticContext,
      Program.initialStaticContext, returnName, localName] using hTail
  simp [
    initialStaticContext, Program.initialStaticContext,
    returnName, localName,
    SolidCoreYulCore.FullYul.checkStmtFuel,
    SolidCoreYulCore.FullYul.checkBlockFuel,
    SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
    SolidCoreYulCore.FullYul.predeclareBlockFunctionSigs?,
    SolidCoreYulCore.FullYul.addVarName?,
    SolidCoreYulCore.FullYul.addScopedName?,
    SolidCoreYulCore.FullYul.containsFunctionName,
    SolidCoreYulCore.FullYul.containsName,
    Expr.toFullYul_staticChecked, hPre', hTail']

theorem Stmt.bodyThenBreakFullYul_staticChecked_from
    (extraFuel : Nat) (body : Stmt)
    (hBody :
      SolidCoreYulCore.FullYul.checkStmtFuel
          (extraFuel + body.fuel + 2)
          initialStaticContext true true body.toFullYul =
        some initialStaticContext) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (extraFuel + body.fuel + 3)
        initialStaticContext true true
        (Stmt.bodyThenBreakFullYul body.toFullYul) =
      some initialStaticContext := by
  rw [show extraFuel + body.fuel + 3 =
      (extraFuel + body.fuel + 2) + 1 by omega]
  simp [SolidCoreYulCore.FullYul.checkStmtFuel,
    SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
    Stmt.predeclare_toFullYul, hBody]

theorem Stmt.singleIterationLoopFullYul_staticChecked_from
    (extraFuel : Nat) (inLoop : Bool) (cond : YulExpr) (body : Stmt)
    (hCond :
      SolidCoreYulCore.FullYul.checkExpr initialStaticContext cond = true)
    (hBody :
      SolidCoreYulCore.FullYul.checkStmtFuel
          (extraFuel + body.fuel + 2)
          initialStaticContext true true body.toFullYul =
        some initialStaticContext) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (extraFuel + body.fuel + 4)
        initialStaticContext inLoop true
        (Stmt.singleIterationLoopFullYul cond body.toFullYul) =
      some initialStaticContext := by
  rw [show extraFuel + body.fuel + 4 =
      (extraFuel + body.fuel + 3) + 1 by omega]
  simp [SolidCoreYulCore.FullYul.checkStmtFuel,
    SolidCoreYulCore.FullYul.stmtHasNoFunDefs,
    SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
    Stmt.predeclare_toFullYul, hCond, hBody]

set_option linter.unusedSimpArgs false in
theorem Stmt.toFullYul_staticChecked_from_inLoop
    (extraFuel : Nat) (inLoop : Bool) (stmt : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (extraFuel + stmt.fuel)
        initialStaticContext inLoop true stmt.toFullYul =
      some initialStaticContext := by
  induction stmt generalizing extraFuel inLoop with
  | skip =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext,
          SolidCoreYulCore.FullYul.checkStmtFuel]
  | discard _ =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext,
          SolidCoreYulCore.FullYul.checkStmtFuel]
  | returnExpr expr =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext, returnName,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
          SolidCoreYulCore.FullYul.containsName,
          SolidCoreYulCore.FullYul.checkExpr,
          SolidCoreYulCore.FullYul.checkExprs,
          Expr.toFullYul_staticChecked]
  | returnStateExpr expr =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext, returnName,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
          SolidCoreYulCore.FullYul.containsName,
          StateExpr.toFullYul_staticChecked]
  | revert =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, Stmt.revertZeroFullYul,
          initialStaticContext, Program.initialStaticContext,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.checkStmtExpr,
          SolidCoreYulCore.FullYul.checkExpr,
          SolidCoreYulCore.FullYul.checkExprs,
          SolidCoreYulCore.Evm.Builtin.signature?]
  | store slot value =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.checkStmtExpr,
          SolidCoreYulCore.FullYul.checkExprs,
          SolidCoreYulCore.Evm.Builtin.signature?,
          Expr.toFullYul_staticChecked]
  | storeStateExpr slot value =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.checkStmtExpr,
          SolidCoreYulCore.FullYul.checkExprs,
          SolidCoreYulCore.Evm.Builtin.signature?,
          Expr.toFullYul_staticChecked,
          StateExpr.toFullYul_staticChecked]
  | loadReturn slot =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, initialStaticContext,
          Program.initialStaticContext, returnName,
          SolidCoreYulCore.FullYul.checkStmtFuel,
          SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
          SolidCoreYulCore.FullYul.containsName,
          SolidCoreYulCore.FullYul.checkExpr,
          SolidCoreYulCore.FullYul.checkExprs,
          SolidCoreYulCore.Evm.Builtin.signature?,
          Expr.toFullYul_staticChecked]
  | storeThenIfLoad slot value body body_ih =>
      have hBody :
          SolidCoreYulCore.FullYul.checkStmtFuel
              ((extraFuel + 1) + body.fuel)
              initialStaticContext inLoop true body.toFullYul =
            some initialStaticContext :=
        body_ih (extraFuel + 1) inLoop
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (body.fuel + 3) =
          (extraFuel + body.fuel + 2) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        SolidCoreYulCore.FullYul.checkStmtExpr,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
        Stmt.predeclare_toFullYul,
        SolidCoreYulCore.FullYul.checkExpr,
        SolidCoreYulCore.FullYul.checkExprs,
        SolidCoreYulCore.Evm.Builtin.signature?,
        Expr.toFullYul_staticChecked]
      have hBody' :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + body.fuel + 1)
              initialStaticContext inLoop true body.toFullYul =
            some initialStaticContext := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBody
      simp [hBody']
  | seq first second first_ih second_ih =>
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (first.fuel + second.fuel + 1) =
          (extraFuel + first.fuel + second.fuel) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
        Stmt.predeclare_toFullYul]
      have hFirst :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + first.fuel + second.fuel)
              initialStaticContext inLoop true first.toFullYul =
            some initialStaticContext := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          first_ih (extraFuel + second.fuel) inLoop
      have hSecond :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + first.fuel + second.fuel)
              initialStaticContext inLoop true second.toFullYul =
            some initialStaticContext := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          second_ih (extraFuel + first.fuel) inLoop
      simp [hFirst, hSecond]
  | ifThen cond body body_ih =>
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (body.fuel + 1) =
          (extraFuel + body.fuel) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        Expr.toFullYul_staticChecked]
      rw [body_ih extraFuel inLoop]
  | switch1 discr label branch defaultBranch branch_ih default_ih =>
      have hBranchFuel : 0 < branch.fuel := Stmt.fuel_pos branch
      have hDefaultFuel : 0 < defaultBranch.fuel := Stmt.fuel_pos defaultBranch
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (branch.fuel + defaultBranch.fuel + 1) =
          (extraFuel + branch.fuel + defaultBranch.fuel) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        SolidCoreYulCore.FullYul.switchHasBranch,
        SolidCoreYulCore.FullYul.switchCaseLabelsUnique,
        SolidCoreYulCore.FullYul.containsSwitchLabel,
        Expr.toFullYul_staticChecked]
      rw [show extraFuel + branch.fuel + defaultBranch.fuel =
          (extraFuel + branch.fuel + defaultBranch.fuel - 1) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkSwitchCasesFuel]
      have hBranch :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + branch.fuel + defaultBranch.fuel - 1)
              initialStaticContext inLoop true branch.toFullYul =
            some initialStaticContext := by
        have hBranchRaw :=
          branch_ih (extraFuel + defaultBranch.fuel - 1) inLoop
        rw [show (extraFuel + defaultBranch.fuel - 1) + branch.fuel =
            extraFuel + branch.fuel + defaultBranch.fuel - 1 by omega] at hBranchRaw
        exact hBranchRaw
      have hRest :
          SolidCoreYulCore.FullYul.checkSwitchCasesFuel
              (extraFuel + branch.fuel + defaultBranch.fuel - 1)
              initialStaticContext inLoop true [] =
            some () := by
        rw [show extraFuel + branch.fuel + defaultBranch.fuel - 1 =
            (extraFuel + branch.fuel + defaultBranch.fuel - 2) + 1 by omega]
        rfl
      have hDefault :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + branch.fuel + defaultBranch.fuel)
              initialStaticContext inLoop true defaultBranch.toFullYul =
            some initialStaticContext := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          default_ih (extraFuel + branch.fuel) inLoop
      rw [show extraFuel + branch.fuel + defaultBranch.fuel - 1 + 1 =
          extraFuel + branch.fuel + defaultBranch.fuel by omega]
      simp [hBranch, hRest, hDefault]
  | switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch hDistinct first_ih second_ih default_ih =>
      have hFirstFuel : 0 < firstBranch.fuel := Stmt.fuel_pos firstBranch
      have hSecondFuel : 0 < secondBranch.fuel := Stmt.fuel_pos secondBranch
      have hDefaultFuel : 0 < defaultBranch.fuel := Stmt.fuel_pos defaultBranch
      have hLabelNe :
          ¬ SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm secondLabel) =
            SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm firstLabel) := by
        intro h
        apply hDistinct
        injection h with hNorm
        exact hNorm.symm
      have hFirst :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel + 1)
              initialStaticContext inLoop true firstBranch.toFullYul =
            some initialStaticContext := by
        have hFirstRaw :=
          first_ih (extraFuel + secondBranch.fuel + defaultBranch.fuel + 1)
            inLoop
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFirstRaw
      have hSecond :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel)
              initialStaticContext inLoop true secondBranch.toFullYul =
            some initialStaticContext := by
        have hSecondRaw :=
          second_ih (extraFuel + firstBranch.fuel + defaultBranch.fuel) inLoop
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecondRaw
      have hEmpty :
          SolidCoreYulCore.FullYul.checkSwitchCasesFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel)
              initialStaticContext inLoop true [] =
            some () := by
        rw [show extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel =
            (extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel - 1) + 1 by omega]
        rfl
      have hRest :
          SolidCoreYulCore.FullYul.checkSwitchCasesFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel + 1)
              initialStaticContext inLoop true
              [ ( SolidCoreYulCore.FullYul.Value.word
                    (SolidCoreYulCore.norm secondLabel)
                , secondBranch.toFullYul ) ] =
            some () := by
        rw [show extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel + 1 =
            (extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel) + 1 by omega]
        simp [SolidCoreYulCore.FullYul.checkSwitchCasesFuel, hSecond, hEmpty]
      have hCases :
          SolidCoreYulCore.FullYul.checkSwitchCasesFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel + 2)
              initialStaticContext inLoop true
              [ ( SolidCoreYulCore.FullYul.Value.word
                    (SolidCoreYulCore.norm firstLabel)
                , firstBranch.toFullYul )
              , ( SolidCoreYulCore.FullYul.Value.word
                    (SolidCoreYulCore.norm secondLabel)
                , secondBranch.toFullYul ) ] =
            some () := by
        rw [show extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel + 2 =
            (extraFuel + firstBranch.fuel + secondBranch.fuel +
              defaultBranch.fuel + 1) + 1 by omega]
        simp [SolidCoreYulCore.FullYul.checkSwitchCasesFuel, hFirst, hRest,
          hSecond, hEmpty]
      have hDefault :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + firstBranch.fuel + secondBranch.fuel +
                defaultBranch.fuel + 2)
              initialStaticContext inLoop true defaultBranch.toFullYul =
            some initialStaticContext := by
        have hDefaultRaw :=
          default_ih (extraFuel + firstBranch.fuel + secondBranch.fuel + 2)
            inLoop
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hDefaultRaw
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 3) =
          (extraFuel + firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 2) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        SolidCoreYulCore.FullYul.switchHasBranch,
        SolidCoreYulCore.FullYul.switchCaseLabelsUnique,
        SolidCoreYulCore.FullYul.containsSwitchLabel,
        hLabelNe, Expr.toFullYul_staticChecked, hCases, hDefault]
  | forFalse body body_ih =>
      have hBody :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + body.fuel)
              initialStaticContext true true body.toFullYul =
            some initialStaticContext :=
        body_ih extraFuel true
      have hPre :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + body.fuel)
              initialStaticContext false true
              SolidCoreYulCore.FullYul.Stmt.skip =
            some initialStaticContext := by
        rw [show extraFuel + body.fuel =
            (extraFuel + body.fuel - 1) + 1 by
          have hFuel : 0 < body.fuel := Stmt.fuel_pos body
          omega]
        rfl
      have hPost :
          SolidCoreYulCore.FullYul.checkStmtFuel
              (extraFuel + body.fuel)
              initialStaticContext false true
              SolidCoreYulCore.FullYul.Stmt.skip =
            some initialStaticContext := hPre
      have hCond :
          SolidCoreYulCore.FullYul.checkExpr initialStaticContext
              (SolidCoreYulCore.FullYul.Expr.value
                (SolidCoreYulCore.FullYul.Value.word 0)) =
            true := by
        rfl
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (body.fuel + 1) =
          (extraFuel + body.fuel) + 1 by omega]
      simp [SolidCoreYulCore.FullYul.checkStmtFuel,
        SolidCoreYulCore.FullYul.stmtHasNoFunDefs,
        SolidCoreYulCore.FullYul.predeclareStmtFunctionSigs?,
        Stmt.predeclare_toFullYul, hPre, hPost, hBody, hCond]
  | forOnce body body_ih =>
      have hBody :
          SolidCoreYulCore.FullYul.checkStmtFuel
              ((extraFuel + 2) + body.fuel)
              initialStaticContext true true body.toFullYul =
            some initialStaticContext :=
        body_ih (extraFuel + 2) true
      have hLoop :=
        Stmt.singleIterationLoopFullYul_staticChecked_from
          extraFuel
          inLoop
          (SolidCoreYulCore.FullYul.Expr.value
            (SolidCoreYulCore.FullYul.Value.word 1))
          body
          (by rfl)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hBody)
      simpa [Stmt.fuel, Stmt.toFullYul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLoop
  | forIf cond body body_ih =>
      have hBody :
          SolidCoreYulCore.FullYul.checkStmtFuel
              ((extraFuel + 2) + body.fuel)
              initialStaticContext true true body.toFullYul =
            some initialStaticContext :=
        body_ih (extraFuel + 2) true
      have hLoop :=
        Stmt.singleIterationLoopFullYul_staticChecked_from
          extraFuel
          inLoop
          cond.toFullYul
          body
          (Expr.toFullYul_staticChecked initialStaticContext cond)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hBody)
      simpa [Stmt.fuel, Stmt.toFullYul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLoop

theorem Stmt.toFullYul_staticChecked_from
    (extraFuel : Nat) (stmt : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (extraFuel + stmt.fuel)
        initialStaticContext false true stmt.toFullYul =
      some initialStaticContext := by
  exact Stmt.toFullYul_staticChecked_from_inLoop extraFuel false stmt

theorem Stmt.toFullYul_staticChecked (stmt : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel stmt.fuel
        initialStaticContext false true stmt.toFullYul =
      some initialStaticContext := by
  simpa using Stmt.toFullYul_staticChecked_from 0 stmt

theorem Stmt.toFullYul_accepted_currentSolidCore_static
    (stmt : Stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      stmt.fuel initialStaticContext false true stmt.toFullYul
      initialStaticContext := by
  exact
    Stmt.toFullYul_accepted_currentSolidCore
      stmt
      (Stmt.toFullYul_staticChecked stmt)

theorem Stmt.boundedWhile_staticChecked_from_inLoop
    (extraFuel : Nat) (inLoop : Bool) (bound : Nat)
    (cond : Expr) (body : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (extraFuel + (Stmt.boundedWhile bound cond body).fuel)
        initialStaticContext inLoop true
        (Stmt.boundedWhile bound cond body).toFullYul =
      some initialStaticContext := by
  exact
    Stmt.toFullYul_staticChecked_from_inLoop extraFuel inLoop
      (Stmt.boundedWhile bound cond body)

theorem Stmt.boundedWhile_compilerEmittable
    (bound : Nat) (cond : Expr) (body : Stmt) :
    SolidCoreYulCore.FullYul.CompilerEmittableStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (Stmt.boundedWhile bound cond body).toFullYul := by
  exact
    Stmt.toFullYul_compilerEmittable
      (Stmt.boundedWhile bound cond body)

theorem Stmt.boundedWhile_accepted_currentSolidCore_static
    (bound : Nat) (cond : Expr) (body : Stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (Stmt.boundedWhile bound cond body).fuel
      initialStaticContext false true
      (Stmt.boundedWhile bound cond body).toFullYul
      initialStaticContext := by
  exact
    Stmt.toFullYul_accepted_currentSolidCore_static
      (Stmt.boundedWhile bound cond body)

theorem mvp_norm_norm (value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.norm value := by
  unfold SolidCoreYulCore.norm
  exact Nat.mod_mod value SolidCoreYulCore.wordModulus

theorem Stmt.localFrameFullYul_noFun
    (init : Expr) (tail : YulStmt)
    (funcs : SolidCoreYulCore.SymYul.FunctionEnv) :
    SolidCoreYulCore.SymYul.collectStmtFunctionDefs
        (Stmt.localFrameFullYul init tail) funcs =
      funcs := by
  rfl

theorem Stmt.localFrameBodyFullYul_noFun
    (init : Expr) {tail : YulStmt}
    (hTail :
      ∀ funcs : SolidCoreYulCore.SymYul.FunctionEnv,
        SolidCoreYulCore.SymYul.collectStmtFunctionDefs tail funcs =
          funcs)
    (funcs : SolidCoreYulCore.SymYul.FunctionEnv) :
    SolidCoreYulCore.SymYul.collectBlockFunctionDefs
        (Stmt.localFrameBodyFullYul init tail) funcs =
      funcs := by
  simp [SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
    SolidCoreYulCore.SymYul.collectBlockFunctionDefs, hTail]

set_option linter.unusedSimpArgs false in
theorem Stmt.collect_toFullYul
    (stmt : Stmt) (funcs : SolidCoreYulCore.SymYul.FunctionEnv) :
    SolidCoreYulCore.SymYul.collectStmtFunctionDefs stmt.toFullYul funcs =
      funcs := by
  induction stmt generalizing funcs with
  | skip =>
      rfl
  | discard _ =>
      rfl
  | returnExpr _ =>
      rfl
  | returnStateExpr _ =>
      rfl
  | revert =>
      rfl
  | store _ _ =>
      rfl
  | storeStateExpr _ _ =>
      rfl
  | loadReturn _ =>
      rfl
  | storeThenIfLoad _ _ body body_ih =>
      simp [Stmt.toFullYul, SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        body_ih]
  | seq first second first_ih second_ih =>
      simp [Stmt.toFullYul, SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        first_ih, second_ih]
  | ifThen _ body body_ih =>
      simp [Stmt.toFullYul, SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        body_ih]
  | switch1 _ _ branch defaultBranch branch_ih default_ih =>
      simp [Stmt.toFullYul, SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        branch_ih, default_ih]
  | switch2 _ _ firstBranch _ secondBranch defaultBranch _
      first_ih second_ih default_ih =>
      simp [Stmt.toFullYul, SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        first_ih, second_ih, default_ih]
  | forFalse body body_ih =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        body_ih]
  | forOnce body body_ih =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        body_ih]
  | forIf _ body body_ih =>
      simp [Stmt.toFullYul,
        SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
        body_ih]

theorem Stmt.switch1_toFullYul_correct_from
    (extraFuel : Nat) (state : State) (discr : Expr) (label : Word)
    (branch defaultBranch : Stmt)
    (hBranch :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + defaultBranch.fuel + branch.fuel)
          state.toConfig branch.toFullYul =
        (branch.eval state).toSymYulResults)
    (hDefault :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + branch.fuel + defaultBranch.fuel)
          state.toConfig defaultBranch.toFullYul =
        (defaultBranch.eval state).toSymYulResults) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.switch1 discr label branch defaultBranch).fuel)
        state.toConfig
        (Stmt.switch1 discr label branch defaultBranch).toFullYul =
      ((Stmt.switch1 discr label branch defaultBranch).eval state).toSymYulResults := by
  by_cases hEq : SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm label
  · have hKnownEq :
        SolidCoreYulCore.SymYul.knownEq?
          (SolidCoreYulCore.FullYul.Value.word discr.eval)
          (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm label)) =
            some true := by
      simp [SolidCoreYulCore.SymYul.knownEq?, hEq, mvp_norm_norm]
    simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hEq, if_true]
    rw [show extraFuel + (branch.fuel + defaultBranch.fuel + 1) =
        (extraFuel + branch.fuel + defaultBranch.fuel) + 1 by omega]
    simp [SolidCoreYulCore.SymYul.evalStmtFuel,
      SolidCoreYulCore.SymYul.switchBranches,
      SolidCoreYulCore.SymYul.switchFallthroughConstraints,
      SolidCoreYulCore.SymYul.addConstraints?,
      SolidCoreYulCore.SymYul.addConstraint?, hKnownEq,
      Expr.toFullYul_correct_env]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBranch
  · have hKnownEq :
        SolidCoreYulCore.SymYul.knownEq?
          (SolidCoreYulCore.FullYul.Value.word discr.eval)
          (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm label)) =
            some false := by
      simp [SolidCoreYulCore.SymYul.knownEq?, hEq, mvp_norm_norm]
    simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hEq, if_false]
    rw [show extraFuel + (branch.fuel + defaultBranch.fuel + 1) =
        (extraFuel + branch.fuel + defaultBranch.fuel) + 1 by omega]
    simp [SolidCoreYulCore.SymYul.evalStmtFuel,
      SolidCoreYulCore.SymYul.switchBranches,
      SolidCoreYulCore.SymYul.switchFallthroughConstraints,
      SolidCoreYulCore.SymYul.addConstraints?,
      SolidCoreYulCore.SymYul.addConstraint?, hKnownEq,
      Expr.toFullYul_correct_env]
    exact hDefault

theorem Stmt.switch2_toFullYul_correct_from
    (extraFuel : Nat) (state : State) (discr : Expr)
    (firstLabel : Word) (firstBranch : Stmt)
    (secondLabel : Word) (secondBranch defaultBranch : Stmt)
    (hDistinct :
      SolidCoreYulCore.norm firstLabel ≠ SolidCoreYulCore.norm secondLabel)
    (hFirst :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + secondBranch.fuel + defaultBranch.fuel + 2 +
            firstBranch.fuel)
          state.toConfig firstBranch.toFullYul =
        (firstBranch.eval state).toSymYulResults)
    (hSecond :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + firstBranch.fuel + defaultBranch.fuel + 2 +
            secondBranch.fuel)
          state.toConfig secondBranch.toFullYul =
        (secondBranch.eval state).toSymYulResults)
    (hDefault :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + firstBranch.fuel + secondBranch.fuel + 2 +
            defaultBranch.fuel)
          state.toConfig defaultBranch.toFullYul =
        (defaultBranch.eval state).toSymYulResults) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel +
          (Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
            defaultBranch hDistinct).fuel)
        state.toConfig
        (Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
          defaultBranch hDistinct).toFullYul =
      ((Stmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
        defaultBranch hDistinct).eval state).toSymYulResults := by
  by_cases hFirstEq :
      SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm firstLabel
  · have hKnownFirst :
        SolidCoreYulCore.SymYul.knownEq?
          (SolidCoreYulCore.FullYul.Value.word discr.eval)
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm firstLabel)) =
            some true := by
      simp [SolidCoreYulCore.SymYul.knownEq?, hFirstEq, mvp_norm_norm]
    have hSecondNe :
        ¬ SolidCoreYulCore.norm discr.eval =
          SolidCoreYulCore.norm secondLabel := by
      intro h
      exact hDistinct (hFirstEq.symm.trans h)
    have hKnownSecond :
        SolidCoreYulCore.SymYul.knownEq?
          (SolidCoreYulCore.FullYul.Value.word discr.eval)
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm secondLabel)) =
            some false := by
      simp [SolidCoreYulCore.SymYul.knownEq?, hSecondNe, mvp_norm_norm]
    simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hFirstEq, if_true]
    rw [show extraFuel + (firstBranch.fuel + secondBranch.fuel +
          defaultBranch.fuel + 3) =
        (extraFuel + firstBranch.fuel + secondBranch.fuel +
          defaultBranch.fuel + 2) + 1 by omega]
    simp [SolidCoreYulCore.SymYul.evalStmtFuel,
      SolidCoreYulCore.SymYul.switchBranches,
      SolidCoreYulCore.SymYul.switchFallthroughConstraints,
      SolidCoreYulCore.SymYul.addConstraints?,
      SolidCoreYulCore.SymYul.addConstraint?, hKnownFirst,
      Expr.toFullYul_correct_env]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFirst
  · by_cases hSecondEq :
        SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm secondLabel
    · have hKnownFirst :
          SolidCoreYulCore.SymYul.knownEq?
            (SolidCoreYulCore.FullYul.Value.word discr.eval)
            (SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm firstLabel)) =
              some false := by
        simp [SolidCoreYulCore.SymYul.knownEq?, hFirstEq, mvp_norm_norm]
      have hKnownSecond :
          SolidCoreYulCore.SymYul.knownEq?
            (SolidCoreYulCore.FullYul.Value.word discr.eval)
            (SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm secondLabel)) =
              some true := by
        simp [SolidCoreYulCore.SymYul.knownEq?, hSecondEq, mvp_norm_norm]
      have hSecondFirstNe :
          ¬ SolidCoreYulCore.norm secondLabel =
            SolidCoreYulCore.norm firstLabel := by
        intro h
        exact hDistinct h.symm
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hSecondFirstNe,
        if_false, hSecondEq, if_true]
      rw [show extraFuel + (firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 3) =
          (extraFuel + firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 2) + 1 by omega]
      simp [SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.switchBranches,
        SolidCoreYulCore.SymYul.switchFallthroughConstraints,
        SolidCoreYulCore.SymYul.addConstraints?,
        SolidCoreYulCore.SymYul.addConstraint?, hKnownFirst, hKnownSecond,
        Expr.toFullYul_correct_env]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSecond
    · have hKnownFirst :
          SolidCoreYulCore.SymYul.knownEq?
            (SolidCoreYulCore.FullYul.Value.word discr.eval)
            (SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm firstLabel)) =
              some false := by
        simp [SolidCoreYulCore.SymYul.knownEq?, hFirstEq, mvp_norm_norm]
      have hKnownSecond :
          SolidCoreYulCore.SymYul.knownEq?
            (SolidCoreYulCore.FullYul.Value.word discr.eval)
            (SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm secondLabel)) =
              some false := by
        simp [SolidCoreYulCore.SymYul.knownEq?, hSecondEq, mvp_norm_norm]
      have hSecondFirstNe :
          ¬ SolidCoreYulCore.norm secondLabel =
            SolidCoreYulCore.norm firstLabel := by
        intro h
        exact hDistinct h.symm
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hFirstEq, if_false,
        hSecondEq]
      rw [show extraFuel + (firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 3) =
          (extraFuel + firstBranch.fuel + secondBranch.fuel +
            defaultBranch.fuel + 2) + 1 by omega]
      simp [SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.switchBranches,
        SolidCoreYulCore.SymYul.switchFallthroughConstraints,
        SolidCoreYulCore.SymYul.addConstraints?,
        SolidCoreYulCore.SymYul.addConstraint?, hKnownFirst, hKnownSecond,
        Expr.toFullYul_correct_env]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hDefault

theorem Stmt.evalStmtFuel_forFalseFullYul_from
    (fuel : Nat) (hFuel : 0 < fuel) (state : State) (body : YulStmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (fuel + 1)
        state.toConfig
        (SolidCoreYulCore.FullYul.Stmt.forLoop
          SolidCoreYulCore.FullYul.Stmt.skip
          (SolidCoreYulCore.FullYul.Expr.value
            (SolidCoreYulCore.FullYul.Value.word 0))
          SolidCoreYulCore.FullYul.Stmt.skip
          body) =
      (Result.normal state).toSymYulResults := by
  cases fuel with
  | zero => cases hFuel
  | succ fuel =>
      simp [State.toConfig, State.toStorageState,
        Core.Storage.State.toConfig,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.knownZero?,
        SolidCoreYulCore.SymYul.normalResult,
        SolidCoreYulCore.SymYul.restoreBlockConfig,
        SolidCoreYulCore.FullYul.restoreOuter,
        SolidCoreYulCore.FullYul.lookup?,
        Result.toSymYulResults,
        SolidCoreYulCore.norm, SolidCoreYulCore.wordModulus]

theorem State.restoreBlockConfig_toConfig (outer inner : State) :
    SolidCoreYulCore.SymYul.restoreBlockConfig
        outer.toConfig inner.toConfig =
      some inner.toConfig := by
  simp [State.toConfig, State.toStorageState, Core.Storage.State.toConfig,
    SolidCoreYulCore.SymYul.restoreBlockConfig,
    SolidCoreYulCore.FullYul.restoreOuter,
    SolidCoreYulCore.FullYul.lookup?]

theorem Stmt.evalStmtFuel_loopBodyConfig_from
    (extraFuel : Nat) (state : State) (body : Stmt)
    {results : List SymResult}
    (hBody :
      SolidCoreYulCore.SymYul.evalStmtFuel
          ((extraFuel + 1) + body.fuel)
          state.toConfig body.toFullYul =
        results) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        ((extraFuel + 1) + body.fuel)
        { pc := state.toConfig.pc
          env := state.toConfig.env
          evm := state.toConfig.evm
          funcs :=
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs
              SolidCoreYulCore.FullYul.Stmt.break
              state.toConfig.funcs
          object? := state.toConfig.object? }
        body.toFullYul =
      results := by
  simpa [State.toConfig, State.toStorageState, Core.Storage.State.toConfig,
    SolidCoreYulCore.SymYul.collectStmtFunctionDefs] using hBody

theorem Stmt.evalStmtFuel_singleIterationLoopFullYul_zero_from
    (extraFuel : Nat) (state : State) (cond : Expr) (body : Stmt)
    (hCond : SolidCoreYulCore.norm cond.eval = 0) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.forIf cond body).fuel)
        state.toConfig
        (Stmt.forIf cond body).toFullYul =
      ((Stmt.forIf cond body).eval state).toSymYulResults := by
  have hZero : cond.eval % SolidCoreYulCore.wordModulus = 0 := by
    simpa [SolidCoreYulCore.norm] using hCond
  have hKnownZero :
      SolidCoreYulCore.SymYul.knownZero?
          (SolidCoreYulCore.FullYul.Value.word cond.eval) =
        some true := by
    simp [SolidCoreYulCore.SymYul.knownZero?,
      SolidCoreYulCore.norm, hZero]
  have hRestore :
      SolidCoreYulCore.SymYul.restoreBlockConfig
          state.toConfig state.toConfig =
        some state.toConfig :=
    State.restoreBlockConfig_toConfig state state
  simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_true]
  rw [show extraFuel + (body.fuel + 4) =
      (extraFuel + body.fuel + 3) + 1 by omega]
  rw [show extraFuel + body.fuel + 3 =
      (extraFuel + body.fuel + 2) + 1 by omega]
  simp [Stmt.bodyThenBreakFullYul,
    SolidCoreYulCore.SymYul.evalStmtFuel,
    SolidCoreYulCore.SymYul.evalForFuel,
    SolidCoreYulCore.SymYul.branchOn,
    SolidCoreYulCore.SymYul.normalResult,
    Expr.toFullYul_correct_env, hRestore, hKnownZero,
    Result.toSymYulResults,
    Nat.add_assoc]

theorem Stmt.evalStmtFuel_singleIterationLoopFullYul_nonzero_from
    (extraFuel : Nat) (state : State) (cond : Expr) (body : Stmt)
    (hCond : ¬ SolidCoreYulCore.norm cond.eval = 0)
    (hBody :
      SolidCoreYulCore.SymYul.evalStmtFuel
          ((extraFuel + 1) + body.fuel)
          state.toConfig body.toFullYul =
        (body.eval state).toSymYulResults) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.forIf cond body).fuel)
        state.toConfig
        (Stmt.forIf cond body).toFullYul =
      ((Stmt.forIf cond body).eval state).toSymYulResults := by
  have hNonzero : cond.eval % SolidCoreYulCore.wordModulus ≠ 0 := by
    simpa [SolidCoreYulCore.norm] using hCond
  have hKnownNonzero :
      SolidCoreYulCore.SymYul.knownZero?
          (SolidCoreYulCore.FullYul.Value.word cond.eval) =
        some false := by
    simp [SolidCoreYulCore.SymYul.knownZero?,
      SolidCoreYulCore.norm, hNonzero]
  cases hEval : body.eval state with
  | normal state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [SolidCoreYulCore.SymYul.normalResult state'.toConfig] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [SolidCoreYulCore.SymYul.normalResult state'.toConfig] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_false,
        hEval, Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hBreak :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              state'.toConfig
              SolidCoreYulCore.FullYul.Stmt.break =
            [{ flow := SolidCoreYulCore.FullYul.Flow.broke,
               config := state'.toConfig }] := by
        rw [show extraFuel + (1 + body.fuel) =
            (extraFuel + body.fuel) + 1 by omega]
        rfl
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig state'.toConfig =
            some state'.toConfig :=
        State.restoreBlockConfig_toConfig state state'
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        Expr.toFullYul_correct_env, hKnownNonzero, hRestore, hBreak,
        Stmt.collect_toFullYul, hBodySeqConfig,
        Nat.add_assoc]
  | returned state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.left,
               config := state'.toConfig }] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.left,
               config := state'.toConfig }] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_false,
        hEval, Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig state'.toConfig =
            some state'.toConfig :=
        State.restoreBlockConfig_toConfig state state'
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        Expr.toFullYul_correct_env, hKnownNonzero, hRestore,
        Stmt.collect_toFullYul, hBodySeqConfig,
        Nat.add_assoc]
  | reverted state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
               config := Result.revertConfig state' }] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
               config := Result.revertConfig state' }] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_false,
        hEval, Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig (Result.revertConfig state') =
            some (Result.revertConfig state') := by
        simp [Result.revertConfig, State.toConfig, State.toStorageState,
          Core.Storage.State.toConfig,
          SolidCoreYulCore.SymYul.restoreBlockConfig,
          SolidCoreYulCore.FullYul.restoreOuter,
          SolidCoreYulCore.FullYul.lookup?]
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        Expr.toFullYul_correct_env, hKnownNonzero, hRestore,
        Stmt.collect_toFullYul, hBodySeqConfig,
        Nat.add_assoc]

theorem Stmt.evalStmtFuel_singleIterationLoopFullYul_one_from
    (extraFuel : Nat) (state : State) (body : Stmt)
    (hBody :
      SolidCoreYulCore.SymYul.evalStmtFuel
          ((extraFuel + 1) + body.fuel)
          state.toConfig body.toFullYul =
        (body.eval state).toSymYulResults) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.forOnce body).fuel)
        state.toConfig
        (Stmt.forOnce body).toFullYul =
      ((Stmt.forOnce body).eval state).toSymYulResults := by
  have hNonzero : ¬ SolidCoreYulCore.norm (Expr.lit 1).eval = 0 := by
    decide
  have hKnownNonzero :
      SolidCoreYulCore.SymYul.knownZero?
          (SolidCoreYulCore.FullYul.Value.word (Expr.lit 1).eval) =
        some false := by
    simp [SolidCoreYulCore.SymYul.knownZero?,
      Expr.eval, SolidCoreYulCore.norm, SolidCoreYulCore.wordModulus]
  cases hEval : body.eval state with
  | normal state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [SolidCoreYulCore.SymYul.normalResult state'.toConfig] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [SolidCoreYulCore.SymYul.normalResult state'.toConfig] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hEval,
        Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hBreak :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              state'.toConfig
              SolidCoreYulCore.FullYul.Stmt.break =
            [{ flow := SolidCoreYulCore.FullYul.Flow.broke,
               config := state'.toConfig }] := by
        rw [show extraFuel + (1 + body.fuel) =
            (extraFuel + body.fuel) + 1 by omega]
        rfl
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig state'.toConfig =
            some state'.toConfig :=
        State.restoreBlockConfig_toConfig state state'
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.knownZero?,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        hRestore, hBreak,
        Stmt.collect_toFullYul, hBodySeqConfig,
        SolidCoreYulCore.norm, SolidCoreYulCore.wordModulus,
        Nat.add_assoc]
  | returned state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.left,
               config := state'.toConfig }] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.left,
               config := state'.toConfig }] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hEval,
        Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig state'.toConfig =
            some state'.toConfig :=
        State.restoreBlockConfig_toConfig state state'
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.knownZero?,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        hRestore,
        Stmt.collect_toFullYul, hBodySeqConfig,
        SolidCoreYulCore.norm, SolidCoreYulCore.wordModulus,
        Nat.add_assoc]
  | reverted state' =>
      have hBody' :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
               config := Result.revertConfig state' }] := by
        simpa [hEval, Result.toSymYulResults] using hBody
      have hBodySeqConfig :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + (1 + body.fuel))
              { pc := state.toConfig.pc
                env := state.toConfig.env
                evm := state.toConfig.evm
                funcs :=
                  SolidCoreYulCore.SymYul.collectStmtFunctionDefs
                    SolidCoreYulCore.FullYul.Stmt.break
                    state.toConfig.funcs
                object? := state.toConfig.object? }
              body.toFullYul =
            [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
               config := Result.revertConfig state' }] :=
        by
          simpa [Nat.add_assoc] using
            Stmt.evalStmtFuel_loopBodyConfig_from extraFuel state body hBody'
      simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hEval,
        Result.toSymYulResults]
      rw [show extraFuel + (body.fuel + 4) =
          (extraFuel + body.fuel + 3) + 1 by omega]
      rw [show extraFuel + body.fuel + 3 =
          (extraFuel + body.fuel + 2) + 1 by omega]
      rw [show extraFuel + body.fuel + 2 =
          ((extraFuel + 1) + body.fuel) + 1 by omega]
      have hRestore :
          SolidCoreYulCore.SymYul.restoreBlockConfig
              state.toConfig (Result.revertConfig state') =
            some (Result.revertConfig state') := by
        simp [Result.revertConfig, State.toConfig, State.toStorageState,
          Core.Storage.State.toConfig,
          SolidCoreYulCore.SymYul.restoreBlockConfig,
          SolidCoreYulCore.FullYul.restoreOuter,
          SolidCoreYulCore.FullYul.lookup?]
      simp [Stmt.bodyThenBreakFullYul,
        SolidCoreYulCore.SymYul.evalStmtFuel,
        SolidCoreYulCore.SymYul.evalForFuel,
        SolidCoreYulCore.SymYul.evalExpr,
        SolidCoreYulCore.SymYul.branchOn,
        SolidCoreYulCore.SymYul.knownZero?,
        SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult,
        hRestore,
        Stmt.collect_toFullYul, hBodySeqConfig,
        SolidCoreYulCore.norm, SolidCoreYulCore.wordModulus,
        Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem Stmt.evalStmtFuel_store_from
    (extraFuel : Nat) (state : State) (slot value : Expr) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.store slot value).fuel)
        state.toConfig
        (Stmt.store slot value).toFullYul =
      ((Stmt.store slot value).eval state).toSymYulResults := by
  cases extraFuel <;>
  simp [Stmt.fuel, Stmt.toFullYul, Stmt.sstoreFullYul, Stmt.eval,
    State.toConfig, State.toStorageState, Core.Storage.State.toConfig,
    State.store, State.storeValue,
    SolidCoreYulCore.SymYul.evalStmtFuel,
    SolidCoreYulCore.SymYul.evalExpr,
    SolidCoreYulCore.SymYul.evalExprs,
    SolidCoreYulCore.SymYul.resultAfterExpr,
    SolidCoreYulCore.SymYul.normalResult,
    SolidCoreYulCore.SymYul.bindNormal,
    SolidCoreYulCore.FullYul.evalEvmBuiltin_sstore_values,
    SolidCoreYulCore.FullYul.EvmState.empty,
    SolidCoreYulCore.FullYul.returnUnit,
    SolidCoreYulCore.FullYul.returnWord,
    storageLookup?, storageWrite, storageAccountZero,
    SolidCoreYulCore.FullYul.lookupAccountValueMap?,
    SolidCoreYulCore.FullYul.lookupAccountValueEntries?,
    SolidCoreYulCore.FullYul.writeAccountValueMap,
    SolidCoreYulCore.FullYul.lookupValueMap?,
    SolidCoreYulCore.FullYul.writeValueMap,
    SolidCoreYulCore.FullYul.assign?,
    SolidCoreYulCore.FullYul.lookup?,
    Expr.toFullYul_correct_env, Result.toSymYulResults]

set_option linter.unusedSimpArgs false in
theorem Stmt.evalStmtFuel_storeStateExpr_from
    (extraFuel : Nat) (state : State) (slot : Expr) (value : StateExpr) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.storeStateExpr slot value).fuel)
        state.toConfig
        (Stmt.storeStateExpr slot value).toFullYul =
      ((Stmt.storeStateExpr slot value).eval state).toSymYulResults := by
  have hValue := StateExpr.toFullYul_correct_env state value
  have hValueRaw :
      SolidCoreYulCore.SymYul.evalExpr
          { pc := SolidCoreYulCore.SymYul.Config.empty.pc
            env := [(returnName, state.returnValue)]
            evm := { storage := state.storage }
            funcs := SolidCoreYulCore.SymYul.Config.empty.funcs
            object? := SolidCoreYulCore.SymYul.Config.empty.object? }
          value.toFullYul =
        some
          (StateExpr.eval state value,
            { pc := SolidCoreYulCore.SymYul.Config.empty.pc
              env := [(returnName, state.returnValue)]
              evm := { storage := state.storage }
              funcs := SolidCoreYulCore.SymYul.Config.empty.funcs
              object? := SolidCoreYulCore.SymYul.Config.empty.object? }) := by
    simpa [State.toConfig, State.toStorageState,
      Core.Storage.State.toConfig, returnName] using hValue
  cases extraFuel <;>
  simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval,
    State.toConfig, State.toStorageState, Core.Storage.State.toConfig,
    State.storeValue,
    SolidCoreYulCore.SymYul.evalStmtFuel,
    SolidCoreYulCore.SymYul.evalExpr,
    SolidCoreYulCore.SymYul.evalExprs,
    SolidCoreYulCore.SymYul.resultAfterExpr,
    SolidCoreYulCore.SymYul.normalResult,
    SolidCoreYulCore.SymYul.bindNormal,
    SolidCoreYulCore.FullYul.evalEvmBuiltin_sstore_values,
    SolidCoreYulCore.FullYul.EvmState.empty,
    SolidCoreYulCore.FullYul.returnUnit,
    SolidCoreYulCore.FullYul.returnWord,
    storageLookup?, storageWrite, storageAccountZero,
    SolidCoreYulCore.FullYul.lookupAccountValueMap?,
    SolidCoreYulCore.FullYul.lookupAccountValueEntries?,
    SolidCoreYulCore.FullYul.writeAccountValueMap,
    SolidCoreYulCore.FullYul.lookupValueMap?,
    SolidCoreYulCore.FullYul.writeValueMap,
    SolidCoreYulCore.FullYul.assign?,
    SolidCoreYulCore.FullYul.lookup?,
    Expr.toFullYul_correct_env, hValueRaw, Result.toSymYulResults]

theorem Stmt.evalExpr_sload_after_store
    (state : State) (slot value : Expr) :
    SolidCoreYulCore.SymYul.evalExpr
        (state.store slot value).toConfig
        (Stmt.sloadFullYul slot) =
      some
        ( SolidCoreYulCore.FullYul.Value.word value.eval
        , (state.store slot value).toConfig ) := by
  have hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (state.store slot value).storage storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word slot.eval) =
        some (SolidCoreYulCore.FullYul.Value.word value.eval) := by
    simpa [State.store, State.storeValue, storageWrite, storageAccountZero]
      using
        SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same
          state.storage storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word slot.eval)
          (SolidCoreYulCore.FullYul.Value.word value.eval)
  have hEvalRaw :
      SolidCoreYulCore.FullYul.evalEvmBuiltin
          SolidCoreYulCore.Evm.Builtin.sload
          [SolidCoreYulCore.FullYul.Value.word slot.eval]
          ({ storage := (state.store slot value).storage } :
            SolidCoreYulCore.FullYul.EvmState) =
        some
          ( SolidCoreYulCore.FullYul.Value.word value.eval
          , ({ storage := (state.store slot value).storage } :
              SolidCoreYulCore.FullYul.EvmState) ) := by
    simpa [SolidCoreYulCore.FullYul.EvmState.empty] using
      evalEvmBuiltin_sload_accountZero_present
        (state.store slot value).storage
        (SolidCoreYulCore.FullYul.Value.word slot.eval)
        (SolidCoreYulCore.FullYul.Value.word value.eval)
        hLookup
  have hEvalEvm :
      SolidCoreYulCore.FullYul.evalEvmBuiltin
          SolidCoreYulCore.Evm.Builtin.sload
          [SolidCoreYulCore.FullYul.Value.word slot.eval]
          (state.store slot value).toConfig.evm =
        some
          ( SolidCoreYulCore.FullYul.Value.word value.eval
          , (state.store slot value).toConfig.evm ) := by
    simpa [State.toConfig, State.toStorageState, Core.Storage.State.toConfig]
      using hEvalRaw
  have hSlot :=
    Expr.toFullYul_correct_env (state.store slot value).toConfig slot
  simp [SolidCoreYulCore.SymYul.evalExpr,
    SolidCoreYulCore.SymYul.evalExprs, hSlot, hEvalEvm]

theorem Stmt.evalStmtFuel_ifSloadAfterStore_from
    (extraFuel : Nat) (state : State) (slot value : Expr) (body : Stmt)
    (hBody :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (extraFuel + body.fuel)
          (state.store slot value).toConfig body.toFullYul =
        (body.eval (state.store slot value)).toSymYulResults) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + body.fuel + 1)
        (state.store slot value).toConfig
        (SolidCoreYulCore.FullYul.Stmt.ifThen
          (Stmt.sloadFullYul slot)
          body.toFullYul) =
      (if SolidCoreYulCore.norm value.eval = 0 then
        Result.normal (state.store slot value)
       else
        body.eval (state.store slot value)).toSymYulResults := by
  have hEvalExpr :=
    Stmt.evalExpr_sload_after_store state slot value
  rw [show extraFuel + body.fuel + 1 =
      (extraFuel + body.fuel) + 1 by omega]
  by_cases hCond : SolidCoreYulCore.norm value.eval = 0
  · simp [SolidCoreYulCore.SymYul.evalStmtFuel,
      SolidCoreYulCore.SymYul.branchOn,
      SolidCoreYulCore.SymYul.knownZero?,
      SolidCoreYulCore.SymYul.normalResult,
      hEvalExpr, hCond, Result.toSymYulResults]
  · simp [SolidCoreYulCore.SymYul.evalStmtFuel,
      SolidCoreYulCore.SymYul.branchOn,
      SolidCoreYulCore.SymYul.knownZero?,
      hEvalExpr, hCond, hBody]

theorem Stmt.localFrameFullYul_wordReturn_correct_from
    (checkFuel : Nat) (state : State) (init : Expr) {tail : YulStmt}
    (localValue returnValue : Word)
    (hNoFun :
      ∀ funcs,
        SolidCoreYulCore.SymYul.collectStmtFunctionDefs tail funcs = funcs)
    (hTail :
      SolidCoreYulCore.SymYul.evalStmtFuel
          checkFuel
          (Stmt.localFrameEntryConfig state init.eval)
          tail =
        [ { flow := SolidCoreYulCore.FullYul.Flow.left
            config :=
              Stmt.localFrameTailReturnConfig
                state localValue returnValue } ]) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (checkFuel + 3) state.toConfig
        (Stmt.localFrameFullYul init tail) =
      (Result.returned (state.withWordReturn returnValue)).toSymYulResults := by
  cases checkFuel with
  | zero =>
      simp [SolidCoreYulCore.SymYul.evalStmtFuel] at hTail
  | succ checkFuel =>
  have hTail' :
      SolidCoreYulCore.SymYul.evalStmtFuel
          (Nat.succ checkFuel)
          { SolidCoreYulCore.SymYul.Config.empty with
            env :=
              [ (1, SolidCoreYulCore.FullYul.Value.word init.eval)
              , (0, state.returnValue) ]
            evm :=
              { SolidCoreYulCore.FullYul.EvmState.empty with
                storage := state.storage } }
          tail =
        [ { flow := SolidCoreYulCore.FullYul.Flow.left
            config :=
              { SolidCoreYulCore.SymYul.Config.empty with
                env :=
                  [ (1, SolidCoreYulCore.FullYul.Value.word localValue)
                  , (0, SolidCoreYulCore.FullYul.Value.word returnValue) ]
                evm :=
                  { SolidCoreYulCore.FullYul.EvmState.empty with
                    storage := state.storage } } } ] := by
    simpa [Stmt.localFrameEntryConfig,
      Stmt.localFrameTailReturnConfig, State.toConfig, State.toStorageState,
      Core.Storage.State.toConfig, returnName, localName] using hTail
  simp [State.toConfig, State.toStorageState,
    State.withReturn, State.withWordReturn,
    Core.Storage.State.toConfig, returnName, localName,
    SolidCoreYulCore.SymYul.evalStmtFuel,
    SolidCoreYulCore.SymYul.evalBlockFuel,
    SolidCoreYulCore.SymYul.bindNormal,
    SolidCoreYulCore.SymYul.withRestoredConfig,
    SolidCoreYulCore.SymYul.restoreBlockConfig,
    SolidCoreYulCore.SymYul.normalResult,
    SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
    SolidCoreYulCore.SymYul.collectBlockFunctionDefs,
    SolidCoreYulCore.FullYul.declare?,
    SolidCoreYulCore.FullYul.lookup?,
    SolidCoreYulCore.FullYul.restoreOuter,
    Expr.toFullYul_correct_env, Result.toSymYulResults, hNoFun, hTail']

set_option linter.unusedSimpArgs false in
theorem Stmt.toFullYul_correct_from
    (extraFuel : Nat) (state : State) (stmt : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + stmt.fuel)
        state.toConfig stmt.toFullYul =
      (stmt.eval state).toSymYulResults := by
  induction stmt generalizing state extraFuel with
  | skip =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval, Result.toSymYulResults,
          State.toConfig, SolidCoreYulCore.SymYul.evalStmtFuel]
  | discard e =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval, Result.toSymYulResults,
          State.toConfig, SolidCoreYulCore.SymYul.evalStmtFuel]
  | returnExpr e =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval, Result.toSymYulResults,
          State.toConfig, State.toStorageState,
          State.withReturn, State.withWordReturn,
          Core.Storage.State.toConfig,
          SolidCoreYulCore.SymYul.evalStmtFuel,
          SolidCoreYulCore.SymYul.bindNormal,
          SolidCoreYulCore.SymYul.normalResult,
          SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
          SolidCoreYulCore.FullYul.assign?,
          Expr.toFullYul_correct_env]
  | returnStateExpr expr =>
      have hExpr := StateExpr.toFullYul_correct_env state expr
      have hConfigEta :
          { pc := state.toConfig.pc
            env := state.toConfig.env
            evm := state.toConfig.evm
            funcs := state.toConfig.funcs
            object? := state.toConfig.object? } = state.toConfig := by
        cases state.toConfig
        rfl
      cases extraFuel with
      | zero =>
          simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval,
            Result.toSymYulResults,
            SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs]
          rw [hConfigEta, hExpr]
          simp [State.toConfig, State.toStorageState,
            State.withReturn, Core.Storage.State.toConfig,
            SolidCoreYulCore.SymYul.normalResult,
            SolidCoreYulCore.FullYul.assign?]
      | succ extraFuel =>
          simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval,
            Result.toSymYulResults,
            SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs]
          rw [hConfigEta, hExpr]
          simp [State.toConfig, State.toStorageState,
            State.withReturn, Core.Storage.State.toConfig,
            SolidCoreYulCore.SymYul.normalResult,
            SolidCoreYulCore.FullYul.assign?]
  | revert =>
      cases extraFuel <;>
        simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval,
          Stmt.revertZeroFullYul, Result.toSymYulResults,
          Result.revertConfig, State.toConfig, State.toStorageState,
          Core.Storage.State.toConfig,
          SolidCoreYulCore.SymYul.evalStmtFuel,
          SolidCoreYulCore.SymYul.evalExpr,
          SolidCoreYulCore.SymYul.evalExprs,
          SolidCoreYulCore.SymYul.resultAfterExpr,
          SolidCoreYulCore.FullYul.evalEvmBuiltin_revert_words,
          SolidCoreYulCore.FullYul.returnUnit,
          SolidCoreYulCore.FullYul.returnWord,
          SolidCoreYulCore.FullYul.EvmState.empty,
          SolidCoreYulCore.FullYul.haltWith,
          SolidCoreYulCore.FullYul.expandMemory,
          SolidCoreYulCore.memorySizeAfter,
          SolidCoreYulCore.FullYul.SymbolicBytes.memorySnapshot]
  | store slot value =>
      exact Stmt.evalStmtFuel_store_from extraFuel state slot value
  | storeStateExpr slot value =>
      exact Stmt.evalStmtFuel_storeStateExpr_from extraFuel state slot value
  | loadReturn slot =>
      cases hLookup :
          SolidCoreYulCore.FullYul.lookupAccountValueMap?
            state.storage storageAccountZero
            (SolidCoreYulCore.FullYul.Value.word slot.eval) with
      | none =>
          have hLoaded :
              state.load slot =
                SolidCoreYulCore.FullYul.Value.storageWord
                  storageAccountZero
                  (SolidCoreYulCore.FullYul.Value.word slot.eval) := by
            simp [State.load, storageLookup?, hLookup]
          have hEval :
              SolidCoreYulCore.FullYul.evalEvmBuiltin
                  SolidCoreYulCore.Evm.Builtin.sload
                  [SolidCoreYulCore.FullYul.Value.word slot.eval]
                  ({ storage := state.storage } :
                    SolidCoreYulCore.FullYul.EvmState) =
                some
                  ( SolidCoreYulCore.FullYul.Value.storageWord
                      storageAccountZero
                      (SolidCoreYulCore.FullYul.Value.word slot.eval)
                  , ({ storage := state.storage } :
                      SolidCoreYulCore.FullYul.EvmState) ) := by
            simpa [SolidCoreYulCore.FullYul.EvmState.empty] using
              evalEvmBuiltin_sload_accountZero_missing
                state.storage
                (SolidCoreYulCore.FullYul.Value.word slot.eval)
                hLookup
          cases extraFuel <;>
          simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval, State.toConfig,
            State.toStorageState, Core.Storage.State.toConfig,
            State.withReturn,
            hLoaded, hLookup, hEval,
            SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.evalExpr,
            SolidCoreYulCore.SymYul.evalExprs,
            SolidCoreYulCore.SymYul.resultAfterExpr,
            SolidCoreYulCore.SymYul.normalResult,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
            SolidCoreYulCore.FullYul.evalEvmBuiltin_sload_missing,
            evalEvmBuiltin_sload_accountZero_missing,
            SolidCoreYulCore.FullYul.EvmState.empty,
            SolidCoreYulCore.FullYul.returnWord,
            storageLookup?, storageAccountZero,
            SolidCoreYulCore.FullYul.lookupAccountValueMap?,
            SolidCoreYulCore.FullYul.lookupAccountValueEntries?,
            SolidCoreYulCore.FullYul.assign?,
            SolidCoreYulCore.FullYul.lookup?,
            Expr.toFullYul_correct_env, Result.toSymYulResults]
      | some loaded =>
          have hLoaded : state.load slot = loaded := by
            simp [State.load, storageLookup?, hLookup]
          have hEval :
              SolidCoreYulCore.FullYul.evalEvmBuiltin
                  SolidCoreYulCore.Evm.Builtin.sload
                  [SolidCoreYulCore.FullYul.Value.word slot.eval]
                  ({ storage := state.storage } :
                    SolidCoreYulCore.FullYul.EvmState) =
                some
                  ( loaded
                  , ({ storage := state.storage } :
                      SolidCoreYulCore.FullYul.EvmState) ) := by
            simpa [SolidCoreYulCore.FullYul.EvmState.empty] using
              evalEvmBuiltin_sload_accountZero_present
                state.storage
                (SolidCoreYulCore.FullYul.Value.word slot.eval)
                loaded hLookup
          cases extraFuel <;>
          simp [Stmt.fuel, Stmt.toFullYul, Stmt.eval, State.toConfig,
            State.toStorageState, Core.Storage.State.toConfig,
            State.withReturn,
            hLoaded, hLookup, hEval,
            SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.evalExpr,
            SolidCoreYulCore.SymYul.evalExprs,
            SolidCoreYulCore.SymYul.resultAfterExpr,
            SolidCoreYulCore.SymYul.normalResult,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
            SolidCoreYulCore.FullYul.evalEvmBuiltin_sload_present,
            evalEvmBuiltin_sload_accountZero_present,
            SolidCoreYulCore.FullYul.EvmState.empty,
            SolidCoreYulCore.FullYul.returnWord,
            storageLookup?, storageAccountZero,
            SolidCoreYulCore.FullYul.lookupAccountValueMap?,
            SolidCoreYulCore.FullYul.lookupAccountValueEntries?,
            SolidCoreYulCore.FullYul.assign?,
            SolidCoreYulCore.FullYul.lookup?,
            Expr.toFullYul_correct_env, Result.toSymYulResults]
  | storeThenIfLoad slot value body body_ih =>
      have hStore :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + body.fuel + 2)
              state.toConfig
              (Stmt.sstoreFullYul slot value) =
            [SolidCoreYulCore.SymYul.normalResult
              (state.store slot value).toConfig] := by
        have hRaw :=
          Stmt.evalStmtFuel_store_from
            (extraFuel + body.fuel + 1) state slot value
        rw [show extraFuel + body.fuel + 2 =
            (extraFuel + body.fuel + 1) + (Stmt.store slot value).fuel by
              simp [Stmt.fuel]]
        simpa [Stmt.toFullYul, Stmt.eval, Result.toSymYulResults] using
          hRaw
      have hBody :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              (state.store slot value).toConfig body.toFullYul =
            (body.eval (state.store slot value)).toSymYulResults :=
        body_ih (extraFuel + 1) (state.store slot value)
      have hIf :
          SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + body.fuel + 2)
              (state.store slot value).toConfig
              (SolidCoreYulCore.FullYul.Stmt.ifThen
                (Stmt.sloadFullYul slot)
                body.toFullYul) =
            ((Stmt.storeThenIfLoad slot value body).eval state).toSymYulResults := by
        have hRaw :=
          Stmt.evalStmtFuel_ifSloadAfterStore_from
            (extraFuel + 1) state slot value body
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hBody)
        rw [show extraFuel + body.fuel + 2 =
            (extraFuel + 1) + body.fuel + 1 by omega]
        simpa [Stmt.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hRaw
      simp only [Stmt.fuel, Stmt.toFullYul]
      rw [show extraFuel + (body.fuel + 3) =
          (extraFuel + body.fuel + 2) + 1 by omega]
      change
        SolidCoreYulCore.SymYul.bindNormal
          (SolidCoreYulCore.SymYul.evalStmtFuel
            (extraFuel + body.fuel + 2)
            state.toConfig
            (Stmt.sstoreFullYul slot value))
          (fun config' =>
            SolidCoreYulCore.SymYul.evalStmtFuel
              (extraFuel + body.fuel + 2)
              config'
              (SolidCoreYulCore.FullYul.Stmt.ifThen
                (Stmt.sloadFullYul slot)
                body.toFullYul)) =
          ((Stmt.storeThenIfLoad slot value body).eval state).toSymYulResults
      simp [SolidCoreYulCore.SymYul.bindNormal,
        SolidCoreYulCore.SymYul.normalResult, hStore, hIf]
  | seq first second first_ih second_ih =>
      cases hFirst : first.eval state with
      | normal state' =>
          have hEvalFirst :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  ((extraFuel + second.fuel) + first.fuel)
                  state.toConfig first.toFullYul =
                [SolidCoreYulCore.SymYul.normalResult state'.toConfig] := by
            simpa [hFirst, Result.toSymYulResults] using
              first_ih (extraFuel + second.fuel) state
          have hEvalSecond :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  ((extraFuel + first.fuel) + second.fuel)
                  state'.toConfig second.toFullYul =
                (second.eval state').toSymYulResults :=
            second_ih (extraFuel + first.fuel) state'
          simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hFirst]
          rw [show extraFuel + (first.fuel + second.fuel + 1) =
              (extraFuel + first.fuel + second.fuel) + 1 by omega]
          have hEvalFirst' :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  (extraFuel + first.fuel + second.fuel)
                  state.toConfig first.toFullYul =
                [SolidCoreYulCore.SymYul.normalResult state'.toConfig] := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hEvalFirst
          have hEvalSecond' :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  (extraFuel + first.fuel + second.fuel)
                  state'.toConfig second.toFullYul =
                (second.eval state').toSymYulResults := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hEvalSecond
          simp [SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.normalResult,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
            Stmt.collect_toFullYul, hEvalFirst', hEvalSecond']
      | returned state' =>
          have hEvalFirst :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  ((extraFuel + second.fuel) + first.fuel)
                  state.toConfig first.toFullYul =
                [{ flow := SolidCoreYulCore.FullYul.Flow.left,
                   config := state'.toConfig }] := by
            simpa [hFirst, Result.toSymYulResults] using
              first_ih (extraFuel + second.fuel) state
          simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hFirst]
          rw [show extraFuel + (first.fuel + second.fuel + 1) =
              (extraFuel + first.fuel + second.fuel) + 1 by omega]
          have hEvalFirst' :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  (extraFuel + first.fuel + second.fuel)
                  state.toConfig first.toFullYul =
                [{ flow := SolidCoreYulCore.FullYul.Flow.left,
                   config := state'.toConfig }] := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hEvalFirst
          simp [SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
            Stmt.collect_toFullYul, hEvalFirst', Result.toSymYulResults]
      | reverted state' =>
          have hEvalFirst :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  ((extraFuel + second.fuel) + first.fuel)
                  state.toConfig first.toFullYul =
                [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
                   config := Result.revertConfig state' }] := by
            simpa [hFirst, Result.toSymYulResults] using
              first_ih (extraFuel + second.fuel) state
          simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hFirst]
          rw [show extraFuel + (first.fuel + second.fuel + 1) =
              (extraFuel + first.fuel + second.fuel) + 1 by omega]
          have hEvalFirst' :
              SolidCoreYulCore.SymYul.evalStmtFuel
                  (extraFuel + first.fuel + second.fuel)
                  state.toConfig first.toFullYul =
                [{ flow := SolidCoreYulCore.FullYul.Flow.halted,
                   config := Result.revertConfig state' }] := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hEvalFirst
          simp [SolidCoreYulCore.SymYul.evalStmtFuel,
            SolidCoreYulCore.SymYul.bindNormal,
            SolidCoreYulCore.SymYul.collectStmtFunctionDefs,
            Stmt.collect_toFullYul, hEvalFirst', Result.toSymYulResults]
  | ifThen cond body body_ih =>
      by_cases hCond : SolidCoreYulCore.norm cond.eval = 0
      · have hZero : cond.eval % SolidCoreYulCore.wordModulus = 0 := by
          simpa [SolidCoreYulCore.norm] using hCond
        simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_true]
        rw [show extraFuel + (body.fuel + 1) =
            (extraFuel + body.fuel) + 1 by omega]
        simp [SolidCoreYulCore.SymYul.evalStmtFuel,
          SolidCoreYulCore.SymYul.evalExpr,
          SolidCoreYulCore.SymYul.evalExprs,
          SolidCoreYulCore.SymYul.branchOn,
          SolidCoreYulCore.SymYul.knownZero?,
          SolidCoreYulCore.norm, hCond, hZero,
          Expr.toFullYul_correct_env, Result.toSymYulResults]
      · have hBody :
            SolidCoreYulCore.SymYul.evalStmtFuel
                (extraFuel + body.fuel)
                state.toConfig body.toFullYul =
              (body.eval state).toSymYulResults :=
          body_ih extraFuel state
        have hNonzero : cond.eval % SolidCoreYulCore.wordModulus ≠ 0 := by
          simpa [SolidCoreYulCore.norm] using hCond
        simp only [Stmt.fuel, Stmt.toFullYul, Stmt.eval, hCond, if_false]
        rw [show extraFuel + (body.fuel + 1) =
            (extraFuel + body.fuel) + 1 by omega]
        simp [SolidCoreYulCore.SymYul.evalStmtFuel,
          SolidCoreYulCore.SymYul.evalExpr,
          SolidCoreYulCore.SymYul.evalExprs,
          SolidCoreYulCore.SymYul.branchOn,
          SolidCoreYulCore.SymYul.knownZero?,
          SolidCoreYulCore.norm, hCond, hNonzero,
          Expr.toFullYul_correct_env, hBody]
  | switch1 discr label branch defaultBranch branch_ih default_ih =>
      exact
        Stmt.switch1_toFullYul_correct_from
          extraFuel state discr label branch defaultBranch
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              branch_ih (extraFuel + defaultBranch.fuel) state)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              default_ih (extraFuel + branch.fuel) state)
  | switch2 discr firstLabel firstBranch secondLabel secondBranch defaultBranch
      hDistinct first_ih second_ih default_ih =>
      exact
        Stmt.switch2_toFullYul_correct_from
          extraFuel state discr firstLabel firstBranch secondLabel
          secondBranch defaultBranch hDistinct
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              first_ih
                (extraFuel + secondBranch.fuel + defaultBranch.fuel + 2)
                state)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              second_ih
                (extraFuel + firstBranch.fuel + defaultBranch.fuel + 2)
                state)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              default_ih
                (extraFuel + firstBranch.fuel + secondBranch.fuel + 2)
                state)
  | forFalse body body_ih =>
      have hFuel : 0 < extraFuel + body.fuel := by
        have hBodyFuel : 0 < body.fuel := Stmt.fuel_pos body
        omega
      have hLoop :=
        Stmt.evalStmtFuel_forFalseFullYul_from
          (extraFuel + body.fuel) hFuel state body.toFullYul
      simpa [Stmt.fuel, Stmt.toFullYul, Stmt.eval,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLoop
  | forOnce body body_ih =>
      have hBody :
          SolidCoreYulCore.SymYul.evalStmtFuel
              ((extraFuel + 1) + body.fuel)
              state.toConfig body.toFullYul =
            (body.eval state).toSymYulResults :=
        body_ih (extraFuel + 1) state
      exact
        Stmt.evalStmtFuel_singleIterationLoopFullYul_one_from
          extraFuel state body hBody
  | forIf cond body body_ih =>
      by_cases hCond : SolidCoreYulCore.norm cond.eval = 0
      · exact
          Stmt.evalStmtFuel_singleIterationLoopFullYul_zero_from
            extraFuel state cond body hCond
      · have hBody :
            SolidCoreYulCore.SymYul.evalStmtFuel
                ((extraFuel + 1) + body.fuel)
                state.toConfig body.toFullYul =
              (body.eval state).toSymYulResults :=
          body_ih (extraFuel + 1) state
        exact
          Stmt.evalStmtFuel_singleIterationLoopFullYul_nonzero_from
            extraFuel state cond body hCond hBody

theorem Stmt.toFullYul_correct (state : State) (stmt : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        stmt.fuel state.toConfig stmt.toFullYul =
      (stmt.eval state).toSymYulResults := by
  simpa using Stmt.toFullYul_correct_from 0 state stmt

theorem Stmt.MVP.toFullYul_correct_from
    {stmt : Stmt} (_hMVP : Stmt.MVP stmt)
    (extraFuel : Nat) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + stmt.fuel)
        state.toConfig stmt.toFullYul =
      (stmt.eval state).toSymYulResults := by
  exact Stmt.toFullYul_correct_from extraFuel state stmt

theorem Stmt.MVP.toFullYul_correct
    {stmt : Stmt} (_hMVP : Stmt.MVP stmt) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        stmt.fuel state.toConfig stmt.toFullYul =
      (stmt.eval state).toSymYulResults := by
  exact Stmt.toFullYul_correct state stmt

theorem Stmt.MVP.toFullYul_staticChecked
    {stmt : Stmt} (_hMVP : Stmt.MVP stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel stmt.fuel
        initialStaticContext false true stmt.toFullYul =
      some initialStaticContext := by
  exact Stmt.toFullYul_staticChecked stmt

theorem Stmt.MVP.toFullYul_compilerEmittable
    {stmt : Stmt} (_hMVP : Stmt.MVP stmt) :
    SolidCoreYulCore.FullYul.CompilerEmittableStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      stmt.toFullYul := by
  exact Stmt.toFullYul_compilerEmittable stmt

theorem Stmt.MVP.toFullYul_accepted_currentSolidCore_static
    {stmt : Stmt} (_hMVP : Stmt.MVP stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      stmt.fuel initialStaticContext false true stmt.toFullYul
      initialStaticContext := by
  exact Stmt.toFullYul_accepted_currentSolidCore_static stmt

theorem Stmt.loopIf_toFullYul_correct_from
    (extraFuel : Nat) (state : State) (cond : Expr) (body : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.loopIf cond body).fuel)
        state.toConfig (Stmt.loopIf cond body).toFullYul =
      ((Stmt.loopIf cond body).eval state).toSymYulResults := by
  exact Stmt.toFullYul_correct_from extraFuel state (Stmt.loopIf cond body)

theorem Stmt.boundedWhile_toFullYul_correct_from
    (extraFuel : Nat) (state : State) (bound : Nat)
    (cond : Expr) (body : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.boundedWhile bound cond body).fuel)
        state.toConfig (Stmt.boundedWhile bound cond body).toFullYul =
      ((Stmt.boundedWhile bound cond body).eval state).toSymYulResults := by
  exact
    Stmt.toFullYul_correct_from extraFuel state
      (Stmt.boundedWhile bound cond body)

theorem Stmt.switchCases_toFullYul_correct_from
    (extraFuel : Nat) (state : State) (discr : Expr)
    (cases : List (Word × Stmt)) (defaultBranch : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (extraFuel + (Stmt.switchCases discr cases defaultBranch).fuel)
        state.toConfig
        (Stmt.switchCases discr cases defaultBranch).toFullYul =
      ((Stmt.switchCases discr cases defaultBranch).eval state).toSymYulResults := by
  exact
    Stmt.toFullYul_correct_from extraFuel state
      (Stmt.switchCases discr cases defaultBranch)

theorem Stmt.switchCases_staticChecked
    (discr : Expr) (cases : List (Word × Stmt)) (defaultBranch : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (Stmt.switchCases discr cases defaultBranch).fuel
        initialStaticContext false true
        (Stmt.switchCases discr cases defaultBranch).toFullYul =
      some initialStaticContext := by
  exact Stmt.toFullYul_staticChecked
    (Stmt.switchCases discr cases defaultBranch)

theorem Stmt.switchCases_accepted_currentSolidCore
    (discr : Expr) (cases : List (Word × Stmt)) (defaultBranch : Stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (Stmt.switchCases discr cases defaultBranch).fuel
      initialStaticContext false true
      (Stmt.switchCases discr cases defaultBranch).toFullYul
      initialStaticContext := by
  exact Stmt.toFullYul_accepted_currentSolidCore_static
    (Stmt.switchCases discr cases defaultBranch)

def compileStmt (source : Stmt) : YulStmt :=
  source.toFullYul

def compileStmtFuel (source : Stmt) : Nat :=
  source.fuel

theorem compileStmt_correct (state : State) (source : Stmt) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileStmtFuel source) state.toConfig (compileStmt source) =
      (source.eval state).toSymYulResults := by
  exact Stmt.toFullYul_correct state source

theorem compileStmt_staticChecked (source : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileStmtFuel source)
        initialStaticContext false true (compileStmt source) =
      some initialStaticContext := by
  exact Stmt.toFullYul_staticChecked source

theorem compileStmt_accepted_currentSolidCore
    (source : Stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileStmtFuel source) initialStaticContext false true
      (compileStmt source)
      initialStaticContext := by
  exact Stmt.toFullYul_accepted_currentSolidCore_static source

structure StmtArtifact where
  source : Stmt
  stmt : YulStmt
  fuel : Nat
  stmt_eq : stmt = compileStmt source
  fuel_eq : fuel = compileStmtFuel source
  dynamic_sound :
    ∀ state : State,
      SolidCoreYulCore.SymYul.evalStmtFuel fuel state.toConfig stmt =
        (source.eval state).toSymYulResults
  static_checked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        fuel initialStaticContext false true stmt =
      some initialStaticContext
  accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      fuel initialStaticContext false true stmt initialStaticContext

def compileStmtArtifact (source : Stmt) : StmtArtifact :=
  { source := source
    stmt := compileStmt source
    fuel := compileStmtFuel source
    stmt_eq := rfl
    fuel_eq := rfl
    dynamic_sound := by
      intro state
      exact compileStmt_correct state source
    static_checked := compileStmt_staticChecked source
    accepted_currentSolidCore :=
      compileStmt_accepted_currentSolidCore source }

theorem compileStmtArtifact_stmt (source : Stmt) :
    (compileStmtArtifact source).stmt = compileStmt source := by
  rfl

theorem compileStmtArtifact_fuel (source : Stmt) :
    (compileStmtArtifact source).fuel = compileStmtFuel source := by
  rfl

theorem compileStmtArtifact_dynamic_sound
    (source : Stmt) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileStmtArtifact source).fuel
        state.toConfig
        (compileStmtArtifact source).stmt =
      (source.eval state).toSymYulResults := by
  exact (compileStmtArtifact source).dynamic_sound state

theorem compileStmtArtifact_staticChecked
    (source : Stmt) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileStmtArtifact source).fuel
        initialStaticContext false true
        (compileStmtArtifact source).stmt =
      some initialStaticContext := by
  exact (compileStmtArtifact source).static_checked

theorem compileStmtArtifact_accepted_currentSolidCore
    (source : Stmt) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileStmtArtifact source).fuel
      initialStaticContext false true
      (compileStmtArtifact source).stmt
      initialStaticContext := by
  exact (compileStmtArtifact source).accepted_currentSolidCore

structure SourceProgram where
  body : Stmt

def SourceProgram.eval (state : State) (source : SourceProgram) : Result :=
  source.body.eval state

def compileSourceProgramStmt (source : SourceProgram) : YulStmt :=
  compileStmt source.body

def compileSourceProgramFuel (source : SourceProgram) : Nat :=
  compileStmtFuel source.body

theorem compileSourceProgram_correct
    (state : State) (source : SourceProgram) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileSourceProgramFuel source)
        state.toConfig
        (compileSourceProgramStmt source) =
      (source.eval state).toSymYulResults := by
  exact compileStmt_correct state source.body

theorem compileSourceProgram_staticChecked
    (source : SourceProgram) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileSourceProgramFuel source)
        initialStaticContext false true
        (compileSourceProgramStmt source) =
      some initialStaticContext := by
  exact compileStmt_staticChecked source.body

theorem compileSourceProgram_accepted_currentSolidCore
    (source : SourceProgram) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileSourceProgramFuel source)
      initialStaticContext false true
      (compileSourceProgramStmt source)
      initialStaticContext := by
  exact compileStmt_accepted_currentSolidCore source.body

structure SourceProgramArtifact where
  source : SourceProgram
  stmtArtifact : StmtArtifact
  body_eq : stmtArtifact.source = source.body

def compileSourceProgramArtifact
    (source : SourceProgram) : SourceProgramArtifact :=
  { source := source
    stmtArtifact := compileStmtArtifact source.body
    body_eq := rfl }

theorem compileSourceProgramArtifact_stmt
    (source : SourceProgram) :
    (compileSourceProgramArtifact source).stmtArtifact.stmt =
      compileSourceProgramStmt source := by
  rfl

theorem compileSourceProgramArtifact_fuel
    (source : SourceProgram) :
    (compileSourceProgramArtifact source).stmtArtifact.fuel =
      compileSourceProgramFuel source := by
  rfl

theorem compileSourceProgramArtifact_dynamic_sound
    (source : SourceProgram) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileSourceProgramArtifact source).stmtArtifact.fuel
        state.toConfig
        (compileSourceProgramArtifact source).stmtArtifact.stmt =
      (source.eval state).toSymYulResults := by
  exact compileStmtArtifact_dynamic_sound source.body state

theorem compileSourceProgramArtifact_staticChecked
    (source : SourceProgram) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileSourceProgramArtifact source).stmtArtifact.fuel
        initialStaticContext false true
        (compileSourceProgramArtifact source).stmtArtifact.stmt =
      some initialStaticContext := by
  exact compileStmtArtifact_staticChecked source.body

theorem compileSourceProgramArtifact_accepted_currentSolidCore
    (source : SourceProgram) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileSourceProgramArtifact source).stmtArtifact.fuel
      initialStaticContext false true
      (compileSourceProgramArtifact source).stmtArtifact.stmt
      initialStaticContext := by
  exact compileStmtArtifact_accepted_currentSolidCore source.body

inductive SurfaceStmt where
  | skip : SurfaceStmt
  | discard : Expr -> SurfaceStmt
  | returnExpr : Expr -> SurfaceStmt
  | returnStateExpr : StateExpr -> SurfaceStmt
  | storageStore : Expr -> Expr -> SurfaceStmt
  | storageLoadReturn : Expr -> SurfaceStmt
  | storageStoreThenIfLoad : Expr -> Expr -> SurfaceStmt -> SurfaceStmt
  | seq : SurfaceStmt -> SurfaceStmt -> SurfaceStmt
  | ifThen : Expr -> SurfaceStmt -> SurfaceStmt
  | switch1 : Expr -> Word -> SurfaceStmt -> SurfaceStmt -> SurfaceStmt
  | switch2 (discr : Expr)
      (firstLabel : Word) (firstBranch : SurfaceStmt)
      (secondLabel : Word) (secondBranch defaultBranch : SurfaceStmt)
      (hDistinct :
        SolidCoreYulCore.norm firstLabel ≠ SolidCoreYulCore.norm secondLabel) :
      SurfaceStmt
  | forFalse : SurfaceStmt -> SurfaceStmt
  | forOnce : SurfaceStmt -> SurfaceStmt
  | forIf : Expr -> SurfaceStmt -> SurfaceStmt
  deriving DecidableEq, Repr

def SurfaceStmt.eval (state : State) : SurfaceStmt -> Result
  | SurfaceStmt.skip => Result.normal state
  | SurfaceStmt.discard _ => Result.normal state
  | SurfaceStmt.returnExpr expr =>
      Result.returned (state.withWordReturn expr.eval)
  | SurfaceStmt.returnStateExpr expr =>
      Result.returned (state.withReturn (expr.eval state))
  | SurfaceStmt.storageStore slot value =>
      Result.normal (state.store slot value)
  | SurfaceStmt.storageLoadReturn slot =>
      Result.returned (state.withReturn (state.load slot))
  | SurfaceStmt.storageStoreThenIfLoad slot value body =>
      let stored := state.store slot value
      if SolidCoreYulCore.norm value.eval = 0 then
        Result.normal stored
      else
        body.eval stored
  | SurfaceStmt.seq first second =>
      match first.eval state with
      | Result.normal state' => second.eval state'
      | Result.returned state' => Result.returned state'
      | Result.reverted state' => Result.reverted state'
  | SurfaceStmt.ifThen cond body =>
      if SolidCoreYulCore.norm cond.eval = 0 then
        Result.normal state
      else
        body.eval state
  | SurfaceStmt.switch1 discr label branch defaultBranch =>
      if SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm label then
        branch.eval state
      else
        defaultBranch.eval state
  | SurfaceStmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch _ =>
      if SolidCoreYulCore.norm discr.eval = SolidCoreYulCore.norm firstLabel then
        firstBranch.eval state
      else if
          SolidCoreYulCore.norm discr.eval =
            SolidCoreYulCore.norm secondLabel then
        secondBranch.eval state
      else
        defaultBranch.eval state
  | SurfaceStmt.forFalse _ => Result.normal state
  | SurfaceStmt.forOnce body => body.eval state
  | SurfaceStmt.forIf cond body =>
      if SolidCoreYulCore.norm cond.eval = 0 then
        Result.normal state
      else
        body.eval state

def SurfaceStmt.toCoreStmt : SurfaceStmt -> Stmt
  | SurfaceStmt.skip => Stmt.skip
  | SurfaceStmt.discard expr => Stmt.discard expr
  | SurfaceStmt.returnExpr expr => Stmt.returnExpr expr
  | SurfaceStmt.returnStateExpr expr => Stmt.returnStateExpr expr
  | SurfaceStmt.storageStore slot value => Stmt.store slot value
  | SurfaceStmt.storageLoadReturn slot => Stmt.loadReturn slot
  | SurfaceStmt.storageStoreThenIfLoad slot value body =>
      Stmt.storeThenIfLoad slot value body.toCoreStmt
  | SurfaceStmt.seq first second =>
      Stmt.seq first.toCoreStmt second.toCoreStmt
  | SurfaceStmt.ifThen cond body =>
      Stmt.ifThen cond body.toCoreStmt
  | SurfaceStmt.switch1 discr label branch defaultBranch =>
      Stmt.switch1 discr label branch.toCoreStmt defaultBranch.toCoreStmt
  | SurfaceStmt.switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch hDistinct =>
      Stmt.switch2 discr firstLabel firstBranch.toCoreStmt secondLabel
        secondBranch.toCoreStmt defaultBranch.toCoreStmt hDistinct
  | SurfaceStmt.forFalse body =>
      Stmt.forFalse body.toCoreStmt
  | SurfaceStmt.forOnce body =>
      Stmt.forOnce body.toCoreStmt
  | SurfaceStmt.forIf cond body =>
      Stmt.forIf cond body.toCoreStmt

theorem SurfaceStmt.toCoreStmt_mvp
    (source : SurfaceStmt) : Stmt.MVP source.toCoreStmt := by
  induction source with
  | skip =>
      exact Stmt.MVP.skip
  | discard expr =>
      exact Stmt.MVP.discard (Expr.valueOK expr)
  | returnExpr expr =>
      exact Stmt.MVP.returnExpr (Expr.valueOK expr)
  | returnStateExpr expr =>
      exact Stmt.MVP.returnStateExpr (StateExpr.ok expr)
  | storageStore slot value =>
      exact Stmt.MVP.store (Expr.slotOK slot) (Expr.valueOK value)
  | storageLoadReturn slot =>
      exact Stmt.MVP.loadReturn (Expr.slotOK slot)
  | storageStoreThenIfLoad slot value body body_ih =>
      exact
        Stmt.MVP.storeThenIfLoad
          (Expr.slotOK slot) (Expr.guardOK value) body_ih
  | seq first second first_ih second_ih =>
      exact Stmt.MVP.seq first_ih second_ih
  | ifThen cond body body_ih =>
      exact Stmt.MVP.ifThen (Expr.guardOK cond) body_ih
  | switch1 discr label branch defaultBranch branch_ih default_ih =>
      exact Stmt.MVP.switch1 (Expr.guardOK discr) branch_ih default_ih
  | switch2 discr firstLabel firstBranch secondLabel secondBranch
      defaultBranch hDistinct first_ih second_ih default_ih =>
      exact
        Stmt.MVP.switch2
          (Expr.guardOK discr) first_ih second_ih default_ih
  | forFalse body body_ih =>
      exact Stmt.MVP.forFalse body_ih
  | forOnce body body_ih =>
      exact Stmt.MVP.forOnce body_ih
  | forIf cond body body_ih =>
      exact Stmt.MVP.forIf (Expr.guardOK cond) body_ih

def SurfaceStmt.elabMVP? (source : SurfaceStmt) :
    Option { stmt : Stmt // Stmt.MVP stmt } :=
  some ⟨source.toCoreStmt, SurfaceStmt.toCoreStmt_mvp source⟩

theorem SurfaceStmt.elabMVP?_toCoreStmt
    {source : SurfaceStmt} {core : { stmt : Stmt // Stmt.MVP stmt }}
    (hElab : source.elabMVP? = some core) :
    core.val = source.toCoreStmt := by
  simp [SurfaceStmt.elabMVP?] at hElab
  cases hElab
  rfl

theorem SurfaceStmt.toCoreStmt_eval
    (state : State) (source : SurfaceStmt) :
    source.toCoreStmt.eval state = source.eval state := by
  induction source generalizing state with
  | skip =>
      rfl
  | discard _ =>
      rfl
  | returnExpr _ =>
      rfl
  | returnStateExpr _ =>
      rfl
  | storageStore _ _ =>
      rfl
  | storageLoadReturn _ =>
      rfl
  | storageStoreThenIfLoad _ _ body body_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        body_ih]
  | seq first second first_ih second_ih =>
      simp only [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval]
      rw [first_ih state]
      cases hFirst : first.eval state with
      | normal state' =>
          simp [second_ih state']
      | returned state' =>
          rfl
      | reverted state' =>
          rfl
  | ifThen _ body body_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        body_ih state]
  | switch1 _ _ branch defaultBranch branch_ih default_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        branch_ih state, default_ih state]
  | switch2 _ _ firstBranch _ secondBranch defaultBranch _
      first_ih second_ih default_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        first_ih state, second_ih state, default_ih state]
  | forFalse _ _ =>
      rfl
  | forOnce body body_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        body_ih state]
  | forIf _ body body_ih =>
      simp [SurfaceStmt.toCoreStmt, Stmt.eval, SurfaceStmt.eval,
        body_ih state]

theorem SurfaceStmt.elabMVP?_eval
    (state : State) {source : SurfaceStmt}
    {core : { stmt : Stmt // Stmt.MVP stmt }}
    (hElab : source.elabMVP? = some core) :
    core.val.eval state = source.eval state := by
  have hCore :=
    SurfaceStmt.elabMVP?_toCoreStmt (source := source)
      (core := core) hElab
  simpa [hCore] using SurfaceStmt.toCoreStmt_eval state source

def SurfaceStmt.loopIf (cond : Expr) (body : SurfaceStmt) : SurfaceStmt :=
  SurfaceStmt.ifThen cond (SurfaceStmt.forOnce body)

def SurfaceStmt.boundedWhile : Nat -> Expr -> SurfaceStmt -> SurfaceStmt
  | 0, _, _ => SurfaceStmt.skip
  | n + 1, cond, body =>
      SurfaceStmt.loopIf cond
        (SurfaceStmt.seq body (SurfaceStmt.boundedWhile n cond body))

def SurfaceStmt.switchCases
    (discr : Expr) :
    List (Word × SurfaceStmt) -> SurfaceStmt -> SurfaceStmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      SurfaceStmt.switch1 discr label branch
        (SurfaceStmt.switchCases discr rest defaultBranch)

theorem SurfaceStmt.loopIf_toCoreStmt
    (cond : Expr) (body : SurfaceStmt) :
    (SurfaceStmt.loopIf cond body).toCoreStmt =
      Stmt.loopIf cond body.toCoreStmt := by
  rfl

theorem SurfaceStmt.boundedWhile_toCoreStmt
    (bound : Nat) (cond : Expr) (body : SurfaceStmt) :
    (SurfaceStmt.boundedWhile bound cond body).toCoreStmt =
      Stmt.boundedWhile bound cond body.toCoreStmt := by
  induction bound with
  | zero =>
      rfl
  | succ bound ih =>
      simp [SurfaceStmt.boundedWhile, Stmt.boundedWhile,
        SurfaceStmt.loopIf, Stmt.loopIf, SurfaceStmt.toCoreStmt, ih]

theorem SurfaceStmt.switchCases_toCoreStmt
    (discr : Expr) (cases : List (Word × SurfaceStmt))
    (defaultBranch : SurfaceStmt) :
    (SurfaceStmt.switchCases discr cases defaultBranch).toCoreStmt =
      Stmt.switchCases discr
        (cases.map (fun switchCase =>
          (switchCase.1, switchCase.2.toCoreStmt)))
        defaultBranch.toCoreStmt := by
  induction cases with
  | nil =>
      rfl
  | cons head rest ih =>
      rcases head with ⟨label, branch⟩
      simp [SurfaceStmt.switchCases, Stmt.switchCases,
        SurfaceStmt.toCoreStmt, ih]

theorem SurfaceStmt.boundedWhile_toCoreStmt_eval
    (state : State) (bound : Nat) (cond : Expr) (body : SurfaceStmt) :
    (Stmt.boundedWhile bound cond body.toCoreStmt).eval state =
      (SurfaceStmt.boundedWhile bound cond body).eval state := by
  have hCore :=
    SurfaceStmt.boundedWhile_toCoreStmt bound cond body
  simpa [hCore] using
    SurfaceStmt.toCoreStmt_eval state
      (SurfaceStmt.boundedWhile bound cond body)

theorem SurfaceStmt.switchCases_toCoreStmt_eval
    (state : State) (discr : Expr)
    (cases : List (Word × SurfaceStmt))
    (defaultBranch : SurfaceStmt) :
    (Stmt.switchCases discr
        (cases.map (fun switchCase =>
          (switchCase.1, switchCase.2.toCoreStmt)))
        defaultBranch.toCoreStmt).eval state =
      (SurfaceStmt.switchCases discr cases defaultBranch).eval state := by
  have hCore :=
    SurfaceStmt.switchCases_toCoreStmt discr cases defaultBranch
  simpa [hCore] using
    SurfaceStmt.toCoreStmt_eval state
      (SurfaceStmt.switchCases discr cases defaultBranch)

structure SurfaceProgram where
  body : SurfaceStmt
  deriving DecidableEq, Repr

def SurfaceProgram.eval
    (state : State) (source : SurfaceProgram) : Result :=
  source.body.eval state

def SurfaceProgram.toSourceProgram
    (source : SurfaceProgram) : SourceProgram :=
  { body := source.body.toCoreStmt }

theorem SurfaceProgram.toSourceProgram_eval
    (state : State) (source : SurfaceProgram) :
    source.toSourceProgram.eval state = source.eval state := by
  simp [SurfaceProgram.toSourceProgram, SourceProgram.eval,
    SurfaceProgram.eval, SurfaceStmt.toCoreStmt_eval]

def SurfaceProgram.elabMVP?
    (source : SurfaceProgram) : Option { stmt : Stmt // Stmt.MVP stmt } :=
  source.body.elabMVP?

theorem SurfaceProgram.elabMVP?_eval
    (state : State) {source : SurfaceProgram}
    {core : { stmt : Stmt // Stmt.MVP stmt }}
    (hElab : source.elabMVP? = some core) :
    core.val.eval state = source.eval state := by
  simpa [SurfaceProgram.elabMVP?, SurfaceProgram.eval] using
    SurfaceStmt.elabMVP?_eval state hElab

def compileSurfaceMVPStmt?
    (source : SurfaceProgram) : Option YulStmt :=
  source.elabMVP?.map (fun core => core.val.toFullYul)

def compileSurfaceMVPFuel?
    (source : SurfaceProgram) : Option Nat :=
  source.elabMVP?.map (fun core => core.val.fuel)

theorem compileSurfaceMVP_correct
    (state : State) {source : SurfaceProgram}
    {core : { stmt : Stmt // Stmt.MVP stmt }}
    (hElab : source.elabMVP? = some core) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        core.val.fuel state.toConfig core.val.toFullYul =
      (source.eval state).toSymYulResults := by
  have hCore :=
    Stmt.MVP.toFullYul_correct core.property state
  have hEval :=
    SurfaceProgram.elabMVP?_eval state hElab
  simpa [hEval] using hCore

theorem compileSurfaceMVP_staticChecked
    {source : SurfaceProgram}
    {core : { stmt : Stmt // Stmt.MVP stmt }}
    (_hElab : source.elabMVP? = some core) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        core.val.fuel initialStaticContext false true core.val.toFullYul =
      some initialStaticContext := by
  exact Stmt.MVP.toFullYul_staticChecked core.property

theorem compileSurfaceMVP_accepted_currentSolidCore
    {source : SurfaceProgram}
    {core : { stmt : Stmt // Stmt.MVP stmt }}
    (_hElab : source.elabMVP? = some core) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      core.val.fuel initialStaticContext false true core.val.toFullYul
      initialStaticContext := by
  exact Stmt.MVP.toFullYul_accepted_currentSolidCore_static core.property

def compileSurfaceProgramStmt
    (source : SurfaceProgram) : YulStmt :=
  compileSourceProgramStmt source.toSourceProgram

def compileSurfaceProgramFuel
    (source : SurfaceProgram) : Nat :=
  compileSourceProgramFuel source.toSourceProgram

theorem compileSurfaceMVPStmt?_eq_compileSurfaceProgramStmt
    (source : SurfaceProgram) :
    compileSurfaceMVPStmt? source = some (compileSurfaceProgramStmt source) := by
  rfl

theorem compileSurfaceMVPFuel?_eq_compileSurfaceProgramFuel
    (source : SurfaceProgram) :
    compileSurfaceMVPFuel? source = some (compileSurfaceProgramFuel source) := by
  rfl

theorem compileSurfaceProgram_correct
    (state : State) (source : SurfaceProgram) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileSurfaceProgramFuel source)
        state.toConfig
        (compileSurfaceProgramStmt source) =
      (source.eval state).toSymYulResults := by
  simpa [compileSurfaceProgramFuel, compileSurfaceProgramStmt,
    SurfaceProgram.toSourceProgram_eval state source] using
    compileSourceProgram_correct state source.toSourceProgram

theorem compileSurfaceProgram_staticChecked
    (source : SurfaceProgram) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileSurfaceProgramFuel source)
        initialStaticContext false true
        (compileSurfaceProgramStmt source) =
      some initialStaticContext := by
  exact compileSourceProgram_staticChecked source.toSourceProgram

theorem compileSurfaceProgram_accepted_currentSolidCore
    (source : SurfaceProgram) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileSurfaceProgramFuel source)
      initialStaticContext false true
      (compileSurfaceProgramStmt source)
      initialStaticContext := by
  exact compileSourceProgram_accepted_currentSolidCore source.toSourceProgram

structure SurfaceProgramArtifact where
  source : SurfaceProgram
  sourceArtifact : SourceProgramArtifact
  source_eq : sourceArtifact.source = source.toSourceProgram

def compileSurfaceProgramArtifact
    (source : SurfaceProgram) : SurfaceProgramArtifact :=
  { source := source
    sourceArtifact := compileSourceProgramArtifact source.toSourceProgram
    source_eq := rfl }

theorem compileSurfaceProgramArtifact_stmt
    (source : SurfaceProgram) :
    (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.stmt =
      compileSurfaceProgramStmt source := by
  rfl

theorem compileSurfaceProgramArtifact_fuel
    (source : SurfaceProgram) :
    (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.fuel =
      compileSurfaceProgramFuel source := by
  rfl

theorem compileSurfaceProgramArtifact_dynamic_sound
    (source : SurfaceProgram) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.fuel
        state.toConfig
        (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.stmt =
      (source.eval state).toSymYulResults := by
  simpa [compileSurfaceProgramArtifact,
    SurfaceProgram.toSourceProgram_eval state source] using
    compileSourceProgramArtifact_dynamic_sound
      source.toSourceProgram state

theorem compileSurfaceProgramArtifact_staticChecked
    (source : SurfaceProgram) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact compileSourceProgramArtifact_staticChecked source.toSourceProgram

theorem compileSurfaceProgramArtifact_accepted_currentSolidCore
    (source : SurfaceProgram) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSourceProgramArtifact_accepted_currentSolidCore
      source.toSourceProgram

structure SurfaceProgramCertificate where
  source : SurfaceProgram
  stmt : YulStmt
  fuel : Nat
  artifact : SurfaceProgramArtifact
  stmt_eq : stmt = compileSurfaceProgramStmt source
  fuel_eq : fuel = compileSurfaceProgramFuel source
  artifact_eq : artifact = compileSurfaceProgramArtifact source

def compileSurfaceProgramCertificate
    (source : SurfaceProgram) : SurfaceProgramCertificate :=
  { source := source
    stmt := compileSurfaceProgramStmt source
    fuel := compileSurfaceProgramFuel source
    artifact := compileSurfaceProgramArtifact source
    stmt_eq := rfl
    fuel_eq := rfl
    artifact_eq := rfl }

def SurfaceProgramCertificate.Verified
    (cert : SurfaceProgramCertificate) : Prop :=
  cert.stmt = compileSurfaceProgramStmt cert.source ∧
  cert.fuel = compileSurfaceProgramFuel cert.source ∧
  cert.artifact = compileSurfaceProgramArtifact cert.source ∧
  (∀ state : State,
    SolidCoreYulCore.SymYul.evalStmtFuel
        cert.fuel state.toConfig cert.stmt =
      (cert.source.eval state).toSymYulResults) ∧
  SolidCoreYulCore.FullYul.checkStmtFuel
      cert.fuel initialStaticContext false true cert.stmt =
    some initialStaticContext ∧
  SolidCoreYulCore.FullYul.CompilerAcceptedStmt
    SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
    cert.fuel initialStaticContext false true cert.stmt
    initialStaticContext

def SurfaceProgramCertificate.VerifiedForSource
    (source : SurfaceProgram) (cert : SurfaceProgramCertificate) : Prop :=
  cert.source = source ∧ SurfaceProgramCertificate.Verified cert

theorem SurfaceProgramCertificate.dynamic_sound
    (cert : SurfaceProgramCertificate) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        cert.fuel state.toConfig cert.stmt =
      (cert.source.eval state).toSymYulResults := by
  rw [cert.fuel_eq, cert.stmt_eq]
  exact compileSurfaceProgram_correct state cert.source

theorem SurfaceProgramCertificate.staticChecked
    (cert : SurfaceProgramCertificate) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        cert.fuel initialStaticContext false true cert.stmt =
      some initialStaticContext := by
  rw [cert.fuel_eq, cert.stmt_eq]
  exact compileSurfaceProgram_staticChecked cert.source

theorem SurfaceProgramCertificate.accepted_currentSolidCore
    (cert : SurfaceProgramCertificate) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      cert.fuel initialStaticContext false true cert.stmt
      initialStaticContext := by
  rw [cert.fuel_eq, cert.stmt_eq]
  exact compileSurfaceProgram_accepted_currentSolidCore cert.source

theorem SurfaceProgramCertificate.verified
    (cert : SurfaceProgramCertificate) :
    SurfaceProgramCertificate.Verified cert := by
  exact ⟨cert.stmt_eq, cert.fuel_eq, cert.artifact_eq,
    cert.dynamic_sound, cert.staticChecked,
    cert.accepted_currentSolidCore⟩

theorem SurfaceProgramCertificate.verifiedForSource
    (cert : SurfaceProgramCertificate) :
    SurfaceProgramCertificate.VerifiedForSource cert.source cert := by
  exact ⟨rfl, cert.verified⟩

theorem compileSurfaceProgramCertificate_verified
    (source : SurfaceProgram) :
    SurfaceProgramCertificate.Verified
      (compileSurfaceProgramCertificate source) := by
  exact (compileSurfaceProgramCertificate source).verified

theorem compileSurfaceProgramCertificate_verifiedForSource
    (source : SurfaceProgram) :
    SurfaceProgramCertificate.VerifiedForSource source
      (compileSurfaceProgramCertificate source) := by
  exact (compileSurfaceProgramCertificate source).verifiedForSource

def switchStorageBuiltinProgram : Stmt :=
  Stmt.seq
    (Stmt.store (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
    (Stmt.switch1 (Expr.lit 1) 1
      (Stmt.loadReturn (Expr.lit 0))
      (Stmt.returnExpr (Expr.lit 9)))

def switchStorageBuiltinFinalState : State :=
  (initialState.store (Expr.lit 0)
    (Expr.add (Expr.lit 2) (Expr.lit 3))).withReturn
      (SolidCoreYulCore.FullYul.Value.word 5)

theorem switchStorageBuiltinProgram_eval :
    switchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

theorem switchStorageBuiltinProgram_toFullYul_correct :
    SolidCoreYulCore.SymYul.evalStmtFuel
        switchStorageBuiltinProgram.fuel
        initialState.toConfig
        switchStorageBuiltinProgram.toFullYul =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [switchStorageBuiltinProgram_eval] using
    Stmt.toFullYul_correct initialState switchStorageBuiltinProgram

theorem switchStorageBuiltinProgram_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        switchStorageBuiltinProgram.fuel
        initialStaticContext false true
        switchStorageBuiltinProgram.toFullYul =
      some initialStaticContext := by
  simpa using Stmt.toFullYul_staticChecked switchStorageBuiltinProgram

theorem switchStorageBuiltinProgram_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      switchStorageBuiltinProgram.fuel
      initialStaticContext false true
      switchStorageBuiltinProgram.toFullYul
      initialStaticContext := by
  exact
    Stmt.toFullYul_accepted_currentSolidCore_static
      switchStorageBuiltinProgram

def switchStorageBuiltinArtifact : StmtArtifact :=
  compileStmtArtifact switchStorageBuiltinProgram

theorem switchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        switchStorageBuiltinArtifact.fuel
        initialState.toConfig
        switchStorageBuiltinArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [switchStorageBuiltinArtifact, switchStorageBuiltinProgram_eval] using
    compileStmtArtifact_dynamic_sound switchStorageBuiltinProgram initialState

theorem switchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      switchStorageBuiltinArtifact.fuel
      initialStaticContext false true
      switchStorageBuiltinArtifact.stmt
      initialStaticContext := by
  exact compileStmtArtifact_accepted_currentSolidCore switchStorageBuiltinProgram

def loopSwitchStorageBuiltinProgram : Stmt :=
  Stmt.seq
    (Stmt.forFalse
      (Stmt.store (Expr.lit 0) (Expr.lit 99)))
    switchStorageBuiltinProgram

theorem loopSwitchStorageBuiltinProgram_eval :
    loopSwitchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

theorem loopSwitchStorageBuiltinProgram_toFullYul_correct :
    SolidCoreYulCore.SymYul.evalStmtFuel
        loopSwitchStorageBuiltinProgram.fuel
        initialState.toConfig
        loopSwitchStorageBuiltinProgram.toFullYul =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [loopSwitchStorageBuiltinProgram_eval] using
    Stmt.toFullYul_correct initialState loopSwitchStorageBuiltinProgram

def loopSwitchStorageBuiltinArtifact : StmtArtifact :=
  compileStmtArtifact loopSwitchStorageBuiltinProgram

theorem loopSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      loopSwitchStorageBuiltinArtifact.fuel
      initialStaticContext false true
      loopSwitchStorageBuiltinArtifact.stmt
      initialStaticContext := by
  exact
    compileStmtArtifact_accepted_currentSolidCore
      loopSwitchStorageBuiltinProgram

def switch2StorageBuiltinProgram : Stmt :=
  Stmt.seq
    (Stmt.store (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
    (Stmt.switch2 (Expr.lit 2)
      1 (Stmt.returnExpr (Expr.lit 9))
      2 (Stmt.loadReturn (Expr.lit 0))
      (Stmt.returnExpr (Expr.lit 7))
      (by decide))

theorem switch2StorageBuiltinProgram_eval :
    switch2StorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

theorem switch2StorageBuiltinProgram_toFullYul_correct :
    SolidCoreYulCore.SymYul.evalStmtFuel
        switch2StorageBuiltinProgram.fuel
        initialState.toConfig
        switch2StorageBuiltinProgram.toFullYul =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [switch2StorageBuiltinProgram_eval] using
    Stmt.toFullYul_correct initialState switch2StorageBuiltinProgram

def switch2StorageBuiltinArtifact : StmtArtifact :=
  compileStmtArtifact switch2StorageBuiltinProgram

theorem switch2StorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      switch2StorageBuiltinArtifact.fuel
      initialStaticContext false true
      switch2StorageBuiltinArtifact.stmt
      initialStaticContext := by
  exact
    compileStmtArtifact_accepted_currentSolidCore
      switch2StorageBuiltinProgram

def switch2SourceProgram : SourceProgram :=
  { body := switch2StorageBuiltinProgram }

def switch2SourceProgramArtifact : SourceProgramArtifact :=
  compileSourceProgramArtifact switch2SourceProgram

theorem switch2SourceProgramArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        switch2SourceProgramArtifact.stmtArtifact.fuel
        initialState.toConfig
        switch2SourceProgramArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [switch2SourceProgramArtifact, switch2SourceProgram,
    switch2StorageBuiltinProgram_eval] using
    compileSourceProgramArtifact_dynamic_sound
      switch2SourceProgram initialState

theorem switch2SourceProgramArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      switch2SourceProgramArtifact.stmtArtifact.fuel
      initialStaticContext false true
      switch2SourceProgramArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSourceProgramArtifact_accepted_currentSolidCore
      switch2SourceProgram

def surfaceSwitchCasesStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore
          (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
        (SurfaceStmt.switchCases (Expr.lit 3)
          [ (1, SurfaceStmt.returnExpr (Expr.lit 9))
          , (2, SurfaceStmt.returnExpr (Expr.lit 7))
          , (3, SurfaceStmt.storageLoadReturn (Expr.lit 0)) ]
          (SurfaceStmt.returnExpr (Expr.lit 11))) }

theorem surfaceSwitchCasesStorageBuiltinProgram_eval :
    surfaceSwitchCasesStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceSwitchCasesStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceSwitchCasesStorageBuiltinProgram

theorem surfaceSwitchCasesStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceSwitchCasesStorageBuiltinArtifact,
    surfaceSwitchCasesStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceSwitchCasesStorageBuiltinProgram initialState

theorem surfaceSwitchCasesStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceSwitchCasesStorageBuiltinProgram

theorem surfaceSwitchCasesStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceSwitchCasesStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceSwitchCasesStorageBuiltinProgram

def surfaceLoopSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.forFalse
          (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 99)))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
          (SurfaceStmt.switch2 (Expr.lit 2)
            1 (SurfaceStmt.returnExpr (Expr.lit 9))
            2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
            (SurfaceStmt.returnExpr (Expr.lit 7))
            (by decide))) }

theorem surfaceLoopSwitchStorageBuiltinProgram_eval :
    surfaceLoopSwitchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceLoopSwitchStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceLoopSwitchStorageBuiltinProgram

theorem surfaceLoopSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceLoopSwitchStorageBuiltinArtifact,
    surfaceLoopSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceLoopSwitchStorageBuiltinProgram initialState

theorem surfaceLoopSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceLoopSwitchStorageBuiltinProgram

theorem surfaceLoopSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceLoopSwitchStorageBuiltinProgram

def surfaceOnceSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.forOnce
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))))
        (SurfaceStmt.switch2 (Expr.lit 2)
          1 (SurfaceStmt.returnExpr (Expr.lit 9))
          2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
          (SurfaceStmt.returnExpr (Expr.lit 7))
          (by decide)) }

theorem surfaceOnceSwitchStorageBuiltinProgram_eval :
    surfaceOnceSwitchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceOnceSwitchStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceOnceSwitchStorageBuiltinProgram

theorem surfaceOnceSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceOnceSwitchStorageBuiltinArtifact,
    surfaceOnceSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceOnceSwitchStorageBuiltinProgram initialState

theorem surfaceOnceSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceOnceSwitchStorageBuiltinProgram

theorem surfaceOnceSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceOnceSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceOnceSwitchStorageBuiltinProgram

def surfaceGuardedSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.forIf (Expr.lit 1)
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))))
        (SurfaceStmt.switch2 (Expr.lit 2)
          1 (SurfaceStmt.returnExpr (Expr.lit 9))
          2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
          (SurfaceStmt.returnExpr (Expr.lit 7))
          (by decide)) }

theorem surfaceGuardedSwitchStorageBuiltinProgram_eval :
    surfaceGuardedSwitchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceGuardedSwitchStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceGuardedSwitchStorageBuiltinProgram

theorem surfaceGuardedSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceGuardedSwitchStorageBuiltinArtifact,
    surfaceGuardedSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceGuardedSwitchStorageBuiltinProgram initialState

theorem surfaceGuardedSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceGuardedSwitchStorageBuiltinProgram

theorem surfaceGuardedSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceGuardedSwitchStorageBuiltinProgram

def surfaceSkippedGuardedSwitchStorageBuiltinFinalState : State :=
  { returnValue :=
      SolidCoreYulCore.FullYul.Value.storageWord storageAccountZero
        (SolidCoreYulCore.FullYul.Value.word 0)
    storage := [] }

def surfaceSkippedGuardedSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.forIf (Expr.lit 0)
          (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 99)))
        (SurfaceStmt.switch2 (Expr.lit 2)
          1 (SurfaceStmt.returnExpr (Expr.lit 9))
          2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
          (SurfaceStmt.returnExpr (Expr.lit 7))
          (by decide)) }

theorem surfaceSkippedGuardedSwitchStorageBuiltinProgram_eval :
    surfaceSkippedGuardedSwitchStorageBuiltinProgram.eval initialState =
      Result.returned surfaceSkippedGuardedSwitchStorageBuiltinFinalState := by
  rfl

def surfaceSkippedGuardedSwitchStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceSkippedGuardedSwitchStorageBuiltinProgram

theorem surfaceSkippedGuardedSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceSkippedGuardedSwitchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceSkippedGuardedSwitchStorageBuiltinArtifact,
    surfaceSkippedGuardedSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceSkippedGuardedSwitchStorageBuiltinProgram initialState

theorem surfaceSkippedGuardedSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceSkippedGuardedSwitchStorageBuiltinProgram

theorem surfaceSkippedGuardedSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceSkippedGuardedSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceSkippedGuardedSwitchStorageBuiltinProgram

def surfaceBoundedLoopSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.boundedWhile 2 (Expr.lit 1)
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))))
        (SurfaceStmt.switch2 (Expr.lit 2)
          1 (SurfaceStmt.returnExpr (Expr.lit 9))
          2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
          (SurfaceStmt.returnExpr (Expr.lit 7))
          (by decide)) }

def surfaceBoundedLoopSwitchStorageBuiltinFinalState : State :=
  ((initialState.store (Expr.lit 0)
    (Expr.add (Expr.lit 2) (Expr.lit 3))).store (Expr.lit 0)
      (Expr.add (Expr.lit 2) (Expr.lit 3))).withReturn
        (SolidCoreYulCore.FullYul.Value.word 5)

theorem surfaceBoundedLoopSwitchStorageBuiltinProgram_eval :
    surfaceBoundedLoopSwitchStorageBuiltinProgram.eval initialState =
      Result.returned surfaceBoundedLoopSwitchStorageBuiltinFinalState := by
  rfl

def surfaceBoundedLoopSwitchStorageBuiltinArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceBoundedLoopSwitchStorageBuiltinProgram

theorem surfaceBoundedLoopSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceBoundedLoopSwitchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceBoundedLoopSwitchStorageBuiltinArtifact,
    surfaceBoundedLoopSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceBoundedLoopSwitchStorageBuiltinProgram initialState

theorem surfaceBoundedLoopSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceBoundedLoopSwitchStorageBuiltinProgram

theorem surfaceBoundedLoopSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceBoundedLoopSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceBoundedLoopSwitchStorageBuiltinProgram

def surfaceStoreThenIfLoadSwitchStorageBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.storageStoreThenIfLoad
        (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))
        (SurfaceStmt.switch2 (Expr.lit 2)
          1 (SurfaceStmt.returnExpr (Expr.lit 9))
          2 (SurfaceStmt.storageLoadReturn (Expr.lit 0))
          (SurfaceStmt.returnExpr (Expr.lit 7))
          (by decide)) }

theorem surfaceStoreThenIfLoadSwitchStorageBuiltinProgram_eval :
    surfaceStoreThenIfLoadSwitchStorageBuiltinProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceStoreThenIfLoadSwitchStorageBuiltinProgram

theorem surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact,
    surfaceStoreThenIfLoadSwitchStorageBuiltinProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceStoreThenIfLoadSwitchStorageBuiltinProgram initialState

theorem surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceStoreThenIfLoadSwitchStorageBuiltinProgram

theorem surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceStoreThenIfLoadSwitchStorageBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceStoreThenIfLoadSwitchStorageBuiltinProgram

def surfaceStoreThenIfLoadSkippedProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.storageStoreThenIfLoad
        (Expr.lit 0) (Expr.lit 0)
        (SurfaceStmt.returnExpr (Expr.lit 9)) }

def surfaceStoreThenIfLoadSkippedFinalState : State :=
  initialState.store (Expr.lit 0) (Expr.lit 0)

theorem surfaceStoreThenIfLoadSkippedProgram_eval :
    surfaceStoreThenIfLoadSkippedProgram.eval initialState =
      Result.normal surfaceStoreThenIfLoadSkippedFinalState := by
  rfl

def surfaceStoreThenIfLoadSkippedArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceStoreThenIfLoadSkippedProgram

theorem surfaceStoreThenIfLoadSkippedArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.normal surfaceStoreThenIfLoadSkippedFinalState).toSymYulResults := by
  simpa [surfaceStoreThenIfLoadSkippedArtifact,
    surfaceStoreThenIfLoadSkippedProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceStoreThenIfLoadSkippedProgram initialState

theorem surfaceStoreThenIfLoadSkippedArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceStoreThenIfLoadSkippedProgram

theorem surfaceStoreThenIfLoadSkippedArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceStoreThenIfLoadSkippedProgram

def surfaceStorageExprAddProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 7))
          (SurfaceStmt.returnStateExpr
            (StateExpr.add
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceStorageExprAddFinalState : State :=
  ((initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 7)).withReturn
      (SolidCoreYulCore.FullYul.Value.word 12)

theorem surfaceStorageExprAddProgram_eval :
    surfaceStorageExprAddProgram.eval initialState =
      Result.returned surfaceStorageExprAddFinalState := by
  rfl

def surfaceStorageExprAddArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceStorageExprAddProgram

theorem surfaceStorageExprAddArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned surfaceStorageExprAddFinalState).toSymYulResults := by
  simpa [surfaceStorageExprAddArtifact,
    surfaceStorageExprAddProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceStorageExprAddProgram initialState

theorem surfaceStorageExprAddArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceStorageExprAddProgram

theorem surfaceStorageExprAddArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceStorageExprAddArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceStorageExprAddProgram

def surfaceBoundedLoopSwitchStorageBuiltinSource : String :=
  "mvp { boundedWhile 2 1 { sstore(0, 2 + 3); } switch 2 { case 1: return 9; case 2: return sload(0); default: return 7; } }"

def surfaceSwitchCasesStorageBuiltinSource : String :=
  "mvp { sstore(0, 2 + 3); switch 3 { case 1: return 9; case 2: return 7; case 3: return sload(0); default: return 11; } }"

def surfaceParsedReturnBuiltinSource : String :=
  "mvp { return addmod(5, 7, 10); }"

def surfaceParsedReturnBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.returnExpr
        (Expr.addmod (Expr.lit 5) (Expr.lit 7) (Expr.lit 10)) }

def surfaceParsedContractLocalShadowsStorageSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { uint256 x = 9; return x; } }"

def surfaceParsedContractLocalShadowsStorageProgram : SurfaceProgram :=
  { body := SurfaceStmt.returnStateExpr (StateExpr.pure (Expr.lit 9)) }

def surfaceParsedContractLocalShadowsStorageFinalState : State :=
  initialState.withWordReturn 9

theorem surfaceParsedContractLocalShadowsStorageProgram_eval :
    surfaceParsedContractLocalShadowsStorageProgram.eval initialState =
      Result.returned surfaceParsedContractLocalShadowsStorageFinalState := by
  rfl

def surfaceParsedContractLocalShadowsStorageArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact
    surfaceParsedContractLocalShadowsStorageProgram

theorem surfaceParsedContractLocalShadowsStorageArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedContractLocalShadowsStorageFinalState).toSymYulResults := by
  simpa [surfaceParsedContractLocalShadowsStorageArtifact,
    surfaceParsedContractLocalShadowsStorageProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedContractLocalShadowsStorageProgram initialState

theorem surfaceParsedContractLocalShadowsStorageArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedContractLocalShadowsStorageProgram

theorem surfaceParsedContractLocalShadowsStorageArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedContractLocalShadowsStorageProgram

def surfaceParsedStoreLoadBuiltinSource : String :=
  "mvp { sstore(0, 2 + 3); return sload(0); }"

def surfaceParsedStoreLoadBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore
          (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
        (SurfaceStmt.storageLoadReturn (Expr.lit 0)) }

def surfaceParsedContractStorageVarExprReturnSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { x = 5; return x + 7; } }"

def surfaceParsedContractStorageVarExprReturnProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.returnStateExpr
          (StateExpr.add
            (StateExpr.load (Expr.lit 0))
            (StateExpr.pure (Expr.lit 7)))) }

def surfaceParsedContractStorageVarExprReturnFinalState : State :=
  let stored := initialState.store (Expr.lit 0) (Expr.lit 5)
  stored.withReturn
    ((StateExpr.add
      (StateExpr.load (Expr.lit 0))
      (StateExpr.pure (Expr.lit 7))).eval stored)

theorem surfaceParsedContractStorageVarExprReturnProgram_eval :
    surfaceParsedContractStorageVarExprReturnProgram.eval initialState =
      Result.returned surfaceParsedContractStorageVarExprReturnFinalState := by
  rfl

def surfaceParsedContractStorageVarExprReturnArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact
    surfaceParsedContractStorageVarExprReturnProgram

theorem surfaceParsedContractStorageVarExprReturnArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedContractStorageVarExprReturnFinalState).toSymYulResults := by
  simpa [surfaceParsedContractStorageVarExprReturnArtifact,
    surfaceParsedContractStorageVarExprReturnProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedContractStorageVarExprReturnProgram initialState

theorem surfaceParsedContractStorageVarExprReturnArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedContractStorageVarExprReturnProgram

theorem surfaceParsedContractStorageVarExprReturnArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractStorageVarExprReturnArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedContractStorageVarExprReturnProgram

def surfaceParsedContractStorageVarSwitchSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { x = 5; switch x { case 5: return x; default: return x + 1; } } }"

def surfaceParsedContractStorageVarSwitchProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.switchCases (Expr.lit 5)
          [ (5,
              SurfaceStmt.returnStateExpr
                (StateExpr.load (Expr.lit 0))) ]
          (SurfaceStmt.returnStateExpr
            (StateExpr.add
              (StateExpr.load (Expr.lit 0))
              (StateExpr.pure (Expr.lit 1))))) }

def surfaceParsedContractStorageVarSwitchStoredState : State :=
  initialState.store (Expr.lit 0) (Expr.lit 5)

def surfaceParsedContractStorageVarSwitchFinalState : State :=
  surfaceParsedContractStorageVarSwitchStoredState.withReturn
    ((StateExpr.load (Expr.lit 0)).eval
      surfaceParsedContractStorageVarSwitchStoredState)

theorem surfaceParsedContractStorageVarSwitchProgram_eval :
    surfaceParsedContractStorageVarSwitchProgram.eval initialState =
      Result.returned surfaceParsedContractStorageVarSwitchFinalState := by
  rfl

def surfaceParsedContractStorageVarSwitchArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact
    surfaceParsedContractStorageVarSwitchProgram

theorem surfaceParsedContractStorageVarSwitchArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedContractStorageVarSwitchFinalState).toSymYulResults := by
  simpa [surfaceParsedContractStorageVarSwitchArtifact,
    surfaceParsedContractStorageVarSwitchProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedContractStorageVarSwitchProgram initialState

theorem surfaceParsedContractStorageVarSwitchArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedContractStorageVarSwitchProgram

theorem surfaceParsedContractStorageVarSwitchArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedContractStorageVarSwitchProgram

def surfaceParsedContractStorageVarSwitchTwoCaseSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { x = 5; switch x { case 4: return x + 2; case 5: return x; default: return x + 1; } } }"

def surfaceParsedContractStorageVarSwitchTwoCaseProgram :
    SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.switchCases (Expr.lit 5)
          [ (4,
              SurfaceStmt.returnStateExpr
                (StateExpr.add
                  (StateExpr.load (Expr.lit 0))
                  (StateExpr.pure (Expr.lit 2))))
          , (5,
              SurfaceStmt.returnStateExpr
                (StateExpr.load (Expr.lit 0))) ]
          (SurfaceStmt.returnStateExpr
            (StateExpr.add
              (StateExpr.load (Expr.lit 0))
              (StateExpr.pure (Expr.lit 1))))) }

def surfaceParsedContractStorageVarSwitchTwoCaseArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact
    surfaceParsedContractStorageVarSwitchTwoCaseProgram

theorem surfaceParsedContractStorageVarSwitchTwoCaseProgram_eval :
    surfaceParsedContractStorageVarSwitchTwoCaseProgram.eval initialState =
      Result.returned surfaceParsedContractStorageVarSwitchFinalState := by
  rfl

theorem surfaceParsedContractStorageVarSwitchTwoCaseArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedContractStorageVarSwitchFinalState).toSymYulResults := by
  simpa [surfaceParsedContractStorageVarSwitchTwoCaseArtifact,
    surfaceParsedContractStorageVarSwitchTwoCaseProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedContractStorageVarSwitchTwoCaseProgram initialState

theorem surfaceParsedContractStorageVarSwitchTwoCaseArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedContractStorageVarSwitchTwoCaseProgram

theorem surfaceParsedContractStorageVarSwitchTwoCaseArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractStorageVarSwitchTwoCaseArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedContractStorageVarSwitchTwoCaseProgram

def surfaceParsedContractStorageVarIfSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { x = 5; if x { return x + 1; } } }"

def surfaceParsedContractStorageVarIfProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.storageStoreThenIfLoad
        (Expr.lit 0) (Expr.lit 5)
        (SurfaceStmt.returnStateExpr
          (StateExpr.add
            (StateExpr.load (Expr.lit 0))
            (StateExpr.pure (Expr.lit 1)))) }

def surfaceParsedContractStorageVarIfStoredState : State :=
  initialState.store (Expr.lit 0) (Expr.lit 5)

def surfaceParsedContractStorageVarIfFinalState : State :=
  surfaceParsedContractStorageVarIfStoredState.withReturn
    ((StateExpr.add
      (StateExpr.load (Expr.lit 0))
      (StateExpr.pure (Expr.lit 1))).eval
        surfaceParsedContractStorageVarIfStoredState)

theorem surfaceParsedContractStorageVarIfProgram_eval :
    surfaceParsedContractStorageVarIfProgram.eval initialState =
      Result.returned surfaceParsedContractStorageVarIfFinalState := by
  rfl

def surfaceParsedContractStorageVarIfArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact
    surfaceParsedContractStorageVarIfProgram

theorem surfaceParsedContractStorageVarIfArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedContractStorageVarIfFinalState).toSymYulResults := by
  simpa [surfaceParsedContractStorageVarIfArtifact,
    surfaceParsedContractStorageVarIfProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedContractStorageVarIfProgram initialState

theorem surfaceParsedContractStorageVarIfArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedContractStorageVarIfProgram

theorem surfaceParsedContractStorageVarIfArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractStorageVarIfArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedContractStorageVarIfProgram

def surfaceParsedSwitchBuiltinSource : String :=
  "mvp { switch 3 { case 1: return 9; case 2: return addmod(2, 3, 5); default: return 11; } }"

def surfaceParsedSwitchBuiltinProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.switchCases (Expr.lit 3)
        [ (1, SurfaceStmt.returnExpr (Expr.lit 9))
        , (2,
            SurfaceStmt.returnExpr
              (Expr.addmod (Expr.lit 2) (Expr.lit 3) (Expr.lit 5))) ]
        (SurfaceStmt.returnExpr (Expr.lit 11)) }

def surfaceParsedStoreThenSwitchLoadSource : String :=
  "mvp { sstore(0, 2 + 3); switch sload(0) { case 1: return 9; case 5: return sload(0); default: return 7; } }"

def surfaceParsedStoreThenSwitchLoadProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore
          (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3)))
        (SurfaceStmt.switchCases (Expr.add (Expr.lit 2) (Expr.lit 3))
          [ (1, SurfaceStmt.returnExpr (Expr.lit 9))
          , (5, SurfaceStmt.storageLoadReturn (Expr.lit 0)) ]
          (SurfaceStmt.returnExpr (Expr.lit 7))) }

theorem surfaceParsedStoreThenSwitchLoadProgram_eval :
    surfaceParsedStoreThenSwitchLoadProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceParsedStoreThenSwitchLoadArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoreThenSwitchLoadProgram

theorem surfaceParsedStoreThenSwitchLoadArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceParsedStoreThenSwitchLoadArtifact,
    surfaceParsedStoreThenSwitchLoadProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoreThenSwitchLoadProgram initialState

theorem surfaceParsedStoreThenSwitchLoadArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoreThenSwitchLoadProgram

theorem surfaceParsedStoreThenSwitchLoadArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoreThenSwitchLoadArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoreThenSwitchLoadProgram

def surfaceParsedBoundedWhileStorageSource : String :=
  "mvp { boundedWhile 2 1 { sstore(0, 2 + 3); } return sload(0); }"

def surfaceParsedBoundedWhileStorageProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.boundedWhile 2 (Expr.lit 1)
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))))
        (SurfaceStmt.storageLoadReturn (Expr.lit 0)) }

def surfaceParsedBoundedWhileSwitchSource : String :=
  "mvp { boundedWhile 1 1 { sstore(0, 4 + 5); } switch 2 { case 1: return 7; case 2: return sload(0); default: return 0; } }"

def surfaceParsedBoundedWhileSwitchProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.boundedWhile 1 (Expr.lit 1)
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 4) (Expr.lit 5))))
        (SurfaceStmt.switchCases (Expr.lit 2)
          [ (1, SurfaceStmt.returnExpr (Expr.lit 7))
          , (2, SurfaceStmt.storageLoadReturn (Expr.lit 0)) ]
          (SurfaceStmt.returnExpr (Expr.lit 0))) }

def surfaceParsedStateExprAddSource : String :=
  "mvp { return sload(0) + sload(1); }"

def surfaceParsedStateExprAddProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.returnStateExpr
        (StateExpr.add
          (StateExpr.load (Expr.lit 0))
          (StateExpr.load (Expr.lit 1))) }

def surfaceParsedStateExprAddFinalState : State :=
  initialState.withReturn
    (Core.Storage.addValue
      (initialState.load (Expr.lit 0))
      (initialState.load (Expr.lit 1)))

theorem surfaceParsedStateExprAddProgram_eval :
    surfaceParsedStateExprAddProgram.eval initialState =
      Result.returned surfaceParsedStateExprAddFinalState := by
  rfl

def surfaceParsedStateExprAddArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStateExprAddProgram

theorem surfaceParsedStateExprAddArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned surfaceParsedStateExprAddFinalState).toSymYulResults := by
  simpa [surfaceParsedStateExprAddArtifact,
    surfaceParsedStateExprAddProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStateExprAddProgram initialState

theorem surfaceParsedStateExprAddArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStateExprAddProgram

theorem surfaceParsedStateExprAddArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStateExprAddProgram

def surfaceParsedStoredStateExprAddSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) + sload(1); }"

def surfaceParsedStoredStateExprAddProgram : SurfaceProgram :=
  surfaceStorageExprAddProgram

theorem surfaceParsedStoredStateExprAddProgram_eval :
    surfaceParsedStoredStateExprAddProgram.eval initialState =
      Result.returned surfaceStorageExprAddFinalState := by
  rfl

def surfaceParsedStoredStateExprAddArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprAddProgram

theorem surfaceParsedStoredStateExprAddArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned surfaceStorageExprAddFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprAddArtifact,
    surfaceParsedStoredStateExprAddProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprAddProgram initialState

theorem surfaceParsedStoredStateExprAddArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprAddProgram

theorem surfaceParsedStoredStateExprAddArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprAddArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprAddProgram

def surfaceParsedStoredStateExprMulSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) * sload(1); }"

def surfaceParsedStoredStateExprMulProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 7))
          (SurfaceStmt.returnStateExpr
            (StateExpr.mul
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceParsedStoredStateExprMulFinalState : State :=
  ((initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 7)).withReturn
      (SolidCoreYulCore.FullYul.Value.word 35)

theorem surfaceParsedStoredStateExprMulProgram_eval :
    surfaceParsedStoredStateExprMulProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprMulFinalState := by
  rfl

def surfaceParsedStoredStateExprMulArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprMulProgram

theorem surfaceParsedStoredStateExprMulArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprMulFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprMulArtifact,
    surfaceParsedStoredStateExprMulProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprMulProgram initialState

theorem surfaceParsedStoredStateExprMulArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprMulProgram

theorem surfaceParsedStoredStateExprMulArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprMulArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprMulProgram

def surfaceParsedStoredStateExprEqSource : String :=
  "mvp { sstore(0, 5); sstore(1, 5); return sload(0) == sload(1); }"

def surfaceParsedStoredStateExprEqProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 5))
          (SurfaceStmt.returnStateExpr
            (StateExpr.eq
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceParsedStoredStateExprEqFinalState : State :=
  ((initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 5)).withReturn
      (SolidCoreYulCore.FullYul.Value.word 1)

theorem surfaceParsedStoredStateExprEqProgram_eval :
    surfaceParsedStoredStateExprEqProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprEqFinalState := by
  rfl

def surfaceParsedStoredStateExprEqArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprEqProgram

theorem surfaceParsedStoredStateExprEqArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprEqFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprEqArtifact,
    surfaceParsedStoredStateExprEqProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprEqProgram initialState

theorem surfaceParsedStoredStateExprEqArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprEqProgram

theorem surfaceParsedStoredStateExprEqArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprEqArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprEqProgram

def surfaceParsedStoredStateExprLtSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) < sload(1); }"

def surfaceParsedStoredStateExprLtProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 7))
          (SurfaceStmt.returnStateExpr
            (StateExpr.lt
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceParsedStoredStateExprLtFinalState : State :=
  ((initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 7)).withReturn
      (SolidCoreYulCore.FullYul.Value.word 1)

theorem surfaceParsedStoredStateExprLtProgram_eval :
    surfaceParsedStoredStateExprLtProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprLtFinalState := by
  rfl

def surfaceParsedStoredStateExprLtArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprLtProgram

theorem surfaceParsedStoredStateExprLtArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprLtFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprLtArtifact,
    surfaceParsedStoredStateExprLtProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprLtProgram initialState

theorem surfaceParsedStoredStateExprLtArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprLtProgram

theorem surfaceParsedStoredStateExprLtArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprLtArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprLtProgram

def surfaceParsedStoredStateExprGtSource : String :=
  "mvp { sstore(0, 7); sstore(1, 5); return sload(0) > sload(1); }"

def surfaceParsedStoredStateExprGtProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 7))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 5))
          (SurfaceStmt.returnStateExpr
            (StateExpr.gt
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceParsedStoredStateExprGtFinalState : State :=
  ((initialState.store (Expr.lit 0) (Expr.lit 7)).store
    (Expr.lit 1) (Expr.lit 5)).withReturn
      (SolidCoreYulCore.FullYul.Value.word 1)

theorem surfaceParsedStoredStateExprGtProgram_eval :
    surfaceParsedStoredStateExprGtProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprGtFinalState := by
  rfl

def surfaceParsedStoredStateExprGtArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprGtProgram

theorem surfaceParsedStoredStateExprGtArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprGtFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprGtArtifact,
    surfaceParsedStoredStateExprGtProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprGtProgram initialState

theorem surfaceParsedStoredStateExprGtArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprGtProgram

theorem surfaceParsedStoredStateExprGtArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprGtArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprGtProgram

def surfaceParsedStoredStateExprBitAndSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) & sload(1); }"

def surfaceParsedStoredStateExprBitAndProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 7))
          (SurfaceStmt.returnStateExpr
            (StateExpr.bitAnd
              (StateExpr.load (Expr.lit 0))
              (StateExpr.load (Expr.lit 1))))) }

def surfaceParsedStoredStateExprBitAndStoredState : State :=
  (initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 7)

def surfaceParsedStoredStateExprBitAndFinalState : State :=
  surfaceParsedStoredStateExprBitAndStoredState.withReturn
    (StateExpr.andValue
      (surfaceParsedStoredStateExprBitAndStoredState.load (Expr.lit 0))
      (surfaceParsedStoredStateExprBitAndStoredState.load (Expr.lit 1)))

theorem surfaceParsedStoredStateExprBitAndProgram_eval :
    surfaceParsedStoredStateExprBitAndProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprBitAndFinalState := by
  rfl

def surfaceParsedStoredStateExprBitAndArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprBitAndProgram

theorem surfaceParsedStoredStateExprBitAndArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprBitAndFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprBitAndArtifact,
    surfaceParsedStoredStateExprBitAndProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprBitAndProgram initialState

theorem surfaceParsedStoredStateExprBitAndArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprBitAndProgram

theorem surfaceParsedStoredStateExprBitAndArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprBitAndArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprBitAndProgram

def surfaceParsedStoredStateExprBinaryProgram (expr : StateExpr) :
    SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore (Expr.lit 1) (Expr.lit 7))
          (SurfaceStmt.returnStateExpr expr)) }

def surfaceParsedStoredStateExprBinaryStoredState : State :=
  (initialState.store (Expr.lit 0) (Expr.lit 5)).store
    (Expr.lit 1) (Expr.lit 7)

def surfaceParsedStoredStateExprBinaryFinalState
    (expr : StateExpr) : State :=
  surfaceParsedStoredStateExprBinaryStoredState.withReturn
    (expr.eval surfaceParsedStoredStateExprBinaryStoredState)

def surfaceParsedStoredStateExprBitOrSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) | sload(1); }"

def surfaceParsedStoredStateExprBitOrProgram : SurfaceProgram :=
  surfaceParsedStoredStateExprBinaryProgram
    (StateExpr.bitOr
      (StateExpr.load (Expr.lit 0))
      (StateExpr.load (Expr.lit 1)))

def surfaceParsedStoredStateExprBitOrFinalState : State :=
  surfaceParsedStoredStateExprBinaryFinalState
    (StateExpr.bitOr
      (StateExpr.load (Expr.lit 0))
      (StateExpr.load (Expr.lit 1)))

theorem surfaceParsedStoredStateExprBitOrProgram_eval :
    surfaceParsedStoredStateExprBitOrProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprBitOrFinalState := by
  rfl

def surfaceParsedStoredStateExprBitOrArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprBitOrProgram

theorem surfaceParsedStoredStateExprBitOrArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprBitOrFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprBitOrArtifact,
    surfaceParsedStoredStateExprBitOrProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprBitOrProgram initialState

theorem surfaceParsedStoredStateExprBitOrArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprBitOrProgram

theorem surfaceParsedStoredStateExprBitOrArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprBitOrArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprBitOrProgram

def surfaceParsedStoredStateExprBitXorSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) ^ sload(1); }"

def surfaceParsedStoredStateExprBitXorProgram : SurfaceProgram :=
  surfaceParsedStoredStateExprBinaryProgram
    (StateExpr.bitXor
      (StateExpr.load (Expr.lit 0))
      (StateExpr.load (Expr.lit 1)))

def surfaceParsedStoredStateExprBitXorFinalState : State :=
  surfaceParsedStoredStateExprBinaryFinalState
    (StateExpr.bitXor
      (StateExpr.load (Expr.lit 0))
      (StateExpr.load (Expr.lit 1)))

theorem surfaceParsedStoredStateExprBitXorProgram_eval :
    surfaceParsedStoredStateExprBitXorProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprBitXorFinalState := by
  rfl

def surfaceParsedStoredStateExprBitXorArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprBitXorProgram

theorem surfaceParsedStoredStateExprBitXorArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprBitXorFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprBitXorArtifact,
    surfaceParsedStoredStateExprBitXorProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprBitXorProgram initialState

theorem surfaceParsedStoredStateExprBitXorArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprBitXorProgram

theorem surfaceParsedStoredStateExprBitXorArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprBitXorArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprBitXorProgram

def surfaceParsedStoredStateExprNeSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) != sload(1); }"

def surfaceParsedStoredStateExprNeProgram : SurfaceProgram :=
  surfaceParsedStoredStateExprBinaryProgram
    (StateExpr.iszero
      (StateExpr.eq
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

def surfaceParsedStoredStateExprNeFinalState : State :=
  surfaceParsedStoredStateExprBinaryFinalState
    (StateExpr.iszero
      (StateExpr.eq
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

theorem surfaceParsedStoredStateExprNeProgram_eval :
    surfaceParsedStoredStateExprNeProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprNeFinalState := by
  rfl

def surfaceParsedStoredStateExprNeArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprNeProgram

theorem surfaceParsedStoredStateExprNeArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprNeFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprNeArtifact,
    surfaceParsedStoredStateExprNeProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprNeProgram initialState

theorem surfaceParsedStoredStateExprNeArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprNeProgram

theorem surfaceParsedStoredStateExprNeArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprNeArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprNeProgram

def surfaceParsedStoredStateExprLeSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) <= sload(1); }"

def surfaceParsedStoredStateExprLeProgram : SurfaceProgram :=
  surfaceParsedStoredStateExprBinaryProgram
    (StateExpr.iszero
      (StateExpr.gt
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

def surfaceParsedStoredStateExprLeFinalState : State :=
  surfaceParsedStoredStateExprBinaryFinalState
    (StateExpr.iszero
      (StateExpr.gt
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

theorem surfaceParsedStoredStateExprLeProgram_eval :
    surfaceParsedStoredStateExprLeProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprLeFinalState := by
  rfl

def surfaceParsedStoredStateExprLeArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprLeProgram

theorem surfaceParsedStoredStateExprLeArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprLeFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprLeArtifact,
    surfaceParsedStoredStateExprLeProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprLeProgram initialState

theorem surfaceParsedStoredStateExprLeArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprLeProgram

theorem surfaceParsedStoredStateExprLeArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprLeArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprLeProgram

def surfaceParsedStoredStateExprGeSource : String :=
  "mvp { sstore(0, 5); sstore(1, 7); return sload(0) >= sload(1); }"

def surfaceParsedStoredStateExprGeProgram : SurfaceProgram :=
  surfaceParsedStoredStateExprBinaryProgram
    (StateExpr.iszero
      (StateExpr.lt
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

def surfaceParsedStoredStateExprGeFinalState : State :=
  surfaceParsedStoredStateExprBinaryFinalState
    (StateExpr.iszero
      (StateExpr.lt
        (StateExpr.load (Expr.lit 0))
        (StateExpr.load (Expr.lit 1))))

theorem surfaceParsedStoredStateExprGeProgram_eval :
    surfaceParsedStoredStateExprGeProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprGeFinalState := by
  rfl

def surfaceParsedStoredStateExprGeArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprGeProgram

theorem surfaceParsedStoredStateExprGeArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprGeFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprGeArtifact,
    surfaceParsedStoredStateExprGeProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprGeProgram initialState

theorem surfaceParsedStoredStateExprGeArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprGeProgram

theorem surfaceParsedStoredStateExprGeArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprGeArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprGeProgram

def surfaceParsedStoredUnaryStateExprProgram (expr : StateExpr) :
    SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5))
        (SurfaceStmt.returnStateExpr expr) }

def surfaceParsedStoredUnaryStateExprStoredState : State :=
  initialState.store (Expr.lit 0) (Expr.lit 5)

def surfaceParsedStoredUnaryStateExprFinalState
    (expr : StateExpr) : State :=
  surfaceParsedStoredUnaryStateExprStoredState.withReturn
    (expr.eval surfaceParsedStoredUnaryStateExprStoredState)

def surfaceParsedStoredStateExprBitNotSource : String :=
  "mvp { sstore(0, 5); return not(sload(0)); }"

def surfaceParsedStoredStateExprBitNotProgram : SurfaceProgram :=
  surfaceParsedStoredUnaryStateExprProgram
    (StateExpr.bitNot (StateExpr.load (Expr.lit 0)))

def surfaceParsedStoredStateExprBitNotFinalState : State :=
  surfaceParsedStoredUnaryStateExprFinalState
    (StateExpr.bitNot (StateExpr.load (Expr.lit 0)))

theorem surfaceParsedStoredStateExprBitNotProgram_eval :
    surfaceParsedStoredStateExprBitNotProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprBitNotFinalState := by
  rfl

def surfaceParsedStoredStateExprBitNotArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprBitNotProgram

theorem surfaceParsedStoredStateExprBitNotArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprBitNotFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprBitNotArtifact,
    surfaceParsedStoredStateExprBitNotProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprBitNotProgram initialState

theorem surfaceParsedStoredStateExprBitNotArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprBitNotProgram

theorem surfaceParsedStoredStateExprBitNotArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprBitNotArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprBitNotProgram

def surfaceParsedStoredStateExprIszeroSource : String :=
  "mvp { sstore(0, 0); return iszero(sload(0)); }"

def surfaceParsedStoredStateExprIszeroProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 0))
        (SurfaceStmt.returnStateExpr
          (StateExpr.iszero (StateExpr.load (Expr.lit 0)))) }

def surfaceParsedStoredStateExprIszeroStoredState : State :=
  initialState.store (Expr.lit 0) (Expr.lit 0)

def surfaceParsedStoredStateExprIszeroFinalState : State :=
  surfaceParsedStoredStateExprIszeroStoredState.withReturn
    ((StateExpr.iszero (StateExpr.load (Expr.lit 0))).eval
      surfaceParsedStoredStateExprIszeroStoredState)

theorem surfaceParsedStoredStateExprIszeroProgram_eval :
    surfaceParsedStoredStateExprIszeroProgram.eval initialState =
      Result.returned surfaceParsedStoredStateExprIszeroFinalState := by
  rfl

def surfaceParsedStoredStateExprIszeroArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoredStateExprIszeroProgram

theorem surfaceParsedStoredStateExprIszeroArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned
        surfaceParsedStoredStateExprIszeroFinalState).toSymYulResults := by
  simpa [surfaceParsedStoredStateExprIszeroArtifact,
    surfaceParsedStoredStateExprIszeroProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoredStateExprIszeroProgram initialState

theorem surfaceParsedStoredStateExprIszeroArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoredStateExprIszeroProgram

theorem surfaceParsedStoredStateExprIszeroArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoredStateExprIszeroProgram

def surfaceParsedIfStorageReturnSource : String :=
  "mvp { if 1 { sstore(0, 8); } return sload(0); }"

def surfaceParsedIfStorageReturnProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.ifThen (Expr.lit 1)
          (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 8)))
        (SurfaceStmt.storageLoadReturn (Expr.lit 0)) }

def surfaceParsedIfStorageReturnFinalState : State :=
  let stored := initialState.store (Expr.lit 0) (Expr.lit 8)
  stored.withReturn (stored.load (Expr.lit 0))

theorem surfaceParsedIfStorageReturnProgram_eval :
    surfaceParsedIfStorageReturnProgram.eval initialState =
      Result.returned surfaceParsedIfStorageReturnFinalState := by
  rfl

def surfaceParsedIfStorageReturnArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedIfStorageReturnProgram

theorem surfaceParsedIfStorageReturnArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned surfaceParsedIfStorageReturnFinalState).toSymYulResults := by
  simpa [surfaceParsedIfStorageReturnArtifact,
    surfaceParsedIfStorageReturnProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedIfStorageReturnProgram initialState

theorem surfaceParsedIfStorageReturnArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedIfStorageReturnProgram

theorem surfaceParsedIfStorageReturnArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedIfStorageReturnArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedIfStorageReturnProgram

def surfaceParsedIfElseSource : String :=
  "mvp { if 0 { return 7; } else { return 11; } }"

def surfaceParsedIfElseProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.switchCases (Expr.lit 0)
        [(0, SurfaceStmt.returnExpr (Expr.lit 11))]
        (SurfaceStmt.returnExpr (Expr.lit 7)) }

def surfaceParsedIfElseFinalState : State :=
  initialState.withWordReturn 11

theorem surfaceParsedIfElseProgram_eval :
    surfaceParsedIfElseProgram.eval initialState =
      Result.returned surfaceParsedIfElseFinalState := by
  rfl

def surfaceParsedIfElseArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedIfElseProgram

theorem surfaceParsedIfElseArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned surfaceParsedIfElseFinalState).toSymYulResults := by
  simpa [surfaceParsedIfElseArtifact,
    surfaceParsedIfElseProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedIfElseProgram initialState

theorem surfaceParsedIfElseArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedIfElseProgram

theorem surfaceParsedIfElseArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedIfElseArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedIfElseProgram

def surfaceParsedStoreThenIfLoadSwitchSource : String :=
  "mvp { sstore(0, 2 + 3); if sload(0) { switch 2 { case 1: return 9; case 2: return sload(0); default: return 7; } } }"

def surfaceParsedStoreThenIfLoadSwitchProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.storageStoreThenIfLoad
        (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))
        (SurfaceStmt.switchCases (Expr.lit 2)
          [ (1, SurfaceStmt.returnExpr (Expr.lit 9))
          , (2, SurfaceStmt.storageLoadReturn (Expr.lit 0)) ]
          (SurfaceStmt.returnExpr (Expr.lit 7))) }

theorem surfaceParsedStoreThenIfLoadSwitchProgram_eval :
    surfaceParsedStoreThenIfLoadSwitchProgram.eval initialState =
      Result.returned switchStorageBuiltinFinalState := by
  rfl

def surfaceParsedStoreThenIfLoadSwitchArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoreThenIfLoadSwitchProgram

theorem surfaceParsedStoreThenIfLoadSwitchArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.returned switchStorageBuiltinFinalState).toSymYulResults := by
  simpa [surfaceParsedStoreThenIfLoadSwitchArtifact,
    surfaceParsedStoreThenIfLoadSwitchProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoreThenIfLoadSwitchProgram initialState

theorem surfaceParsedStoreThenIfLoadSwitchArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoreThenIfLoadSwitchProgram

theorem surfaceParsedStoreThenIfLoadSwitchArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoreThenIfLoadSwitchArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoreThenIfLoadSwitchProgram

def surfaceParsedStoreThenIfLoadSkippedSource : String :=
  "mvp { sstore(0, 0); if sload(0) { return 9; } }"

def surfaceParsedStoreThenIfLoadSkippedProgram : SurfaceProgram :=
  surfaceStoreThenIfLoadSkippedProgram

theorem surfaceParsedStoreThenIfLoadSkippedProgram_eval :
    surfaceParsedStoreThenIfLoadSkippedProgram.eval initialState =
      Result.normal surfaceStoreThenIfLoadSkippedFinalState := by
  rfl

def surfaceParsedStoreThenIfLoadSkippedArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedStoreThenIfLoadSkippedProgram

theorem surfaceParsedStoreThenIfLoadSkippedArtifact_dynamic_sound :
    SolidCoreYulCore.SymYul.evalStmtFuel
        surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
        initialState.toConfig
        surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt =
      (Result.normal surfaceStoreThenIfLoadSkippedFinalState).toSymYulResults := by
  simpa [surfaceParsedStoreThenIfLoadSkippedArtifact,
    surfaceParsedStoreThenIfLoadSkippedProgram_eval] using
    compileSurfaceProgramArtifact_dynamic_sound
      surfaceParsedStoreThenIfLoadSkippedProgram initialState

theorem surfaceParsedStoreThenIfLoadSkippedArtifact_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_staticChecked
      surfaceParsedStoreThenIfLoadSkippedProgram

theorem surfaceParsedStoreThenIfLoadSkippedArtifact_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoreThenIfLoadSkippedArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceProgramArtifact_accepted_currentSolidCore
      surfaceParsedStoreThenIfLoadSkippedProgram

def surfaceParsedFunctionIfStorageReturnSource : String :=
  "function main() returns (uint256) { if 1 { sstore(0, 8); } return sload(0); }"

def surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource : String :=
  "function main() public returns (uint256) { sstore(0, 2 + 3); if sload(0) { switch 2 { case 1: return 9; case 2: return sload(0); default: return 7; } } }"

def surfaceParsedContractIfStorageReturnSource : String :=
  "contract Main { function main() public returns (uint256) { if 1 { sstore(0, 8); } return sload(0); } }"

def surfaceProgramPrefix : String :=
  "mvp { "

def surfaceProgramSuffix : String :=
  " }"

def surfaceReturnPrefix : String :=
  "return "

def surfaceReturnSuffix : String :=
  ";"

def surfaceReturnSloadPrefix : String :=
  "return sload("

def surfaceReturnSloadSuffix : String :=
  ");"

def surfaceStorageVarAssignPrefix : String :=
  "x = "

def surfaceStorageVarAssignSwitchMiddle : String :=
  "; switch "

def surfaceStorageVarAssignIfMiddle : String :=
  "; if "

def surfaceSstorePrefix : String :=
  "sstore("

def surfaceSstoreReturnSloadMiddle : String :=
  "); return sload("

def surfaceSstoreReturnSloadSuffix : String :=
  ");"

def surfaceSstoreSuffix : String :=
  ");"

def surfaceSwitchPrefix : String :=
  "switch "

def surfaceSwitchOpen : String :=
  " { "

def surfaceSwitchSuffix : String :=
  " }"

def surfaceSwitchCasePrefix : String :=
  "case "

def surfaceSwitchCaseMiddle : String :=
  ": "

def surfaceSwitchDefaultMiddle : String :=
  " default: "

def surfaceBoundedWhilePrefix : String :=
  "boundedWhile "

def surfaceBoundedWhileBodyOpen : String :=
  " { "

def surfaceBoundedWhileBodyClose : String :=
  " } "

def surfaceIfPrefix : String :=
  "if "

def surfaceIfBodyOpen : String :=
  " { "

def surfaceIfBodyClose : String :=
  " } "

def surfaceIfElseMiddle : String :=
  " } else { "

def surfaceIfElseSuffix : String :=
  " }"

def surfaceFunctionPrefix : String :=
  "function main() returns (uint256) { "

def surfacePublicFunctionPrefix : String :=
  "function main() public returns (uint256) { "

def surfaceFunctionSuffix : String :=
  " }"

def surfaceContractFunctionPrefix : String :=
  "contract Main { function main() public returns (uint256) { "

def surfaceContractStorageFunctionPrefix : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { "

def surfaceContractFunctionSuffix : String :=
  " } }"

def stripSurfaceProgramBody? (source : String) : Option String :=
  let trimmed := source.trimAscii.toString
  if trimmed.startsWith surfaceProgramPrefix &&
      trimmed.endsWith surfaceProgramSuffix then
    some
      ((((trimmed.drop surfaceProgramPrefix.length).dropEnd
        surfaceProgramSuffix.length).trimAscii).toString)
  else
    none

def stripSurfaceFunctionBody? (source : String) : Option String :=
  let trimmed := source.trimAscii.toString
  if trimmed.startsWith surfaceFunctionPrefix &&
      trimmed.endsWith surfaceFunctionSuffix then
    some
      ((((trimmed.drop surfaceFunctionPrefix.length).dropEnd
        surfaceFunctionSuffix.length).trimAscii).toString)
  else if trimmed.startsWith surfacePublicFunctionPrefix &&
      trimmed.endsWith surfaceFunctionSuffix then
    some
      ((((trimmed.drop surfacePublicFunctionPrefix.length).dropEnd
        surfaceFunctionSuffix.length).trimAscii).toString)
  else if trimmed.startsWith surfaceContractFunctionPrefix &&
      trimmed.endsWith surfaceContractFunctionSuffix then
    some
      ((((trimmed.drop surfaceContractFunctionPrefix.length).dropEnd
        surfaceContractFunctionSuffix.length).trimAscii).toString)
  else if trimmed.startsWith surfaceContractStorageFunctionPrefix &&
      trimmed.endsWith surfaceContractFunctionSuffix then
    some
      ((((trimmed.drop surfaceContractStorageFunctionPrefix.length).dropEnd
        surfaceContractFunctionSuffix.length).trimAscii).toString)
  else
    none

def parseSurfaceExpr? (literal : String) : Option Expr :=
  match SolidCore.Concrete.parseGeneratedReturnExpr?
      (SolidCore.Concrete.returnLiteralSource literal) with
  | some expr => some expr
  | none =>
      SolidCore.Concrete.parseGeneratedBoolReturnExpr?
        (SolidCore.Concrete.returnBoolSource literal)

def stripSurfaceReturn? (body : String) : Option String :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceReturnPrefix &&
      trimmed.endsWith surfaceReturnSuffix then
    some
      ((((trimmed.drop surfaceReturnPrefix.length).dropEnd
        surfaceReturnSuffix.length).trimAscii).toString)
  else
    none

def stripSurfaceReturnSload? (body : String) : Option String :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceReturnSloadPrefix &&
      trimmed.endsWith surfaceReturnSloadSuffix then
    some
      ((((trimmed.drop surfaceReturnSloadPrefix.length).dropEnd
        surfaceReturnSloadSuffix.length).trimAscii).toString)
  else
    none

def stripSurfaceSloadExpr? (literal : String) : Option String :=
  let trimmed := literal.trimAscii.toString
  if trimmed.startsWith "sload(" && trimmed.endsWith ")" then
    some ((((trimmed.drop "sload(".length).dropEnd 1).trimAscii).toString)
  else
    none

def stripSurfaceStateUnary? (name literal : String) : Option String :=
  let trimmed := literal.trimAscii.toString
  let callPrefix := name ++ "("
  if trimmed.startsWith callPrefix && trimmed.endsWith ")" then
    some ((((trimmed.drop callPrefix.length).dropEnd 1).trimAscii).toString)
  else
    none

structure SurfaceLocalHandle where
  index : Nat
  deriving DecidableEq, Repr

def SurfaceLocalHandle.first : SurfaceLocalHandle :=
  { index := 0 }

inductive SurfaceTy where
  | uint256 : SurfaceTy
  deriving DecidableEq, Repr

structure SurfaceLocalInfo where
  handle : SurfaceLocalHandle
  ty : SurfaceTy
  deriving DecidableEq, Repr

def SurfaceLocalInfo.uint256
    (handle : SurfaceLocalHandle) : SurfaceLocalInfo :=
  { handle := handle, ty := SurfaceTy.uint256 }

structure SurfaceStorageInfo where
  slot : Expr
  ty : SurfaceTy
  deriving DecidableEq, Repr

def SurfaceStorageInfo.uint256 (slot : Expr) : SurfaceStorageInfo :=
  { slot := slot, ty := SurfaceTy.uint256 }

inductive SurfaceWordRef where
  | local : SurfaceLocalInfo -> SurfaceWordRef
  | storage : SurfaceStorageInfo -> SurfaceWordRef
  deriving DecidableEq, Repr

inductive SurfaceResolvedLValue where
  | local : SurfaceLocalInfo -> SurfaceResolvedLValue
  | storage : SurfaceStorageInfo -> SurfaceResolvedLValue
  deriving DecidableEq, Repr

inductive SurfaceWordBinaryOp where
  | add : SurfaceWordBinaryOp
  | sub : SurfaceWordBinaryOp
  | mul : SurfaceWordBinaryOp
  | eq : SurfaceWordBinaryOp
  | lt : SurfaceWordBinaryOp
  | gt : SurfaceWordBinaryOp
  | bitAnd : SurfaceWordBinaryOp
  | bitOr : SurfaceWordBinaryOp
  | bitXor : SurfaceWordBinaryOp
  deriving DecidableEq, Repr

def SurfaceWordBinaryOp.toStateExpr
    (op : SurfaceWordBinaryOp) (lhs rhs : StateExpr) : StateExpr :=
  match op with
  | SurfaceWordBinaryOp.add => StateExpr.add lhs rhs
  | SurfaceWordBinaryOp.sub => StateExpr.sub lhs rhs
  | SurfaceWordBinaryOp.mul => StateExpr.mul lhs rhs
  | SurfaceWordBinaryOp.eq => StateExpr.eq lhs rhs
  | SurfaceWordBinaryOp.lt => StateExpr.lt lhs rhs
  | SurfaceWordBinaryOp.gt => StateExpr.gt lhs rhs
  | SurfaceWordBinaryOp.bitAnd => StateExpr.bitAnd lhs rhs
  | SurfaceWordBinaryOp.bitOr => StateExpr.bitOr lhs rhs
  | SurfaceWordBinaryOp.bitXor => StateExpr.bitXor lhs rhs

def SurfaceWordBinaryOp.toPureExpr
    (op : SurfaceWordBinaryOp) (lhs rhs : Expr) : Expr :=
  match op with
  | SurfaceWordBinaryOp.add => Expr.add lhs rhs
  | SurfaceWordBinaryOp.sub => Expr.sub lhs rhs
  | SurfaceWordBinaryOp.mul => Expr.mul lhs rhs
  | SurfaceWordBinaryOp.eq => Expr.eq lhs rhs
  | SurfaceWordBinaryOp.lt => Expr.lt lhs rhs
  | SurfaceWordBinaryOp.gt => Expr.gt lhs rhs
  | SurfaceWordBinaryOp.bitAnd => Expr.bitAnd lhs rhs
  | SurfaceWordBinaryOp.bitOr => Expr.bitOr lhs rhs
  | SurfaceWordBinaryOp.bitXor => Expr.bitXor lhs rhs

inductive SurfaceWordUnaryOp where
  | bitNot : SurfaceWordUnaryOp
  | iszero : SurfaceWordUnaryOp
  deriving DecidableEq, Repr

def SurfaceWordUnaryOp.toStateExpr
    (op : SurfaceWordUnaryOp) (expr : StateExpr) : StateExpr :=
  match op with
  | SurfaceWordUnaryOp.bitNot => StateExpr.bitNot expr
  | SurfaceWordUnaryOp.iszero => StateExpr.iszero expr

def SurfaceWordUnaryOp.toPureExpr
    (op : SurfaceWordUnaryOp) (expr : Expr) : Expr :=
  match op with
  | SurfaceWordUnaryOp.bitNot => Expr.bitNot expr
  | SurfaceWordUnaryOp.iszero => Expr.iszero expr

inductive SurfaceResolvedWordExpr where
  | pure : Expr -> SurfaceResolvedWordExpr
  | local : SurfaceLocalInfo -> SurfaceResolvedWordExpr
  | storageLoad : SurfaceStorageInfo -> SurfaceResolvedWordExpr
  | binary :
      SurfaceWordBinaryOp -> SurfaceResolvedWordExpr ->
        SurfaceResolvedWordExpr -> SurfaceResolvedWordExpr
  | unary :
      SurfaceWordUnaryOp -> SurfaceResolvedWordExpr ->
        SurfaceResolvedWordExpr
  deriving DecidableEq, Repr

abbrev SurfaceResolvedWordExpr.add
    (lhs rhs : SurfaceResolvedWordExpr) : SurfaceResolvedWordExpr :=
  SurfaceResolvedWordExpr.binary SurfaceWordBinaryOp.add lhs rhs

abbrev SurfaceResolvedWordExpr.mul
    (lhs rhs : SurfaceResolvedWordExpr) : SurfaceResolvedWordExpr :=
  SurfaceResolvedWordExpr.binary SurfaceWordBinaryOp.mul lhs rhs

abbrev SurfaceResolvedWordExpr.iszero
    (expr : SurfaceResolvedWordExpr) : SurfaceResolvedWordExpr :=
  SurfaceResolvedWordExpr.unary SurfaceWordUnaryOp.iszero expr

inductive SurfaceNamedWordExpr where
  | pure : Expr -> SurfaceNamedWordExpr
  | ident : String -> SurfaceNamedWordExpr
  | binary :
      SurfaceWordBinaryOp -> SurfaceNamedWordExpr ->
        SurfaceNamedWordExpr -> SurfaceNamedWordExpr
  | unary :
      SurfaceWordUnaryOp -> SurfaceNamedWordExpr -> SurfaceNamedWordExpr
  deriving DecidableEq, Repr

abbrev SurfaceNamedWordExpr.add
    (lhs rhs : SurfaceNamedWordExpr) : SurfaceNamedWordExpr :=
  SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.add lhs rhs

abbrev SurfaceNamedWordExpr.mul
    (lhs rhs : SurfaceNamedWordExpr) : SurfaceNamedWordExpr :=
  SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.mul lhs rhs

abbrev SurfaceNamedWordExpr.iszero
    (expr : SurfaceNamedWordExpr) : SurfaceNamedWordExpr :=
  SurfaceNamedWordExpr.unary SurfaceWordUnaryOp.iszero expr

inductive SurfaceNamedLValue where
  | ident : String -> SurfaceNamedLValue
  deriving DecidableEq, Repr

def SurfaceWordRef.toLValue : SurfaceWordRef -> SurfaceResolvedLValue
  | SurfaceWordRef.local info => SurfaceResolvedLValue.local info
  | SurfaceWordRef.storage info => SurfaceResolvedLValue.storage info

def SurfaceWordRef.toRValue : SurfaceWordRef -> SurfaceResolvedWordExpr
  | SurfaceWordRef.local info => SurfaceResolvedWordExpr.local info
  | SurfaceWordRef.storage info => SurfaceResolvedWordExpr.storageLoad info

structure SurfaceLocalValueBinding where
  info : SurfaceLocalInfo
  value : Expr
  deriving DecidableEq, Repr

abbrev SurfaceLocalValueEnv := List SurfaceLocalValueBinding

namespace SurfaceLocalValueEnv

def lookup? : SurfaceLocalValueEnv -> SurfaceLocalInfo -> Option Expr
  | [], _ => none
  | binding :: rest, info =>
      if info = binding.info then
        some binding.value
      else
        lookup? rest info

def push
    (info : SurfaceLocalInfo) (value : Expr)
    (env : SurfaceLocalValueEnv) : SurfaceLocalValueEnv :=
  { info := info, value := value } :: env

def single
    (info : SurfaceLocalInfo) (value : Expr) : SurfaceLocalValueEnv :=
  push info value []

theorem lookup?_push_self
    (info : SurfaceLocalInfo) (value : Expr)
    (env : SurfaceLocalValueEnv) :
    SurfaceLocalValueEnv.lookup?
        (SurfaceLocalValueEnv.push info value env) info =
      some value := by
  simp [SurfaceLocalValueEnv.lookup?, SurfaceLocalValueEnv.push]

theorem lookup?_push_other
    {pushed info : SurfaceLocalInfo} {value : Expr}
    (env : SurfaceLocalValueEnv) (hNe : info ≠ pushed) :
    SurfaceLocalValueEnv.lookup?
        (SurfaceLocalValueEnv.push pushed value env) info =
      SurfaceLocalValueEnv.lookup? env info := by
  simp [SurfaceLocalValueEnv.lookup?, SurfaceLocalValueEnv.push,
    if_neg hNe]

def update? :
    SurfaceLocalValueEnv -> SurfaceLocalInfo -> Expr ->
      Option SurfaceLocalValueEnv
  | [], _, _ => none
  | binding :: rest, info, value =>
      if info = binding.info then
        some ({ binding with value := value } :: rest)
      else
        match update? rest info value with
        | some rest' => some (binding :: rest')
        | none => none

theorem update?_push_self
    (info : SurfaceLocalInfo) (oldValue newValue : Expr)
    (env : SurfaceLocalValueEnv) :
    SurfaceLocalValueEnv.update?
        (SurfaceLocalValueEnv.push info oldValue env)
        info newValue =
      some (SurfaceLocalValueEnv.push info newValue env) := by
  simp [SurfaceLocalValueEnv.update?, SurfaceLocalValueEnv.push]

end SurfaceLocalValueEnv

def SurfaceResolvedWordExpr.toStateExpr? :
    SurfaceResolvedWordExpr -> Option StateExpr
  | SurfaceResolvedWordExpr.pure expr => some (StateExpr.pure expr)
  | SurfaceResolvedWordExpr.local _ => none
  | SurfaceResolvedWordExpr.storageLoad info =>
      some (StateExpr.load info.slot)
  | SurfaceResolvedWordExpr.binary op lhs rhs =>
      match lhs.toStateExpr?, rhs.toStateExpr? with
      | some lhsExpr, some rhsExpr =>
          some (op.toStateExpr lhsExpr rhsExpr)
      | _, _ => none
  | SurfaceResolvedWordExpr.unary op expr =>
      match expr.toStateExpr? with
      | some stateExpr => some (op.toStateExpr stateExpr)
      | none => none

def SurfaceResolvedWordExpr.toStateExprWithLocals?
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedWordExpr -> Option StateExpr
  | SurfaceResolvedWordExpr.pure expr => some (StateExpr.pure expr)
  | SurfaceResolvedWordExpr.local info =>
      match SurfaceLocalValueEnv.lookup? locals info with
      | some value => some (StateExpr.pure value)
      | none => none
  | SurfaceResolvedWordExpr.storageLoad info =>
      some (StateExpr.load info.slot)
  | SurfaceResolvedWordExpr.binary op lhs rhs =>
      match lhs.toStateExprWithLocals? locals,
          rhs.toStateExprWithLocals? locals with
      | some lhsExpr, some rhsExpr =>
          some (op.toStateExpr lhsExpr rhsExpr)
      | _, _ => none
  | SurfaceResolvedWordExpr.unary op expr =>
      match expr.toStateExprWithLocals? locals with
      | some stateExpr => some (op.toStateExpr stateExpr)
      | none => none

def SurfaceResolvedWordExpr.toStateExprWithLocal?
    (localInfo : SurfaceLocalInfo) (localValue : Expr)
    (expr : SurfaceResolvedWordExpr) : Option StateExpr :=
  expr.toStateExprWithLocals?
    (SurfaceLocalValueEnv.single localInfo localValue)

def SurfaceResolvedWordExpr.toPureExpr? :
    SurfaceResolvedWordExpr -> Option Expr
  | SurfaceResolvedWordExpr.pure expr => some expr
  | SurfaceResolvedWordExpr.local _ => none
  | SurfaceResolvedWordExpr.storageLoad _ => none
  | SurfaceResolvedWordExpr.binary op lhs rhs =>
      match lhs.toPureExpr?, rhs.toPureExpr? with
      | some lhsExpr, some rhsExpr =>
          some (op.toPureExpr lhsExpr rhsExpr)
      | _, _ => none
  | SurfaceResolvedWordExpr.unary op expr =>
      match expr.toPureExpr? with
      | some pureExpr => some (op.toPureExpr pureExpr)
      | none => none

def SurfaceResolvedWordExpr.toPureExprWithLocals?
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedWordExpr -> Option Expr
  | SurfaceResolvedWordExpr.pure expr => some expr
  | SurfaceResolvedWordExpr.local info =>
      SurfaceLocalValueEnv.lookup? locals info
  | SurfaceResolvedWordExpr.storageLoad _ => none
  | SurfaceResolvedWordExpr.binary op lhs rhs =>
      match lhs.toPureExprWithLocals? locals,
          rhs.toPureExprWithLocals? locals with
      | some lhsExpr, some rhsExpr =>
          some (op.toPureExpr lhsExpr rhsExpr)
      | _, _ => none
  | SurfaceResolvedWordExpr.unary op expr =>
      match expr.toPureExprWithLocals? locals with
      | some pureExpr => some (op.toPureExpr pureExpr)
      | none => none

def SurfaceResolvedWordExpr.toPureExprWithLocal?
    (localInfo : SurfaceLocalInfo) (localValue : Expr)
    (expr : SurfaceResolvedWordExpr) : Option Expr :=
  expr.toPureExprWithLocals?
    (SurfaceLocalValueEnv.single localInfo localValue)

structure SurfaceNameScope where
  localWord? : String -> Option SurfaceLocalInfo

def SurfaceNameScope.empty : SurfaceNameScope :=
  { localWord? := fun _ => none }

def SurfaceNameScope.singleLocal
    (name : String) (handle : SurfaceLocalHandle) : SurfaceNameScope :=
  { localWord? := fun candidate =>
      if candidate = name then
        some (SurfaceLocalInfo.uint256 handle)
      else
        none }

structure SurfaceNameEnv where
  localScopes : List SurfaceNameScope
  storageInfo? : String -> Option SurfaceStorageInfo

def SurfaceNameEnv.lookupStorageSlot?
    (env : SurfaceNameEnv) (name : String) : Option Expr :=
  match env.storageInfo? name with
  | some info => some info.slot
  | none => none

def SurfaceNameEnv.lookupStorageInfo?
    (env : SurfaceNameEnv) (name : String) :
    Option SurfaceStorageInfo :=
  env.storageInfo? name

def SurfaceNameEnv.lookupLocalWordInScopes? :
    List SurfaceNameScope -> String -> Option SurfaceLocalInfo
  | [], _ => none
  | scope :: rest, name =>
      match scope.localWord? name with
      | some value => some value
      | none =>
          SurfaceNameEnv.lookupLocalWordInScopes? rest name

def SurfaceNameEnv.lookupLocalWord?
    (env : SurfaceNameEnv) (name : String) :
    Option SurfaceLocalInfo :=
  SurfaceNameEnv.lookupLocalWordInScopes? env.localScopes name

def SurfaceNameEnv.lookupWord?
    (env : SurfaceNameEnv) (name : String) : Option SurfaceWordRef :=
  match SurfaceNameEnv.lookupLocalWord? env name with
  | some handle => some (SurfaceWordRef.local handle)
  | none =>
      match SurfaceNameEnv.lookupStorageInfo? env name with
      | some info => some (SurfaceWordRef.storage info)
      | none => none

def SurfaceNameEnv.resolveIdentLValue?
    (env : SurfaceNameEnv) (name : String) :
    Option SurfaceResolvedLValue :=
  match SurfaceNameEnv.lookupWord? env name with
  | some ref => some ref.toLValue
  | none => none

def SurfaceNameEnv.resolveIdentRValue?
    (env : SurfaceNameEnv) (name : String) :
    Option SurfaceResolvedWordExpr :=
  match SurfaceNameEnv.lookupWord? env name with
  | some ref => some ref.toRValue
  | none => none

def SurfaceNamedLValue.resolve?
    (env : SurfaceNameEnv) : SurfaceNamedLValue ->
    Option SurfaceResolvedLValue
  | SurfaceNamedLValue.ident name =>
      SurfaceNameEnv.resolveIdentLValue? env name

def SurfaceNamedWordExpr.resolve?
    (env : SurfaceNameEnv) : SurfaceNamedWordExpr ->
    Option SurfaceResolvedWordExpr
  | SurfaceNamedWordExpr.pure expr =>
      some (SurfaceResolvedWordExpr.pure expr)
  | SurfaceNamedWordExpr.ident name =>
      SurfaceNameEnv.resolveIdentRValue? env name
  | SurfaceNamedWordExpr.binary op lhs rhs =>
      match lhs.resolve? env, rhs.resolve? env with
      | some resolvedLhs, some resolvedRhs =>
          some (SurfaceResolvedWordExpr.binary op resolvedLhs resolvedRhs)
      | _, _ => none
  | SurfaceNamedWordExpr.unary op expr =>
      match expr.resolve? env with
      | some resolvedExpr =>
          some (SurfaceResolvedWordExpr.unary op resolvedExpr)
      | none => none

def SurfaceNameEnv.pushScope
    (env : SurfaceNameEnv) (scope : SurfaceNameScope) :
    SurfaceNameEnv :=
  { env with localScopes := scope :: env.localScopes }

def SurfaceNameEnv.nextLocalHandle
    (env : SurfaceNameEnv) : SurfaceLocalHandle :=
  { index := env.localScopes.length }

theorem SurfaceNameEnv.nextLocalHandle_pushScope
    (env : SurfaceNameEnv) (scope : SurfaceNameScope) :
    SurfaceNameEnv.nextLocalHandle (env.pushScope scope) =
      { index := env.localScopes.length.succ } := by
  rfl

def SurfaceNameEnv.empty : SurfaceNameEnv :=
  { localScopes := [], storageInfo? := fun _ => none }

def SurfaceNameEnv.singleStorage
    (name : String) (slot : Expr) : SurfaceNameEnv :=
  { localScopes := []
    storageInfo? := fun candidate =>
      if candidate = name then
        some (SurfaceStorageInfo.uint256 slot)
      else
        none }

theorem SurfaceNameEnv.nextLocalHandle_singleStorage
    (name : String) (slot : Expr) :
    SurfaceNameEnv.nextLocalHandle
        (SurfaceNameEnv.singleStorage name slot) =
      SurfaceLocalHandle.first := by
  rfl

theorem SurfaceNameEnv.lookupWord?_push_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNameEnv.lookupWord?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        name =
      some
        (SurfaceWordRef.local
          (SurfaceLocalInfo.uint256 handle)) := by
  dsimp [SurfaceNameEnv.lookupWord?,
    SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.lookupStorageInfo?,
    SurfaceNameEnv.pushScope,
    SurfaceNameScope.singleLocal]
  rw [if_pos rfl]

theorem SurfaceNameEnv.lookupWord?_push_local_other
    (env : SurfaceNameEnv) {bound query : String}
    (handle : SurfaceLocalHandle) (hNe : query ≠ bound) :
    SurfaceNameEnv.lookupWord?
        (env.pushScope
          (SurfaceNameScope.singleLocal bound handle))
        query =
      SurfaceNameEnv.lookupWord? env query := by
  dsimp [SurfaceNameEnv.lookupWord?,
    SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.lookupStorageInfo?,
    SurfaceNameEnv.pushScope,
    SurfaceNameScope.singleLocal]
  rw [if_neg hNe]

theorem SurfaceNameEnv.resolveIdentLValue?_push_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNameEnv.resolveIdentLValue?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        name =
      some
        (SurfaceResolvedLValue.local
          (SurfaceLocalInfo.uint256 handle)) := by
  dsimp [SurfaceNameEnv.resolveIdentLValue?]
  rw [SurfaceNameEnv.lookupWord?_push_local_self]
  rfl

theorem SurfaceNameEnv.resolveIdentRValue?_push_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNameEnv.resolveIdentRValue?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        name =
      some
        (SurfaceResolvedWordExpr.local
          (SurfaceLocalInfo.uint256 handle)) := by
  dsimp [SurfaceNameEnv.resolveIdentRValue?]
  rw [SurfaceNameEnv.lookupWord?_push_local_self]
  rfl

theorem SurfaceNameEnv.lookupWord?_single_storage_self
    (name : String) (slot : Expr) :
    SurfaceNameEnv.lookupWord?
        (SurfaceNameEnv.singleStorage name slot)
        name =
      some
        (SurfaceWordRef.storage
          (SurfaceStorageInfo.uint256 slot)) := by
  dsimp [SurfaceNameEnv.lookupWord?,
    SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.lookupStorageInfo?,
    SurfaceNameEnv.singleStorage]
  rw [if_pos rfl]

theorem SurfaceNameEnv.lookupWord?_single_storage_other
    {bound query : String} (slot : Expr) (hNe : query ≠ bound) :
    SurfaceNameEnv.lookupWord?
        (SurfaceNameEnv.singleStorage bound slot)
        query =
      none := by
  dsimp [SurfaceNameEnv.lookupWord?,
    SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.lookupStorageInfo?,
    SurfaceNameEnv.singleStorage]
  rw [if_neg hNe]

theorem SurfaceNameEnv.resolveIdentLValue?_single_storage_self
    (name : String) (slot : Expr) :
    SurfaceNameEnv.resolveIdentLValue?
        (SurfaceNameEnv.singleStorage name slot)
        name =
      some
        (SurfaceResolvedLValue.storage
          (SurfaceStorageInfo.uint256 slot)) := by
  dsimp [SurfaceNameEnv.resolveIdentLValue?]
  rw [SurfaceNameEnv.lookupWord?_single_storage_self]
  rfl

theorem SurfaceNameEnv.resolveIdentRValue?_single_storage_self
    (name : String) (slot : Expr) :
    SurfaceNameEnv.resolveIdentRValue?
        (SurfaceNameEnv.singleStorage name slot)
        name =
      some
        (SurfaceResolvedWordExpr.storageLoad
          (SurfaceStorageInfo.uint256 slot)) := by
  dsimp [SurfaceNameEnv.resolveIdentRValue?]
  rw [SurfaceNameEnv.lookupWord?_single_storage_self]
  rfl

theorem SurfaceNamedWordExpr.resolve?_pure
    (env : SurfaceNameEnv) (expr : Expr) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.pure expr) =
      some (SurfaceResolvedWordExpr.pure expr) := by
  rfl

theorem SurfaceNamedWordExpr.resolve?_ident_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNamedWordExpr.resolve?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedWordExpr.ident name) =
      some
        (SurfaceResolvedWordExpr.local
          (SurfaceLocalInfo.uint256 handle)) := by
  dsimp [SurfaceNamedWordExpr.resolve?]
  rw [SurfaceNameEnv.resolveIdentRValue?_push_local_self]

theorem SurfaceNamedWordExpr.resolve?_ident_storage_self
    (name : String) (slot : Expr) :
    SurfaceNamedWordExpr.resolve?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedWordExpr.ident name) =
      some
        (SurfaceResolvedWordExpr.storageLoad
          (SurfaceStorageInfo.uint256 slot)) := by
  dsimp [SurfaceNamedWordExpr.resolve?]
  rw [SurfaceNameEnv.resolveIdentRValue?_single_storage_self]

theorem SurfaceNamedWordExpr.resolve?_binary
    {env : SurfaceNameEnv} {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceNamedWordExpr}
    {resolvedLhs resolvedRhs : SurfaceResolvedWordExpr}
    (hLhs : lhs.resolve? env = some resolvedLhs)
    (hRhs : rhs.resolve? env = some resolvedRhs) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.binary op lhs rhs) =
      some (SurfaceResolvedWordExpr.binary op resolvedLhs resolvedRhs) := by
  dsimp [SurfaceNamedWordExpr.resolve?]
  rw [hLhs, hRhs]

theorem SurfaceNamedWordExpr.resolve?_add
    {env : SurfaceNameEnv} {lhs rhs : SurfaceNamedWordExpr}
    {resolvedLhs resolvedRhs : SurfaceResolvedWordExpr}
    (hLhs : lhs.resolve? env = some resolvedLhs)
    (hRhs : rhs.resolve? env = some resolvedRhs) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.add lhs rhs) =
      some (SurfaceResolvedWordExpr.add resolvedLhs resolvedRhs) := by
  exact SurfaceNamedWordExpr.resolve?_binary hLhs hRhs

theorem SurfaceNamedWordExpr.resolve?_mul
    {env : SurfaceNameEnv} {lhs rhs : SurfaceNamedWordExpr}
    {resolvedLhs resolvedRhs : SurfaceResolvedWordExpr}
    (hLhs : lhs.resolve? env = some resolvedLhs)
    (hRhs : rhs.resolve? env = some resolvedRhs) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.mul lhs rhs) =
      some (SurfaceResolvedWordExpr.mul resolvedLhs resolvedRhs) := by
  exact SurfaceNamedWordExpr.resolve?_binary hLhs hRhs

theorem SurfaceNamedWordExpr.resolve?_unary
    {env : SurfaceNameEnv} {op : SurfaceWordUnaryOp}
    {expr : SurfaceNamedWordExpr}
    {resolvedExpr : SurfaceResolvedWordExpr}
    (hExpr : expr.resolve? env = some resolvedExpr) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.unary op expr) =
      some (SurfaceResolvedWordExpr.unary op resolvedExpr) := by
  dsimp [SurfaceNamedWordExpr.resolve?]
  rw [hExpr]

theorem SurfaceNamedWordExpr.resolve?_iszero
    {env : SurfaceNameEnv} {expr : SurfaceNamedWordExpr}
    {resolvedExpr : SurfaceResolvedWordExpr}
    (hExpr : expr.resolve? env = some resolvedExpr) :
    SurfaceNamedWordExpr.resolve? env
        (SurfaceNamedWordExpr.iszero expr) =
      some (SurfaceResolvedWordExpr.iszero resolvedExpr) := by
  exact SurfaceNamedWordExpr.resolve?_unary hExpr

theorem SurfaceResolvedWordExpr.toStateExpr?_binary
    {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExpr?
        (SurfaceResolvedWordExpr.binary op lhs rhs) =
      some (op.toStateExpr lhsExpr rhsExpr) := by
  dsimp [SurfaceResolvedWordExpr.toStateExpr?]
  rw [hLhs, hRhs]

theorem SurfaceResolvedWordExpr.toStateExpr?_add
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExpr?
        (SurfaceResolvedWordExpr.add lhs rhs) =
      some (StateExpr.add lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toStateExpr?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toStateExpr?_mul
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExpr?
        (SurfaceResolvedWordExpr.mul lhs rhs) =
      some (StateExpr.mul lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toStateExpr?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toStateExpr?_unary
    {op : SurfaceWordUnaryOp}
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr : expr.toStateExpr? = some stateExpr) :
    SurfaceResolvedWordExpr.toStateExpr?
        (SurfaceResolvedWordExpr.unary op expr) =
      some (op.toStateExpr stateExpr) := by
  dsimp [SurfaceResolvedWordExpr.toStateExpr?]
  rw [hExpr]

theorem SurfaceResolvedWordExpr.toStateExpr?_iszero
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr : expr.toStateExpr? = some stateExpr) :
    SurfaceResolvedWordExpr.toStateExpr?
        (SurfaceResolvedWordExpr.iszero expr) =
      some (StateExpr.iszero stateExpr) := by
  exact SurfaceResolvedWordExpr.toStateExpr?_unary hExpr

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_local_self
    (localInfo : SurfaceLocalInfo) (localValue : Expr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.local localInfo) =
      some (StateExpr.pure localValue) := by
  simp [SurfaceResolvedWordExpr.toStateExprWithLocal?,
    SurfaceResolvedWordExpr.toStateExprWithLocals?,
    SurfaceLocalValueEnv.single, SurfaceLocalValueEnv.push,
    SurfaceLocalValueEnv.lookup?]

theorem SurfaceResolvedWordExpr.toStateExprWithLocals?_local_lookup
    {locals : SurfaceLocalValueEnv} {info : SurfaceLocalInfo}
    {value : Expr}
    (hLookup : SurfaceLocalValueEnv.lookup? locals info = some value) :
    SurfaceResolvedWordExpr.toStateExprWithLocals? locals
        (SurfaceResolvedWordExpr.local info) =
      some (StateExpr.pure value) := by
  dsimp [SurfaceResolvedWordExpr.toStateExprWithLocals?]
  rw [hLookup]

theorem SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_self
    (info : SurfaceLocalInfo) (value : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedWordExpr.toStateExprWithLocals?
        (SurfaceLocalValueEnv.push info value locals)
        (SurfaceResolvedWordExpr.local info) =
      some (StateExpr.pure value) := by
  exact
    SurfaceResolvedWordExpr.toStateExprWithLocals?_local_lookup
      (SurfaceLocalValueEnv.lookup?_push_self info value locals)

theorem SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_other
    {pushed info : SurfaceLocalInfo} {pushedValue value : Expr}
    (locals : SurfaceLocalValueEnv) (hNe : info ≠ pushed)
    (hLookup : SurfaceLocalValueEnv.lookup? locals info = some value) :
    SurfaceResolvedWordExpr.toStateExprWithLocals?
        (SurfaceLocalValueEnv.push pushed pushedValue locals)
        (SurfaceResolvedWordExpr.local info) =
      some (StateExpr.pure value) := by
  exact
    SurfaceResolvedWordExpr.toStateExprWithLocals?_local_lookup
      ((SurfaceLocalValueEnv.lookup?_push_other locals hNe).trans
        hLookup)

theorem SurfaceResolvedWordExpr.toStateExprWithLocals?_binary
    {locals : SurfaceLocalValueEnv} {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocals? locals = some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocals? locals = some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocals? locals
        (SurfaceResolvedWordExpr.binary op lhs rhs) =
      some (op.toStateExpr lhsExpr rhsExpr) := by
  dsimp [SurfaceResolvedWordExpr.toStateExprWithLocals?]
  rw [hLhs, hRhs]

theorem SurfaceResolvedWordExpr.toStateExprWithLocals?_add
    {locals : SurfaceLocalValueEnv}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocals? locals = some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocals? locals = some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocals? locals
        (SurfaceResolvedWordExpr.add lhs rhs) =
      some (StateExpr.add lhsExpr rhsExpr) := by
  exact
    SurfaceResolvedWordExpr.toStateExprWithLocals?_binary
      hLhs hRhs

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_binary
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocal? localInfo localValue =
        some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocal? localInfo localValue =
        some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.binary op lhs rhs) =
      some (op.toStateExpr lhsExpr rhsExpr) := by
  change lhs.toStateExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some lhsExpr at hLhs
  change rhs.toStateExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some rhsExpr at hRhs
  dsimp [SurfaceResolvedWordExpr.toStateExprWithLocal?,
    SurfaceResolvedWordExpr.toStateExprWithLocals?]
  rw [hLhs, hRhs]

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_add
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocal? localInfo localValue =
        some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocal? localInfo localValue =
        some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.add lhs rhs) =
      some (StateExpr.add lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toStateExprWithLocal?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_mul
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocal? localInfo localValue =
        some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocal? localInfo localValue =
        some rhsExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.mul lhs rhs) =
      some (StateExpr.mul lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toStateExprWithLocal?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_unary
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {op : SurfaceWordUnaryOp}
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr :
      expr.toStateExprWithLocal? localInfo localValue =
        some stateExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.unary op expr) =
      some (op.toStateExpr stateExpr) := by
  change expr.toStateExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some stateExpr at hExpr
  dsimp [SurfaceResolvedWordExpr.toStateExprWithLocal?,
    SurfaceResolvedWordExpr.toStateExprWithLocals?]
  rw [hExpr]

theorem SurfaceResolvedWordExpr.toStateExprWithLocal?_iszero
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr :
      expr.toStateExprWithLocal? localInfo localValue =
        some stateExpr) :
    SurfaceResolvedWordExpr.toStateExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.iszero expr) =
      some (StateExpr.iszero stateExpr) := by
  exact SurfaceResolvedWordExpr.toStateExprWithLocal?_unary hExpr

theorem SurfaceResolvedWordExpr.toPureExpr?_binary
    {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : Expr}
    (hLhs : lhs.toPureExpr? = some lhsExpr)
    (hRhs : rhs.toPureExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toPureExpr?
        (SurfaceResolvedWordExpr.binary op lhs rhs) =
      some (op.toPureExpr lhsExpr rhsExpr) := by
  dsimp [SurfaceResolvedWordExpr.toPureExpr?]
  rw [hLhs, hRhs]

theorem SurfaceResolvedWordExpr.toPureExpr?_add
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : Expr}
    (hLhs : lhs.toPureExpr? = some lhsExpr)
    (hRhs : rhs.toPureExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toPureExpr?
        (SurfaceResolvedWordExpr.add lhs rhs) =
      some (Expr.add lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toPureExpr?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toPureExpr?_mul
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : Expr}
    (hLhs : lhs.toPureExpr? = some lhsExpr)
    (hRhs : rhs.toPureExpr? = some rhsExpr) :
    SurfaceResolvedWordExpr.toPureExpr?
        (SurfaceResolvedWordExpr.mul lhs rhs) =
      some (Expr.mul lhsExpr rhsExpr) := by
  exact SurfaceResolvedWordExpr.toPureExpr?_binary hLhs hRhs

theorem SurfaceResolvedWordExpr.toPureExpr?_unary
    {op : SurfaceWordUnaryOp}
    {expr : SurfaceResolvedWordExpr} {pureExpr : Expr}
    (hExpr : expr.toPureExpr? = some pureExpr) :
    SurfaceResolvedWordExpr.toPureExpr?
        (SurfaceResolvedWordExpr.unary op expr) =
      some (op.toPureExpr pureExpr) := by
  dsimp [SurfaceResolvedWordExpr.toPureExpr?]
  rw [hExpr]

theorem SurfaceResolvedWordExpr.toPureExpr?_iszero
    {expr : SurfaceResolvedWordExpr} {pureExpr : Expr}
    (hExpr : expr.toPureExpr? = some pureExpr) :
    SurfaceResolvedWordExpr.toPureExpr?
        (SurfaceResolvedWordExpr.iszero expr) =
      some (Expr.iszero pureExpr) := by
  exact SurfaceResolvedWordExpr.toPureExpr?_unary hExpr

theorem SurfaceResolvedWordExpr.toPureExprWithLocal?_local_self
    (localInfo : SurfaceLocalInfo) (localValue : Expr) :
    SurfaceResolvedWordExpr.toPureExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.local localInfo) =
      some localValue := by
  simp [SurfaceResolvedWordExpr.toPureExprWithLocal?,
    SurfaceResolvedWordExpr.toPureExprWithLocals?,
    SurfaceLocalValueEnv.single, SurfaceLocalValueEnv.push,
    SurfaceLocalValueEnv.lookup?]

theorem SurfaceResolvedWordExpr.toPureExprWithLocals?_local_lookup
    {locals : SurfaceLocalValueEnv} {info : SurfaceLocalInfo}
    {value : Expr}
    (hLookup : SurfaceLocalValueEnv.lookup? locals info = some value) :
    SurfaceResolvedWordExpr.toPureExprWithLocals? locals
        (SurfaceResolvedWordExpr.local info) =
      some value := by
  dsimp [SurfaceResolvedWordExpr.toPureExprWithLocals?]
  exact hLookup

theorem SurfaceResolvedWordExpr.toPureExprWithLocals?_local_push_self
    (info : SurfaceLocalInfo) (value : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedWordExpr.toPureExprWithLocals?
        (SurfaceLocalValueEnv.push info value locals)
        (SurfaceResolvedWordExpr.local info) =
      some value := by
  exact
    SurfaceResolvedWordExpr.toPureExprWithLocals?_local_lookup
      (SurfaceLocalValueEnv.lookup?_push_self info value locals)

theorem SurfaceResolvedWordExpr.toPureExprWithLocal?_binary
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : Expr}
    (hLhs :
      lhs.toPureExprWithLocal? localInfo localValue =
        some lhsExpr)
    (hRhs :
      rhs.toPureExprWithLocal? localInfo localValue =
        some rhsExpr) :
    SurfaceResolvedWordExpr.toPureExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.binary op lhs rhs) =
      some (op.toPureExpr lhsExpr rhsExpr) := by
  change lhs.toPureExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some lhsExpr at hLhs
  change rhs.toPureExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some rhsExpr at hRhs
  dsimp [SurfaceResolvedWordExpr.toPureExprWithLocal?,
    SurfaceResolvedWordExpr.toPureExprWithLocals?]
  rw [hLhs, hRhs]

theorem SurfaceResolvedWordExpr.toPureExprWithLocal?_unary
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {op : SurfaceWordUnaryOp}
    {expr : SurfaceResolvedWordExpr} {pureExpr : Expr}
    (hExpr :
      expr.toPureExprWithLocal? localInfo localValue =
        some pureExpr) :
    SurfaceResolvedWordExpr.toPureExprWithLocal?
        localInfo localValue
        (SurfaceResolvedWordExpr.unary op expr) =
      some (op.toPureExpr pureExpr) := by
  change expr.toPureExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some pureExpr at hExpr
  dsimp [SurfaceResolvedWordExpr.toPureExprWithLocal?,
    SurfaceResolvedWordExpr.toPureExprWithLocals?]
  rw [hExpr]

theorem SurfaceNamedLValue.resolve?_ident_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNamedLValue.resolve?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedLValue.ident name) =
      some
        (SurfaceResolvedLValue.local
          (SurfaceLocalInfo.uint256 handle)) := by
  dsimp [SurfaceNamedLValue.resolve?]
  rw [SurfaceNameEnv.resolveIdentLValue?_push_local_self]

theorem SurfaceNamedLValue.resolve?_ident_storage_self
    (name : String) (slot : Expr) :
    SurfaceNamedLValue.resolve?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedLValue.ident name) =
      some
        (SurfaceResolvedLValue.storage
          (SurfaceStorageInfo.uint256 slot)) := by
  dsimp [SurfaceNamedLValue.resolve?]
  rw [SurfaceNameEnv.resolveIdentLValue?_single_storage_self]

inductive SurfaceNamedStmt where
  | skip : SurfaceNamedStmt
  | localDecl : String -> Expr -> SurfaceNamedStmt -> SurfaceNamedStmt
  | returnWord : SurfaceNamedWordExpr -> SurfaceNamedStmt
  | assign : SurfaceNamedLValue -> Expr -> SurfaceNamedStmt
  | ifThen : SurfaceNamedWordExpr -> SurfaceNamedStmt -> SurfaceNamedStmt
  | ifElse :
      SurfaceNamedWordExpr -> SurfaceNamedStmt ->
        SurfaceNamedStmt -> SurfaceNamedStmt
  | switch1 :
      SurfaceNamedWordExpr -> Word -> SurfaceNamedStmt ->
        SurfaceNamedStmt -> SurfaceNamedStmt
  | forOnce : SurfaceNamedStmt -> SurfaceNamedStmt
  | forIf : SurfaceNamedWordExpr -> SurfaceNamedStmt -> SurfaceNamedStmt
  | seq : SurfaceNamedStmt -> SurfaceNamedStmt -> SurfaceNamedStmt
  deriving DecidableEq, Repr

def SurfaceNamedStmt.switchCases
    (discr : SurfaceNamedWordExpr) :
    List (Word × SurfaceNamedStmt) -> SurfaceNamedStmt ->
      SurfaceNamedStmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      SurfaceNamedStmt.switch1 discr label branch
        (SurfaceNamedStmt.switchCases discr rest defaultBranch)

def SurfaceNamedStmt.loopIf
    (cond : SurfaceNamedWordExpr) (body : SurfaceNamedStmt) :
    SurfaceNamedStmt :=
  SurfaceNamedStmt.ifThen cond (SurfaceNamedStmt.forOnce body)

def SurfaceNamedStmt.boundedWhile :
    Nat -> SurfaceNamedWordExpr -> SurfaceNamedStmt -> SurfaceNamedStmt
  | 0, _, _ => SurfaceNamedStmt.skip
  | n + 1, cond, body =>
      SurfaceNamedStmt.loopIf cond
        (SurfaceNamedStmt.seq body
          (SurfaceNamedStmt.boundedWhile n cond body))

inductive SurfaceResolvedStmt where
  | skip : SurfaceResolvedStmt
  | localDecl :
      SurfaceLocalInfo -> Expr -> SurfaceResolvedStmt ->
        SurfaceResolvedStmt
  | returnWord : SurfaceResolvedWordExpr -> SurfaceResolvedStmt
  | assign : SurfaceResolvedLValue -> Expr -> SurfaceResolvedStmt
  | ifThen : SurfaceResolvedWordExpr -> SurfaceResolvedStmt ->
      SurfaceResolvedStmt
  | ifElse :
      SurfaceResolvedWordExpr -> SurfaceResolvedStmt ->
        SurfaceResolvedStmt -> SurfaceResolvedStmt
  | switch1 :
      SurfaceResolvedWordExpr -> Word -> SurfaceResolvedStmt ->
        SurfaceResolvedStmt -> SurfaceResolvedStmt
  | forOnce : SurfaceResolvedStmt -> SurfaceResolvedStmt
  | forIf : SurfaceResolvedWordExpr -> SurfaceResolvedStmt ->
      SurfaceResolvedStmt
  | seq : SurfaceResolvedStmt -> SurfaceResolvedStmt -> SurfaceResolvedStmt
  deriving DecidableEq, Repr

def SurfaceNamedStmt.resolve?
    (env : SurfaceNameEnv) : SurfaceNamedStmt ->
    Option SurfaceResolvedStmt
  | SurfaceNamedStmt.skip =>
      some SurfaceResolvedStmt.skip
  | SurfaceNamedStmt.localDecl name init body =>
      let handle := env.nextLocalHandle
      let info := SurfaceLocalInfo.uint256 handle
      let localEnv :=
        env.pushScope (SurfaceNameScope.singleLocal name handle)
      match body.resolve? localEnv with
      | some resolvedBody =>
          some
            (SurfaceResolvedStmt.localDecl
              info init resolvedBody)
      | none => none
  | SurfaceNamedStmt.returnWord returnExpr =>
      match SurfaceNamedWordExpr.resolve? env returnExpr with
      | some resolvedReturn =>
          some (SurfaceResolvedStmt.returnWord resolvedReturn)
      | none => none
  | SurfaceNamedStmt.assign target value =>
      match SurfaceNamedLValue.resolve? env target with
      | some resolvedTarget =>
          some (SurfaceResolvedStmt.assign resolvedTarget value)
      | none => none
  | SurfaceNamedStmt.ifThen cond body =>
      match cond.resolve? env, body.resolve? env with
      | some resolvedCond, some resolvedBody =>
          some (SurfaceResolvedStmt.ifThen resolvedCond resolvedBody)
      | _, _ => none
  | SurfaceNamedStmt.ifElse cond thenBranch elseBranch =>
      match cond.resolve? env, thenBranch.resolve? env,
          elseBranch.resolve? env with
      | some resolvedCond, some resolvedThen, some resolvedElse =>
          some
            (SurfaceResolvedStmt.ifElse
              resolvedCond resolvedThen resolvedElse)
      | _, _, _ => none
  | SurfaceNamedStmt.switch1 discr label branch defaultBranch =>
      match discr.resolve? env, branch.resolve? env,
          defaultBranch.resolve? env with
      | some resolvedDiscr, some resolvedBranch,
          some resolvedDefault =>
          some
            (SurfaceResolvedStmt.switch1
              resolvedDiscr label resolvedBranch resolvedDefault)
      | _, _, _ => none
  | SurfaceNamedStmt.forOnce body =>
      match body.resolve? env with
      | some resolvedBody =>
          some (SurfaceResolvedStmt.forOnce resolvedBody)
      | none => none
  | SurfaceNamedStmt.forIf cond body =>
      match cond.resolve? env, body.resolve? env with
      | some resolvedCond, some resolvedBody =>
          some (SurfaceResolvedStmt.forIf resolvedCond resolvedBody)
      | _, _ => none
  | SurfaceNamedStmt.seq first second =>
      match first.resolve? env, second.resolve? env with
      | some resolvedFirst, some resolvedSecond =>
          some (SurfaceResolvedStmt.seq resolvedFirst resolvedSecond)
      | _, _ => none

def SurfaceResolvedStmt.toSurfaceStmtWithLocals?
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedStmt -> Option SurfaceStmt
  | SurfaceResolvedStmt.skip => some SurfaceStmt.skip
  | SurfaceResolvedStmt.localDecl localInfo init body =>
      body.toSurfaceStmtWithLocals?
        (SurfaceLocalValueEnv.push localInfo init locals)
  | SurfaceResolvedStmt.returnWord returnExpr =>
      match returnExpr.toStateExprWithLocals? locals with
      | some stateExpr => some (SurfaceStmt.returnStateExpr stateExpr)
      | none => none
  | SurfaceResolvedStmt.assign
      (SurfaceResolvedLValue.storage info) value =>
      some (SurfaceStmt.storageStore info.slot value)
  | SurfaceResolvedStmt.assign
      (SurfaceResolvedLValue.local _) _ =>
      none
  | SurfaceResolvedStmt.ifThen cond body =>
      match cond.toPureExprWithLocals? locals,
          body.toSurfaceStmtWithLocals? locals with
      | some condExpr, some bodyStmt =>
          some (SurfaceStmt.ifThen condExpr bodyStmt)
      | _, _ => none
  | SurfaceResolvedStmt.ifElse cond thenBranch elseBranch =>
      match cond.toPureExprWithLocals? locals,
          thenBranch.toSurfaceStmtWithLocals? locals,
          elseBranch.toSurfaceStmtWithLocals? locals with
      | some condExpr, some thenStmt, some elseStmt =>
          some (SurfaceStmt.switch1 condExpr 0 elseStmt thenStmt)
      | _, _, _ => none
  | SurfaceResolvedStmt.switch1 discr label branch defaultBranch =>
      match discr.toPureExprWithLocals? locals,
          branch.toSurfaceStmtWithLocals? locals,
          defaultBranch.toSurfaceStmtWithLocals? locals with
      | some discrExpr, some branchStmt, some defaultStmt =>
          some (SurfaceStmt.switch1
            discrExpr label branchStmt defaultStmt)
      | _, _, _ => none
  | SurfaceResolvedStmt.forOnce body =>
      match body.toSurfaceStmtWithLocals? locals with
      | some bodyStmt => some (SurfaceStmt.forOnce bodyStmt)
      | none => none
  | SurfaceResolvedStmt.forIf cond body =>
      match cond.toPureExprWithLocals? locals,
          body.toSurfaceStmtWithLocals? locals with
      | some condExpr, some bodyStmt =>
          some (SurfaceStmt.forIf condExpr bodyStmt)
      | _, _ => none
  | SurfaceResolvedStmt.seq first second =>
      match first.toSurfaceStmtWithLocals? locals,
          second.toSurfaceStmtWithLocals? locals with
      | some firstStmt, some secondStmt =>
          some (SurfaceStmt.seq firstStmt secondStmt)
      | _, _ => none

def SurfaceResolvedStmt.toSurfaceStmtWithLocal?
    (localInfo : SurfaceLocalInfo) (localValue : Expr) :
    SurfaceResolvedStmt -> Option SurfaceStmt :=
  SurfaceResolvedStmt.toSurfaceStmtWithLocals?
    (SurfaceLocalValueEnv.single localInfo localValue)

def SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? :
    SurfaceLocalValueEnv -> SurfaceResolvedStmt ->
      Option (SurfaceStmt × SurfaceLocalValueEnv)
  | locals, SurfaceResolvedStmt.skip =>
      some (SurfaceStmt.skip, locals)
  | locals, SurfaceResolvedStmt.localDecl localInfo init body =>
      match
          body.toSurfaceStmtWithMutableLocals?
            (SurfaceLocalValueEnv.push localInfo init locals) with
      | some (bodyStmt, bodyLocals) =>
          match bodyLocals with
          | _localBinding :: outerLocals => some (bodyStmt, outerLocals)
          | [] => none
      | none => none
  | locals, SurfaceResolvedStmt.returnWord returnExpr =>
      match returnExpr.toStateExprWithLocals? locals with
      | some stateExpr =>
          some (SurfaceStmt.returnStateExpr stateExpr, locals)
      | none => none
  | locals, SurfaceResolvedStmt.assign
      (SurfaceResolvedLValue.storage info) value =>
      some (SurfaceStmt.storageStore info.slot value, locals)
  | locals, SurfaceResolvedStmt.assign
      (SurfaceResolvedLValue.local info) value =>
      match SurfaceLocalValueEnv.update? locals info value with
      | some locals' => some (SurfaceStmt.skip, locals')
      | none => none
  | locals, SurfaceResolvedStmt.ifThen cond body =>
      match cond.toPureExprWithLocals? locals,
          body.toSurfaceStmtWithMutableLocals? locals with
      | some condExpr, some (bodyStmt, bodyLocals) =>
          if bodyLocals = locals then
            some (SurfaceStmt.ifThen condExpr bodyStmt, locals)
          else
            none
      | _, _ => none
  | locals, SurfaceResolvedStmt.ifElse cond thenBranch elseBranch =>
      match cond.toPureExprWithLocals? locals,
          thenBranch.toSurfaceStmtWithMutableLocals? locals,
          elseBranch.toSurfaceStmtWithMutableLocals? locals with
      | some condExpr, some (thenStmt, thenLocals),
          some (elseStmt, elseLocals) =>
          if thenLocals = locals && elseLocals = locals then
            some (SurfaceStmt.switch1 condExpr 0 elseStmt thenStmt, locals)
          else
            none
      | _, _, _ => none
  | locals, SurfaceResolvedStmt.switch1 discr label branch defaultBranch =>
      match discr.toPureExprWithLocals? locals,
          branch.toSurfaceStmtWithMutableLocals? locals,
          defaultBranch.toSurfaceStmtWithMutableLocals? locals with
      | some discrExpr, some (branchStmt, branchLocals),
          some (defaultStmt, defaultLocals) =>
          if branchLocals = locals && defaultLocals = locals then
            some (SurfaceStmt.switch1
              discrExpr label branchStmt defaultStmt, locals)
          else
            none
      | _, _, _ => none
  | locals, SurfaceResolvedStmt.forOnce body =>
      match body.toSurfaceStmtWithMutableLocals? locals with
      | some (bodyStmt, bodyLocals) =>
          some (SurfaceStmt.forOnce bodyStmt, bodyLocals)
      | none => none
  | locals, SurfaceResolvedStmt.forIf cond body =>
      match cond.toPureExprWithLocals? locals,
          body.toSurfaceStmtWithMutableLocals? locals with
      | some condExpr, some (bodyStmt, bodyLocals) =>
          if bodyLocals = locals then
            some (SurfaceStmt.forIf condExpr bodyStmt, locals)
          else
            none
      | _, _ => none
  | locals, SurfaceResolvedStmt.seq first second =>
      match first.toSurfaceStmtWithMutableLocals? locals with
      | some (firstStmt, firstLocals) =>
          match second.toSurfaceStmtWithMutableLocals? firstLocals with
          | some (secondStmt, secondLocals) =>
              some (SurfaceStmt.seq firstStmt secondStmt, secondLocals)
          | none => none
      | none => none

def SurfaceResolvedStmt.toSurfaceStmt? :
    SurfaceResolvedStmt -> Option SurfaceStmt
  | SurfaceResolvedStmt.skip => some SurfaceStmt.skip
  | SurfaceResolvedStmt.localDecl localInfo init
      (SurfaceResolvedStmt.returnWord returnExpr) =>
      match returnExpr.toStateExprWithLocal? localInfo init with
      | some stateExpr => some (SurfaceStmt.returnStateExpr stateExpr)
      | none => none
  | SurfaceResolvedStmt.localDecl localInfo init body =>
      match body.toSurfaceStmtWithLocal? localInfo init with
      | some bodyStmt => some bodyStmt
      | none =>
          match
              body.toSurfaceStmtWithMutableLocals?
                (SurfaceLocalValueEnv.single localInfo init) with
          | some (bodyStmt, _) => some bodyStmt
          | none => none
  | SurfaceResolvedStmt.returnWord
      (SurfaceResolvedWordExpr.pure expr) =>
      some (SurfaceStmt.returnExpr expr)
  | SurfaceResolvedStmt.returnWord
      (SurfaceResolvedWordExpr.storageLoad info) =>
      some (SurfaceStmt.returnStateExpr (StateExpr.load info.slot))
  | SurfaceResolvedStmt.returnWord expr =>
      match expr.toStateExpr? with
      | some stateExpr => some (SurfaceStmt.returnStateExpr stateExpr)
      | none => none
  | SurfaceResolvedStmt.assign
      (SurfaceResolvedLValue.storage info) value =>
      some (SurfaceStmt.storageStore info.slot value)
  | SurfaceResolvedStmt.ifThen cond body =>
      match cond.toPureExpr?, body.toSurfaceStmt? with
      | some condExpr, some bodyStmt =>
          some (SurfaceStmt.ifThen condExpr bodyStmt)
      | _, _ => none
  | SurfaceResolvedStmt.ifElse cond thenBranch elseBranch =>
      match cond.toPureExpr?, thenBranch.toSurfaceStmt?,
          elseBranch.toSurfaceStmt? with
      | some condExpr, some thenStmt, some elseStmt =>
          some (SurfaceStmt.switch1 condExpr 0 elseStmt thenStmt)
      | _, _, _ => none
  | SurfaceResolvedStmt.switch1 discr label branch defaultBranch =>
      match discr.toPureExpr?, branch.toSurfaceStmt?,
          defaultBranch.toSurfaceStmt? with
      | some discrExpr, some branchStmt, some defaultStmt =>
          some
            (SurfaceStmt.switch1
              discrExpr label branchStmt defaultStmt)
      | _, _, _ => none
  | SurfaceResolvedStmt.forOnce body =>
      match body.toSurfaceStmt? with
      | some bodyStmt => some (SurfaceStmt.forOnce bodyStmt)
      | none => none
  | SurfaceResolvedStmt.forIf cond body =>
      match cond.toPureExpr?, body.toSurfaceStmt? with
      | some condExpr, some bodyStmt =>
          some (SurfaceStmt.forIf condExpr bodyStmt)
      | _, _ => none
  | SurfaceResolvedStmt.seq first second =>
      match first.toSurfaceStmt?, second.toSurfaceStmt? with
      | some firstStmt, some secondStmt =>
          some (SurfaceStmt.seq firstStmt secondStmt)
      | _, _ => none
  | _ => none

def SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
    (info : SurfaceStorageInfo) (value : Expr) :
    SurfaceResolvedStmt -> Option SurfaceStmt
  | SurfaceResolvedStmt.switch1
      (SurfaceResolvedWordExpr.storageLoad discrInfo)
      label branch defaultBranch =>
      if discrInfo = info then
        match branch.toSurfaceStmt?, defaultBranch.toSurfaceStmt? with
        | some branchStmt, some defaultStmt =>
            some (SurfaceStmt.switch1 value label branchStmt defaultStmt)
        | some branchStmt, none =>
            match
                SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
                  info value defaultBranch with
            | some defaultStmt =>
                some (SurfaceStmt.switch1 value label branchStmt defaultStmt)
            | none => none
        | _, _ => none
      else
        none
  | _ => none

def SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard? :
    SurfaceResolvedStmt -> Option SurfaceStmt
  | resolved =>
      match resolved.toSurfaceStmt? with
      | some stmt => some stmt
      | none =>
          match resolved with
          | SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage info) value)
              (SurfaceResolvedStmt.ifThen
                (SurfaceResolvedWordExpr.storageLoad guardInfo) body) =>
              if guardInfo = info then
                match body.toSurfaceStmt? with
                | some bodyStmt =>
                    some
                      (SurfaceStmt.storageStoreThenIfLoad
                        info.slot value bodyStmt)
                | none => none
              else
                none
          | SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage info) value)
              switchStmt =>
              match
                  SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
                    info value switchStmt with
              | some switchSurfaceStmt =>
                  some
                    (SurfaceStmt.seq
                      (SurfaceStmt.storageStore info.slot value)
                      switchSurfaceStmt)
              | none => none
          | _ => none

theorem SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?_seq_storage_if
    (info : SurfaceStorageInfo) (value : Expr)
    {body : SurfaceResolvedStmt} {bodyStmt : SurfaceStmt}
    (hBody : body.toSurfaceStmt? = some bodyStmt) :
    SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?
        (SurfaceResolvedStmt.seq
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage info) value)
          (SurfaceResolvedStmt.ifThen
            (SurfaceResolvedWordExpr.storageLoad info) body)) =
      some
        (SurfaceStmt.storageStoreThenIfLoad
          info.slot value bodyStmt) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?,
    SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedWordExpr.toPureExpr?, hBody]

theorem SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?_switch1
    (info : SurfaceStorageInfo) (value : Expr) (label : Word)
    {branch defaultBranch : SurfaceResolvedStmt}
    {branchStmt defaultStmt : SurfaceStmt}
    (hBranch : branch.toSurfaceStmt? = some branchStmt)
    (hDefault : defaultBranch.toSurfaceStmt? = some defaultStmt) :
    SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
        info value
        (SurfaceResolvedStmt.switch1
          (SurfaceResolvedWordExpr.storageLoad info)
          label branch defaultBranch) =
      some
        (SurfaceStmt.switch1 value label branchStmt defaultStmt) := by
  simp [SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?,
    hBranch, hDefault]

theorem SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?_switch1_cons
    (info : SurfaceStorageInfo) (value : Expr) (label : Word)
    {branch defaultBranch : SurfaceResolvedStmt}
    {branchStmt defaultStmt : SurfaceStmt}
    (hBranch : branch.toSurfaceStmt? = some branchStmt)
    (hDefault :
      SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
        info value defaultBranch =
          some defaultStmt)
    (hDefaultDirect : defaultBranch.toSurfaceStmt? = none) :
    SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
        info value
        (SurfaceResolvedStmt.switch1
          (SurfaceResolvedWordExpr.storageLoad info)
          label branch defaultBranch) =
      some
        (SurfaceStmt.switch1 value label branchStmt defaultStmt) := by
  simp [SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?,
    hBranch, hDefaultDirect, hDefault]

theorem SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?_seq_storage_switch1
    (info : SurfaceStorageInfo) (value : Expr) (label : Word)
    {branch defaultBranch : SurfaceResolvedStmt}
    {branchStmt defaultStmt : SurfaceStmt}
    (hBranch : branch.toSurfaceStmt? = some branchStmt)
    (hDefault : defaultBranch.toSurfaceStmt? = some defaultStmt) :
    SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?
        (SurfaceResolvedStmt.seq
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage info) value)
          (SurfaceResolvedStmt.switch1
            (SurfaceResolvedWordExpr.storageLoad info)
            label branch defaultBranch)) =
      some
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore info.slot value)
          (SurfaceStmt.switch1 value label branchStmt defaultStmt)) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?,
    SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedWordExpr.toPureExpr?,
    SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?,
    hBranch, hDefault]

theorem SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?_seq_storage_switch1_cons
    (info : SurfaceStorageInfo) (value : Expr) (label : Word)
    {branch defaultBranch : SurfaceResolvedStmt}
    {branchStmt defaultStmt : SurfaceStmt}
    (hBranch : branch.toSurfaceStmt? = some branchStmt)
    (hDefault :
      SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?
        info value defaultBranch =
          some defaultStmt)
    (hDefaultDirect : defaultBranch.toSurfaceStmt? = none) :
    SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?
        (SurfaceResolvedStmt.seq
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage info) value)
          (SurfaceResolvedStmt.switch1
            (SurfaceResolvedWordExpr.storageLoad info)
            label branch defaultBranch)) =
      some
        (SurfaceStmt.seq
          (SurfaceStmt.storageStore info.slot value)
          (SurfaceStmt.switch1 value label branchStmt defaultStmt)) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithStorageGuard?,
    SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedWordExpr.toPureExpr?,
    SurfaceResolvedStmt.toSurfaceSwitchWithStorageDiscr?,
    hBranch, hDefaultDirect, hDefault]

def SurfaceNamedStmt.toSurfaceStmt?
    (env : SurfaceNameEnv) (stmt : SurfaceNamedStmt) :
    Option SurfaceStmt :=
  match stmt.resolve? env with
  | some resolved => resolved.toSurfaceStmt?
  | none => none

def SurfaceNamedStmt.toSurfaceProgram?
    (env : SurfaceNameEnv) (stmt : SurfaceNamedStmt) :
    Option SurfaceProgram :=
  match stmt.toSurfaceStmt? env with
  | some body => some { body := body }
  | none => none

def SurfaceNamedStmt.toSurfaceStmtWithStorageGuard?
    (env : SurfaceNameEnv) (stmt : SurfaceNamedStmt) :
    Option SurfaceStmt :=
  match stmt.resolve? env with
  | some resolved => resolved.toSurfaceStmtWithStorageGuard?
  | none => none

def SurfaceNamedStmt.toSurfaceProgramWithStorageGuard?
    (env : SurfaceNameEnv) (stmt : SurfaceNamedStmt) :
    Option SurfaceProgram :=
  match stmt.toSurfaceStmtWithStorageGuard? env with
  | some body => some { body := body }
  | none => none

theorem SurfaceNamedStmt.toSurfaceProgramWithStorageGuard?_of_resolve
    {env : SurfaceNameEnv} {stmt : SurfaceNamedStmt}
    {resolved : SurfaceResolvedStmt} {body : SurfaceStmt}
    (hResolve : stmt.resolve? env = some resolved)
    (hLower : resolved.toSurfaceStmtWithStorageGuard? = some body) :
    SurfaceNamedStmt.toSurfaceProgramWithStorageGuard? env stmt =
      some { body := body } := by
  dsimp [SurfaceNamedStmt.toSurfaceProgramWithStorageGuard?,
    SurfaceNamedStmt.toSurfaceStmtWithStorageGuard?]
  simp [hResolve, hLower]

def compileSurfaceNamedStmtArtifact?
    (env : SurfaceNameEnv) (stmt : SurfaceNamedStmt) :
    Option SurfaceProgramArtifact :=
  match stmt.toSurfaceProgram? env with
  | some program => some (compileSurfaceProgramArtifact program)
  | none => none

theorem compileSurfaceNamedStmtArtifact?_eq_of_toSurfaceProgram?
    {env : SurfaceNameEnv} {stmt : SurfaceNamedStmt}
    {program : SurfaceProgram} {artifact : SurfaceProgramArtifact}
    (hProgram :
      SurfaceNamedStmt.toSurfaceProgram? env stmt = some program)
    (hArtifact :
      compileSurfaceNamedStmtArtifact? env stmt = some artifact) :
    artifact = compileSurfaceProgramArtifact program := by
  unfold compileSurfaceNamedStmtArtifact? at hArtifact
  rw [hProgram] at hArtifact
  cases hArtifact
  rfl

theorem compileSurfaceNamedStmtArtifact?_dynamic_sound
    {env : SurfaceNameEnv} {stmt : SurfaceNamedStmt}
    {program : SurfaceProgram} {artifact : SurfaceProgramArtifact}
    (hProgram :
      SurfaceNamedStmt.toSurfaceProgram? env stmt = some program)
    (hArtifact :
      compileSurfaceNamedStmtArtifact? env stmt = some artifact)
    (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        artifact.sourceArtifact.stmtArtifact.fuel
        state.toConfig
        artifact.sourceArtifact.stmtArtifact.stmt =
      (program.eval state).toSymYulResults := by
  have hEq :=
    compileSurfaceNamedStmtArtifact?_eq_of_toSurfaceProgram?
      hProgram hArtifact
  rw [hEq]
  exact compileSurfaceProgramArtifact_dynamic_sound program state

theorem compileSurfaceNamedStmtArtifact?_staticChecked
    {env : SurfaceNameEnv} {stmt : SurfaceNamedStmt}
    {program : SurfaceProgram} {artifact : SurfaceProgramArtifact}
    (hProgram :
      SurfaceNamedStmt.toSurfaceProgram? env stmt = some program)
    (hArtifact :
      compileSurfaceNamedStmtArtifact? env stmt = some artifact) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        artifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        artifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  have hEq :=
    compileSurfaceNamedStmtArtifact?_eq_of_toSurfaceProgram?
      hProgram hArtifact
  rw [hEq]
  exact compileSurfaceProgramArtifact_staticChecked program

theorem compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
    {env : SurfaceNameEnv} {stmt : SurfaceNamedStmt}
    {program : SurfaceProgram} {artifact : SurfaceProgramArtifact}
    (hProgram :
      SurfaceNamedStmt.toSurfaceProgram? env stmt = some program)
    (hArtifact :
      compileSurfaceNamedStmtArtifact? env stmt = some artifact) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      artifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      artifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  have hEq :=
    compileSurfaceNamedStmtArtifact?_eq_of_toSurfaceProgram?
      hProgram hArtifact
  rw [hEq]
  exact compileSurfaceProgramArtifact_accepted_currentSolidCore program

theorem SurfaceNamedStmt.resolve?_localDecl_returnWord_self
    (env : SurfaceNameEnv) (name : String) (init : Expr) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.localDecl
          name init
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident name))) =
      some
        (SurfaceResolvedStmt.localDecl
          (SurfaceLocalInfo.uint256 env.nextLocalHandle)
          init
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.local
              (SurfaceLocalInfo.uint256 env.nextLocalHandle)))) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_ident_local_self]

theorem SurfaceNamedStmt.resolve?_localDecl
    {env : SurfaceNameEnv} {name : String} {init : Expr}
    {body : SurfaceNamedStmt} {resolvedBody : SurfaceResolvedStmt}
    (hBody :
      body.resolve?
          (env.pushScope
            (SurfaceNameScope.singleLocal name env.nextLocalHandle)) =
        some resolvedBody) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.localDecl name init body) =
      some
        (SurfaceResolvedStmt.localDecl
          (SurfaceLocalInfo.uint256 env.nextLocalHandle)
          init resolvedBody) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hBody]

theorem SurfaceNamedStmt.resolve?_returnWord_pure
    (env : SurfaceNameEnv) (expr : Expr) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.pure expr)) =
      some
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.pure expr)) := by
  rfl

theorem SurfaceNamedStmt.resolve?_returnWord_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNamedStmt.resolve?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident name)) =
      some
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.local
            (SurfaceLocalInfo.uint256 handle))) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_ident_local_self]

theorem SurfaceNamedStmt.resolve?_returnWord_storage_self
    (name : String) (slot : Expr) :
    SurfaceNamedStmt.resolve?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident name)) =
      some
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.storageLoad
            (SurfaceStorageInfo.uint256 slot))) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_ident_storage_self]

theorem SurfaceNamedStmt.resolve?_assign_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) (value : Expr) :
    SurfaceNamedStmt.resolve?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedStmt.assign
          (SurfaceNamedLValue.ident name) value) =
      some
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.local
            (SurfaceLocalInfo.uint256 handle))
          value) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedLValue.resolve?_ident_local_self]

theorem SurfaceNamedStmt.resolve?_assign_storage_self
    (name : String) (slot value : Expr) :
    SurfaceNamedStmt.resolve?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.assign
          (SurfaceNamedLValue.ident name) value) =
      some
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.storage
            (SurfaceStorageInfo.uint256 slot))
          value) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedLValue.resolve?_ident_storage_self]

theorem SurfaceNamedStmt.resolve?_skip
    (env : SurfaceNameEnv) :
    SurfaceNamedStmt.resolve? env SurfaceNamedStmt.skip =
      some SurfaceResolvedStmt.skip := by
  rfl

theorem SurfaceNamedStmt.resolve?_seq
    {env : SurfaceNameEnv} {first second : SurfaceNamedStmt}
    {resolvedFirst resolvedSecond : SurfaceResolvedStmt}
    (hFirst :
      first.resolve? env = some resolvedFirst)
    (hSecond :
      second.resolve? env = some resolvedSecond) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.seq first second) =
      some (SurfaceResolvedStmt.seq resolvedFirst resolvedSecond) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hFirst, hSecond]

theorem SurfaceNamedStmt.resolve?_ifThen
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {body : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedBody : SurfaceResolvedStmt}
    (hCond :
      cond.resolve? env = some resolvedCond)
    (hBody :
      body.resolve? env = some resolvedBody) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.ifThen cond body) =
      some (SurfaceResolvedStmt.ifThen resolvedCond resolvedBody) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hCond, hBody]

theorem SurfaceNamedStmt.resolve?_ifElse
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {thenBranch elseBranch : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedThen resolvedElse : SurfaceResolvedStmt}
    (hCond :
      cond.resolve? env = some resolvedCond)
    (hThen :
      thenBranch.resolve? env = some resolvedThen)
    (hElse :
      elseBranch.resolve? env = some resolvedElse) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.ifElse cond thenBranch elseBranch) =
      some
        (SurfaceResolvedStmt.ifElse
          resolvedCond resolvedThen resolvedElse) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hCond, hThen, hElse]

theorem SurfaceNamedStmt.resolve?_switch1
    {env : SurfaceNameEnv} {discr : SurfaceNamedWordExpr}
    {label : Word} {branch defaultBranch : SurfaceNamedStmt}
    {resolvedDiscr : SurfaceResolvedWordExpr}
    {resolvedBranch resolvedDefault : SurfaceResolvedStmt}
    (hDiscr :
      discr.resolve? env = some resolvedDiscr)
    (hBranch :
      branch.resolve? env = some resolvedBranch)
    (hDefault :
      defaultBranch.resolve? env = some resolvedDefault) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.switch1 discr label branch defaultBranch) =
      some
        (SurfaceResolvedStmt.switch1
          resolvedDiscr label resolvedBranch resolvedDefault) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hDiscr, hBranch, hDefault]

theorem SurfaceNamedStmt.resolve?_forOnce
    {env : SurfaceNameEnv} {body : SurfaceNamedStmt}
    {resolvedBody : SurfaceResolvedStmt}
    (hBody :
      body.resolve? env = some resolvedBody) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.forOnce body) =
      some (SurfaceResolvedStmt.forOnce resolvedBody) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hBody]

theorem SurfaceNamedStmt.resolve?_forIf
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {body : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedBody : SurfaceResolvedStmt}
    (hCond :
      cond.resolve? env = some resolvedCond)
    (hBody :
      body.resolve? env = some resolvedBody) :
    SurfaceNamedStmt.resolve? env
        (SurfaceNamedStmt.forIf cond body) =
      some (SurfaceResolvedStmt.forIf resolvedCond resolvedBody) := by
  dsimp [SurfaceNamedStmt.resolve?]
  rw [hCond, hBody]

theorem SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_self
    (localInfo : SurfaceLocalInfo) (init : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl
          localInfo init
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.local localInfo))) =
      some (SurfaceStmt.returnStateExpr (StateExpr.pure init)) := by
  simp [SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedWordExpr.toStateExprWithLocal?,
    SurfaceResolvedWordExpr.toStateExprWithLocals?,
    SurfaceLocalValueEnv.single, SurfaceLocalValueEnv.lookup?,
    SurfaceLocalValueEnv.push]

theorem SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_binary_withLocal
    {localInfo : SurfaceLocalInfo} {init : Expr}
    {op : SurfaceWordBinaryOp} {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocal? localInfo init =
        some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocal? localInfo init =
        some rhsExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl
          localInfo init
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.binary op lhs rhs))) =
      some
        (SurfaceStmt.returnStateExpr
          (op.toStateExpr lhsExpr rhsExpr)) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [SurfaceResolvedWordExpr.toStateExprWithLocal?_binary hLhs hRhs]

theorem SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_add_withLocal
    {localInfo : SurfaceLocalInfo} {init : Expr}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs :
      lhs.toStateExprWithLocal? localInfo init =
        some lhsExpr)
    (hRhs :
      rhs.toStateExprWithLocal? localInfo init =
        some rhsExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl
          localInfo init
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.add lhs rhs))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.add lhsExpr rhsExpr)) := by
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_binary_withLocal
      hLhs hRhs

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_pure
    (expr : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.pure expr)) =
      some (SurfaceStmt.returnExpr expr) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_storage
    (info : SurfaceStorageInfo) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.storageLoad info)) =
      some (SurfaceStmt.returnStateExpr (StateExpr.load info.slot)) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_binary
    {op : SurfaceWordBinaryOp}
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.binary op lhs rhs)) =
      some
        (SurfaceStmt.returnStateExpr
          (op.toStateExpr lhsExpr rhsExpr)) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [SurfaceResolvedWordExpr.toStateExpr?_binary hLhs hRhs]

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_add
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.add lhs rhs)) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.add lhsExpr rhsExpr)) := by
  exact SurfaceResolvedStmt.toSurfaceStmt?_returnWord_binary hLhs hRhs

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_mul
    {lhs rhs : SurfaceResolvedWordExpr}
    {lhsExpr rhsExpr : StateExpr}
    (hLhs : lhs.toStateExpr? = some lhsExpr)
    (hRhs : rhs.toStateExpr? = some rhsExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.mul lhs rhs)) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.mul lhsExpr rhsExpr)) := by
  exact SurfaceResolvedStmt.toSurfaceStmt?_returnWord_binary hLhs hRhs

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_unary
    {op : SurfaceWordUnaryOp}
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr : expr.toStateExpr? = some stateExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.unary op expr)) =
      some
        (SurfaceStmt.returnStateExpr
          (op.toStateExpr stateExpr)) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [SurfaceResolvedWordExpr.toStateExpr?_unary hExpr]

theorem SurfaceResolvedStmt.toSurfaceStmt?_returnWord_iszero
    {expr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hExpr : expr.toStateExpr? = some stateExpr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.iszero expr)) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.iszero stateExpr)) := by
  exact SurfaceResolvedStmt.toSurfaceStmt?_returnWord_unary hExpr

theorem SurfaceResolvedStmt.toSurfaceStmt?_assign_storage
    (info : SurfaceStorageInfo) (value : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.storage info) value) =
      some (SurfaceStmt.storageStore info.slot value) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmt?_assign_local_rejected
    (info : SurfaceLocalInfo) (value : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.local info) value) =
      none := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmt?_skip :
    SurfaceResolvedStmt.toSurfaceStmt? SurfaceResolvedStmt.skip =
      some SurfaceStmt.skip := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmt?_ifThen
    {cond : SurfaceResolvedWordExpr} {body : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCond :
      cond.toPureExpr? = some condExpr)
    (hBody :
      body.toSurfaceStmt? = some bodyStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.ifThen cond body) =
      some (SurfaceStmt.ifThen condExpr bodyStmt) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [hCond, hBody]

theorem SurfaceResolvedStmt.toSurfaceStmt?_ifElse
    {cond : SurfaceResolvedWordExpr}
    {thenBranch elseBranch : SurfaceResolvedStmt}
    {condExpr : Expr} {thenStmt elseStmt : SurfaceStmt}
    (hCond :
      cond.toPureExpr? = some condExpr)
    (hThen :
      thenBranch.toSurfaceStmt? = some thenStmt)
    (hElse :
      elseBranch.toSurfaceStmt? = some elseStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.ifElse cond thenBranch elseBranch) =
      some (SurfaceStmt.switch1 condExpr 0 elseStmt thenStmt) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [hCond, hThen, hElse]

theorem SurfaceResolvedStmt.toSurfaceStmt?_switch1
    {discr : SurfaceResolvedWordExpr} {label : Word}
    {branch defaultBranch : SurfaceResolvedStmt}
    {discrExpr : Expr} {branchStmt defaultStmt : SurfaceStmt}
    (hDiscr :
      discr.toPureExpr? = some discrExpr)
    (hBranch :
      branch.toSurfaceStmt? = some branchStmt)
    (hDefault :
      defaultBranch.toSurfaceStmt? = some defaultStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.switch1
          discr label branch defaultBranch) =
      some
        (SurfaceStmt.switch1
          discrExpr label branchStmt defaultStmt) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [hDiscr, hBranch, hDefault]

theorem SurfaceResolvedStmt.toSurfaceStmt?_forOnce
    {body : SurfaceResolvedStmt}
    {bodyStmt : SurfaceStmt}
    (hBody :
      body.toSurfaceStmt? = some bodyStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.forOnce body) =
      some (SurfaceStmt.forOnce bodyStmt) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [hBody]

theorem SurfaceResolvedStmt.toSurfaceStmt?_forIf
    {cond : SurfaceResolvedWordExpr} {body : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCond :
      cond.toPureExpr? = some condExpr)
    (hBody :
      body.toSurfaceStmt? = some bodyStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.forIf cond body) =
      some (SurfaceStmt.forIf condExpr bodyStmt) := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmt?]
  rw [hCond, hBody]

theorem SurfaceResolvedStmt.toSurfaceStmt?_seq
    {first second : SurfaceResolvedStmt}
    {firstStmt secondStmt : SurfaceStmt}
    (hFirst :
      first.toSurfaceStmt? = some firstStmt)
    (hSecond :
      second.toSurfaceStmt? = some secondStmt) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.seq first second) =
      some (SurfaceStmt.seq firstStmt secondStmt) := by
  simp [SurfaceResolvedStmt.toSurfaceStmt?, hFirst, hSecond]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_local
    {locals locals' : SurfaceLocalValueEnv}
    {info : SurfaceLocalInfo} {value : Expr}
    (hUpdate :
      SurfaceLocalValueEnv.update? locals info value = some locals') :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.local info) value) =
      some (SurfaceStmt.skip, locals') := by
  dsimp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?]
  rw [hUpdate]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_local_push_self
    (info : SurfaceLocalInfo) (oldValue newValue : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?
        (SurfaceLocalValueEnv.push info oldValue locals)
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.local info) newValue) =
      some
        (SurfaceStmt.skip,
          SurfaceLocalValueEnv.push info newValue locals) := by
  exact
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_local
      (SurfaceLocalValueEnv.update?_push_self
        info oldValue newValue locals)

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_storage
    (locals : SurfaceLocalValueEnv)
    (storageInfo : SurfaceStorageInfo) (value : Expr) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.storage storageInfo) value) =
      some (SurfaceStmt.storageStore storageInfo.slot value, locals) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord
    {locals : SurfaceLocalValueEnv}
    {returnExpr : SurfaceResolvedWordExpr} {stateExpr : StateExpr}
    (hReturn :
      returnExpr.toStateExprWithLocals? locals = some stateExpr) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.returnWord returnExpr) =
      some (SurfaceStmt.returnStateExpr stateExpr, locals) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?,
    hReturn]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord_local_push_self
    (info : SurfaceLocalInfo) (value : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?
        (SurfaceLocalValueEnv.push info value locals)
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.local info)) =
      some
        (SurfaceStmt.returnStateExpr (StateExpr.pure value),
          SurfaceLocalValueEnv.push info value locals) := by
  exact
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord
      (SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_self
        info value locals)

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord_storage
    (locals : SurfaceLocalValueEnv) (storageInfo : SurfaceStorageInfo) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.storageLoad storageInfo)) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.load storageInfo.slot), locals) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_ifThen_preserved
    {locals : SurfaceLocalValueEnv}
    {cond : SurfaceResolvedWordExpr} {body : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCond :
      cond.toPureExprWithLocals? locals = some condExpr)
    (hBody :
      body.toSurfaceStmtWithMutableLocals? locals =
        some (bodyStmt, locals)) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.ifThen cond body) =
      some (SurfaceStmt.ifThen condExpr bodyStmt, locals) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?,
    hCond, hBody]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_switch1_preserved
    {locals : SurfaceLocalValueEnv}
    {discr : SurfaceResolvedWordExpr} {label : Word}
    {branch defaultBranch : SurfaceResolvedStmt}
    {discrExpr : Expr} {branchStmt defaultStmt : SurfaceStmt}
    (hDiscr : discr.toPureExprWithLocals? locals = some discrExpr)
    (hBranch :
      branch.toSurfaceStmtWithMutableLocals? locals =
        some (branchStmt, locals))
    (hDefault :
      defaultBranch.toSurfaceStmtWithMutableLocals? locals =
        some (defaultStmt, locals)) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.switch1 discr label branch defaultBranch) =
      some
        (SurfaceStmt.switch1 discrExpr label branchStmt defaultStmt,
          locals) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?,
    hDiscr, hBranch, hDefault]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_forOnce
    {locals bodyLocals : SurfaceLocalValueEnv}
    {body : SurfaceResolvedStmt} {bodyStmt : SurfaceStmt}
    (hBody :
      body.toSurfaceStmtWithMutableLocals? locals =
        some (bodyStmt, bodyLocals)) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.forOnce body) =
      some (SurfaceStmt.forOnce bodyStmt, bodyLocals) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?,
    hBody]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq
    {locals midLocals finalLocals : SurfaceLocalValueEnv}
    {first second : SurfaceResolvedStmt}
    {firstStmt secondStmt : SurfaceStmt}
    (hFirst :
      first.toSurfaceStmtWithMutableLocals? locals =
        some (firstStmt, midLocals))
    (hSecond :
      second.toSurfaceStmtWithMutableLocals? midLocals =
        some (secondStmt, finalLocals)) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals? locals
        (SurfaceResolvedStmt.seq first second) =
      some (SurfaceStmt.seq firstStmt secondStmt, finalLocals) := by
  simp [SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?,
    hFirst, hSecond]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq_update_if_storage_read
    (localInfo : SurfaceLocalInfo) (oldValue condValue : Expr)
    (storageInfo : SurfaceStorageInfo) (storedValue : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?
        (SurfaceLocalValueEnv.push localInfo oldValue locals)
        (SurfaceResolvedStmt.seq
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.local localInfo) condValue)
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.ifThen
              (SurfaceResolvedWordExpr.local localInfo)
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo)
                storedValue))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad storageInfo)))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.ifThen condValue
              (SurfaceStmt.storageStore storageInfo.slot storedValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load storageInfo.slot))),
          SurfaceLocalValueEnv.push localInfo condValue locals) := by
  have hAssign :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_local_push_self
      localInfo oldValue condValue locals
  have hCond :=
    SurfaceResolvedWordExpr.toPureExprWithLocals?_local_push_self
      localInfo condValue locals
  have hStorageAssign :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_storage
      (SurfaceLocalValueEnv.push localInfo condValue locals)
      storageInfo storedValue
  have hIf :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_ifThen_preserved
      hCond hStorageAssign
  have hReturn :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord_storage
      (SurfaceLocalValueEnv.push localInfo condValue locals) storageInfo
  have hTail :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq hIf hReturn
  exact
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq
      hAssign hTail

theorem SurfaceResolvedStmt.toSurfaceStmt?_localDecl_update_if_storage_read
    (localInfo : SurfaceLocalInfo) (oldValue condValue : Expr)
    (storageInfo : SurfaceStorageInfo) (storedValue : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl localInfo oldValue
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.local localInfo) condValue)
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.ifThen
                (SurfaceResolvedWordExpr.local localInfo)
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo)
                  storedValue))
              (SurfaceResolvedStmt.returnWord
                (SurfaceResolvedWordExpr.storageLoad storageInfo))))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.ifThen condValue
              (SurfaceStmt.storageStore storageInfo.slot storedValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load storageInfo.slot)))) := by
  simp [SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?,
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq_update_if_storage_read,
    SurfaceLocalValueEnv.single]

theorem SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq_update_switch_storage_read
    (localInfo : SurfaceLocalInfo) (oldValue discrValue : Expr)
    (storageInfo : SurfaceStorageInfo) (label : Word)
    (branchValue defaultValue : Expr)
    (locals : SurfaceLocalValueEnv) :
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?
        (SurfaceLocalValueEnv.push localInfo oldValue locals)
        (SurfaceResolvedStmt.seq
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.local localInfo) discrValue)
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.switch1
              (SurfaceResolvedWordExpr.local localInfo)
              label
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo)
                branchValue)
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo)
                defaultValue))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad storageInfo)))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.switch1 discrValue label
              (SurfaceStmt.storageStore storageInfo.slot branchValue)
              (SurfaceStmt.storageStore storageInfo.slot defaultValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load storageInfo.slot))),
          SurfaceLocalValueEnv.push localInfo discrValue locals) := by
  have hAssign :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_local_push_self
      localInfo oldValue discrValue locals
  have hDiscr :=
    SurfaceResolvedWordExpr.toPureExprWithLocals?_local_push_self
      localInfo discrValue locals
  have hBranch :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_storage
      (SurfaceLocalValueEnv.push localInfo discrValue locals)
      storageInfo branchValue
  have hDefault :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_assign_storage
      (SurfaceLocalValueEnv.push localInfo discrValue locals)
      storageInfo defaultValue
  have hSwitch :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_switch1_preserved
      (locals := SurfaceLocalValueEnv.push localInfo discrValue locals)
      (label := label)
      hDiscr hBranch hDefault
  have hReturn :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_returnWord_storage
      (SurfaceLocalValueEnv.push localInfo discrValue locals) storageInfo
  have hTail :=
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq
      hSwitch hReturn
  exact
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq
      hAssign hTail

theorem SurfaceResolvedStmt.toSurfaceStmt?_localDecl_update_switch_storage_read
    (localInfo : SurfaceLocalInfo) (oldValue discrValue : Expr)
    (storageInfo : SurfaceStorageInfo) (label : Word)
    (branchValue defaultValue : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl localInfo oldValue
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.local localInfo) discrValue)
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.switch1
                (SurfaceResolvedWordExpr.local localInfo)
                label
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo)
                  branchValue)
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo)
                  defaultValue))
              (SurfaceResolvedStmt.returnWord
                (SurfaceResolvedWordExpr.storageLoad storageInfo))))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.switch1 discrValue label
              (SurfaceStmt.storageStore storageInfo.slot branchValue)
              (SurfaceStmt.storageStore storageInfo.slot defaultValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load storageInfo.slot)))) := by
  simp [SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?,
    SurfaceResolvedStmt.toSurfaceStmtWithMutableLocals?_seq_update_switch_storage_read,
    SurfaceLocalValueEnv.single]

theorem SurfaceResolvedStmt.toSurfaceStmt?_nested_localDecl_return_inner_self
    (outerInfo innerInfo : SurfaceLocalInfo)
    (outerInit innerInit : Expr) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl outerInfo outerInit
          (SurfaceResolvedStmt.localDecl innerInfo innerInit
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.local innerInfo)))) =
      some (SurfaceStmt.returnStateExpr (StateExpr.pure innerInit)) := by
  simp [SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?,
    SurfaceLocalValueEnv.single,
    SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_self]

theorem SurfaceResolvedStmt.toSurfaceStmt?_nested_localDecl_return_add_outer_inner
    (outerInfo innerInfo : SurfaceLocalInfo)
    (outerInit innerInit : Expr)
    (hNe : outerInfo ≠ innerInfo) :
    SurfaceResolvedStmt.toSurfaceStmt?
        (SurfaceResolvedStmt.localDecl outerInfo outerInit
          (SurfaceResolvedStmt.localDecl innerInfo innerInit
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.add
                (SurfaceResolvedWordExpr.local outerInfo)
                (SurfaceResolvedWordExpr.local innerInfo))))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.add
            (StateExpr.pure outerInit)
            (StateExpr.pure innerInit))) := by
  let outerLocals :=
    SurfaceLocalValueEnv.single outerInfo outerInit
  let innerLocals :=
    SurfaceLocalValueEnv.push innerInfo innerInit outerLocals
  have hOuterLookup :
      SurfaceLocalValueEnv.lookup? outerLocals outerInfo =
        some outerInit := by
    exact SurfaceLocalValueEnv.lookup?_push_self outerInfo outerInit []
  have hOuter :
      SurfaceResolvedWordExpr.toStateExprWithLocals? innerLocals
          (SurfaceResolvedWordExpr.local outerInfo) =
        some (StateExpr.pure outerInit) := by
    dsimp [innerLocals]
    exact
      SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_other
        outerLocals hNe hOuterLookup
  have hInner :
      SurfaceResolvedWordExpr.toStateExprWithLocals? innerLocals
          (SurfaceResolvedWordExpr.local innerInfo) =
        some (StateExpr.pure innerInit) := by
    exact
      SurfaceResolvedWordExpr.toStateExprWithLocals?_local_push_self
        innerInfo innerInit outerLocals
  have hAdd :
      SurfaceResolvedWordExpr.toStateExprWithLocals? innerLocals
          (SurfaceResolvedWordExpr.add
            (SurfaceResolvedWordExpr.local outerInfo)
            (SurfaceResolvedWordExpr.local innerInfo)) =
        some
          (StateExpr.add
            (StateExpr.pure outerInit)
            (StateExpr.pure innerInit)) :=
    SurfaceResolvedWordExpr.toStateExprWithLocals?_add hOuter hInner
  have hAddDirect :
      SurfaceResolvedWordExpr.toStateExprWithLocals?
          (SurfaceLocalValueEnv.push innerInfo innerInit
            (SurfaceLocalValueEnv.push outerInfo outerInit []))
          (SurfaceResolvedWordExpr.add
            (SurfaceResolvedWordExpr.local outerInfo)
            (SurfaceResolvedWordExpr.local innerInfo)) =
        some
          (StateExpr.add
            (StateExpr.pure outerInit)
            (StateExpr.pure innerInit)) := by
    exact hAdd
  simp [SurfaceResolvedStmt.toSurfaceStmt?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?,
    SurfaceLocalValueEnv.single, hAddDirect]

theorem SurfaceResolvedStmt.toSurfaceStmtWithLocal?_returnWord_storage
    (localInfo : SurfaceLocalInfo) (localValue : Expr)
    (storageInfo : SurfaceStorageInfo) :
    SurfaceResolvedStmt.toSurfaceStmtWithLocal? localInfo localValue
        (SurfaceResolvedStmt.returnWord
          (SurfaceResolvedWordExpr.storageLoad storageInfo)) =
      some (SurfaceStmt.returnStateExpr
        (StateExpr.load storageInfo.slot)) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmtWithLocal?_assign_storage
    (localInfo : SurfaceLocalInfo) (localValue : Expr)
    (storageInfo : SurfaceStorageInfo) (value : Expr) :
    SurfaceResolvedStmt.toSurfaceStmtWithLocal? localInfo localValue
        (SurfaceResolvedStmt.assign
          (SurfaceResolvedLValue.storage storageInfo) value) =
      some (SurfaceStmt.storageStore storageInfo.slot value) := by
  rfl

theorem SurfaceResolvedStmt.toSurfaceStmtWithLocal?_ifThen
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {cond : SurfaceResolvedWordExpr} {body : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCond :
      cond.toPureExprWithLocal? localInfo localValue =
        some condExpr)
    (hBody :
      body.toSurfaceStmtWithLocal? localInfo localValue =
        some bodyStmt) :
    SurfaceResolvedStmt.toSurfaceStmtWithLocal? localInfo localValue
        (SurfaceResolvedStmt.ifThen cond body) =
      some (SurfaceStmt.ifThen condExpr bodyStmt) := by
  change cond.toPureExprWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some condExpr at hCond
  change body.toSurfaceStmtWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some bodyStmt at hBody
  dsimp [SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?]
  rw [hCond, hBody]

theorem SurfaceResolvedStmt.toSurfaceStmtWithLocal?_seq
    {localInfo : SurfaceLocalInfo} {localValue : Expr}
    {first second : SurfaceResolvedStmt}
    {firstStmt secondStmt : SurfaceStmt}
    (hFirst :
      first.toSurfaceStmtWithLocal? localInfo localValue =
        some firstStmt)
    (hSecond :
      second.toSurfaceStmtWithLocal? localInfo localValue =
        some secondStmt) :
    SurfaceResolvedStmt.toSurfaceStmtWithLocal? localInfo localValue
        (SurfaceResolvedStmt.seq first second) =
      some (SurfaceStmt.seq firstStmt secondStmt) := by
  change first.toSurfaceStmtWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some firstStmt at hFirst
  change second.toSurfaceStmtWithLocals?
      (SurfaceLocalValueEnv.single localInfo localValue) =
        some secondStmt at hSecond
  dsimp [SurfaceResolvedStmt.toSurfaceStmtWithLocal?,
    SurfaceResolvedStmt.toSurfaceStmtWithLocals?]
  rw [hFirst, hSecond]

theorem SurfaceNamedStmt.toSurfaceStmt?_localDecl_returnWord_self
    (env : SurfaceNameEnv) (name : String) (init : Expr) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.localDecl
          name init
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident name))) =
      some (SurfaceStmt.returnStateExpr (StateExpr.pure init)) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_localDecl_returnWord_self]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_self
      (SurfaceLocalInfo.uint256 env.nextLocalHandle) init

theorem SurfaceNamedStmt.toSurfaceStmt?_nested_localDecl_shadow_return_inner_self
    (env : SurfaceNameEnv) (name : String)
    (outerInit innerInit : Expr) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.localDecl name outerInit
          (SurfaceNamedStmt.localDecl name innerInit
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.ident name)))) =
      some (SurfaceStmt.returnStateExpr (StateExpr.pure innerInit)) := by
  let outerInfo := SurfaceLocalInfo.uint256 env.nextLocalHandle
  let outerEnv :=
    env.pushScope
      (SurfaceNameScope.singleLocal name env.nextLocalHandle)
  let innerInfo := SurfaceLocalInfo.uint256 outerEnv.nextLocalHandle
  have hInnerReturnResolve :
      SurfaceNamedStmt.resolve?
          (outerEnv.pushScope
            (SurfaceNameScope.singleLocal name outerEnv.nextLocalHandle))
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident name)) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.local innerInfo)) := by
    dsimp [innerInfo]
    exact
      SurfaceNamedStmt.resolve?_returnWord_local_self
        outerEnv name outerEnv.nextLocalHandle
  have hInnerResolve :
      SurfaceNamedStmt.resolve? outerEnv
          (SurfaceNamedStmt.localDecl name innerInit
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.ident name))) =
        some
          (SurfaceResolvedStmt.localDecl innerInfo innerInit
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.local innerInfo))) := by
    dsimp [innerInfo]
    exact SurfaceNamedStmt.resolve?_localDecl hInnerReturnResolve
  have hResolve :
      SurfaceNamedStmt.resolve? env
          (SurfaceNamedStmt.localDecl name outerInit
            (SurfaceNamedStmt.localDecl name innerInit
              (SurfaceNamedStmt.returnWord
                (SurfaceNamedWordExpr.ident name)))) =
        some
          (SurfaceResolvedStmt.localDecl outerInfo outerInit
            (SurfaceResolvedStmt.localDecl innerInfo innerInit
              (SurfaceResolvedStmt.returnWord
                (SurfaceResolvedWordExpr.local innerInfo)))) := by
    dsimp [outerInfo, outerEnv]
    exact SurfaceNamedStmt.resolve?_localDecl hInnerResolve
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [hResolve]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_nested_localDecl_return_inner_self
      outerInfo innerInfo outerInit innerInit

theorem SurfaceNamedStmt.toSurfaceStmt?_localDecl_update_if_storage_read
    (localName storageName : String)
    (slot init condValue storedValue : Expr)
    (hNe : storageName ≠ localName) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage storageName slot)
        (SurfaceNamedStmt.localDecl localName init
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident localName) condValue)
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.ifThen
                (SurfaceNamedWordExpr.ident localName)
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) storedValue))
              (SurfaceNamedStmt.returnWord
                (SurfaceNamedWordExpr.ident storageName))))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.ifThen condValue
              (SurfaceStmt.storageStore slot storedValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load slot)))) := by
  let env := SurfaceNameEnv.singleStorage storageName slot
  let handle := env.nextLocalHandle
  let localInfo := SurfaceLocalInfo.uint256 handle
  let storageInfo := SurfaceStorageInfo.uint256 slot
  let localEnv :=
    env.pushScope (SurfaceNameScope.singleLocal localName handle)
  have hLocalAssignResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident localName) condValue) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.local localInfo) condValue) := by
    dsimp [localEnv, localInfo, handle]
    exact
      SurfaceNamedStmt.resolve?_assign_local_self
        env localName env.nextLocalHandle condValue
  have hCondResolve :
      SurfaceNamedWordExpr.resolve? localEnv
          (SurfaceNamedWordExpr.ident localName) =
        some (SurfaceResolvedWordExpr.local localInfo) := by
    dsimp [localEnv, localInfo, handle]
    exact
      SurfaceNamedWordExpr.resolve?_ident_local_self
        env localName env.nextLocalHandle
  have hLookupStorage :
      SurfaceNameEnv.lookupWord? localEnv storageName =
        some (SurfaceWordRef.storage storageInfo) := by
    dsimp [localEnv, storageInfo]
    rw [SurfaceNameEnv.lookupWord?_push_local_other
      (SurfaceNameEnv.singleStorage storageName slot)
      (bound := localName) (query := storageName)
      handle hNe]
    exact SurfaceNameEnv.lookupWord?_single_storage_self storageName slot
  have hStorageAssignResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident storageName) storedValue) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage storageInfo) storedValue) := by
    dsimp [SurfaceNamedStmt.resolve?, SurfaceNamedLValue.resolve?,
      SurfaceNameEnv.resolveIdentLValue?]
    rw [hLookupStorage]
    rfl
  have hIfResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.ifThen
            (SurfaceNamedWordExpr.ident localName)
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident storageName) storedValue)) =
        some
          (SurfaceResolvedStmt.ifThen
            (SurfaceResolvedWordExpr.local localInfo)
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.storage storageInfo) storedValue)) := by
    exact SurfaceNamedStmt.resolve?_ifThen hCondResolve hStorageAssignResolve
  have hStorageReturnResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident storageName)) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.storageLoad storageInfo)) := by
    dsimp [SurfaceNamedStmt.resolve?, SurfaceNamedWordExpr.resolve?,
      SurfaceNameEnv.resolveIdentRValue?]
    rw [hLookupStorage]
    rfl
  have hTailResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.ifThen
              (SurfaceNamedWordExpr.ident localName)
              (SurfaceNamedStmt.assign
                (SurfaceNamedLValue.ident storageName) storedValue))
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.ident storageName))) =
        some
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.ifThen
              (SurfaceResolvedWordExpr.local localInfo)
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo) storedValue))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad storageInfo))) := by
    exact SurfaceNamedStmt.resolve?_seq hIfResolve hStorageReturnResolve
  have hBodyResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident localName) condValue)
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.ifThen
                (SurfaceNamedWordExpr.ident localName)
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) storedValue))
              (SurfaceNamedStmt.returnWord
                (SurfaceNamedWordExpr.ident storageName)))) =
        some
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.local localInfo) condValue)
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.ifThen
                (SurfaceResolvedWordExpr.local localInfo)
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo) storedValue))
              (SurfaceResolvedStmt.returnWord
                (SurfaceResolvedWordExpr.storageLoad storageInfo)))) := by
    exact SurfaceNamedStmt.resolve?_seq hLocalAssignResolve hTailResolve
  have hResolve :
      SurfaceNamedStmt.resolve? env
          (SurfaceNamedStmt.localDecl localName init
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.assign
                (SurfaceNamedLValue.ident localName) condValue)
              (SurfaceNamedStmt.seq
                (SurfaceNamedStmt.ifThen
                  (SurfaceNamedWordExpr.ident localName)
                  (SurfaceNamedStmt.assign
                    (SurfaceNamedLValue.ident storageName) storedValue))
                (SurfaceNamedStmt.returnWord
                  (SurfaceNamedWordExpr.ident storageName))))) =
        some
          (SurfaceResolvedStmt.localDecl localInfo init
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.local localInfo) condValue)
              (SurfaceResolvedStmt.seq
                (SurfaceResolvedStmt.ifThen
                  (SurfaceResolvedWordExpr.local localInfo)
                  (SurfaceResolvedStmt.assign
                    (SurfaceResolvedLValue.storage storageInfo)
                    storedValue))
                (SurfaceResolvedStmt.returnWord
                  (SurfaceResolvedWordExpr.storageLoad storageInfo))))) := by
    dsimp [localInfo, handle, localEnv]
    exact SurfaceNamedStmt.resolve?_localDecl hBodyResolve
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [hResolve]
  simpa [storageInfo] using
    SurfaceResolvedStmt.toSurfaceStmt?_localDecl_update_if_storage_read
      localInfo init condValue storageInfo storedValue

theorem SurfaceNamedStmt.toSurfaceStmt?_localDecl_update_switch_storage_read
    (localName storageName : String)
    (slot init discrValue branchValue defaultValue : Expr)
    (label : Word)
    (hNe : storageName ≠ localName) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage storageName slot)
        (SurfaceNamedStmt.localDecl localName init
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident localName) discrValue)
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.switch1
                (SurfaceNamedWordExpr.ident localName)
                label
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) branchValue)
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) defaultValue))
              (SurfaceNamedStmt.returnWord
                (SurfaceNamedWordExpr.ident storageName))))) =
      some
        (SurfaceStmt.seq SurfaceStmt.skip
          (SurfaceStmt.seq
            (SurfaceStmt.switch1 discrValue label
              (SurfaceStmt.storageStore slot branchValue)
              (SurfaceStmt.storageStore slot defaultValue))
            (SurfaceStmt.returnStateExpr
              (StateExpr.load slot)))) := by
  let env := SurfaceNameEnv.singleStorage storageName slot
  let handle := env.nextLocalHandle
  let localInfo := SurfaceLocalInfo.uint256 handle
  let storageInfo := SurfaceStorageInfo.uint256 slot
  let localEnv :=
    env.pushScope (SurfaceNameScope.singleLocal localName handle)
  have hLocalAssignResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident localName) discrValue) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.local localInfo) discrValue) := by
    dsimp [localEnv, localInfo, handle]
    exact
      SurfaceNamedStmt.resolve?_assign_local_self
        env localName env.nextLocalHandle discrValue
  have hDiscrResolve :
      SurfaceNamedWordExpr.resolve? localEnv
          (SurfaceNamedWordExpr.ident localName) =
        some (SurfaceResolvedWordExpr.local localInfo) := by
    dsimp [localEnv, localInfo, handle]
    exact
      SurfaceNamedWordExpr.resolve?_ident_local_self
        env localName env.nextLocalHandle
  have hLookupStorage :
      SurfaceNameEnv.lookupWord? localEnv storageName =
        some (SurfaceWordRef.storage storageInfo) := by
    dsimp [localEnv, storageInfo]
    rw [SurfaceNameEnv.lookupWord?_push_local_other
      (SurfaceNameEnv.singleStorage storageName slot)
      (bound := localName) (query := storageName)
      handle hNe]
    exact SurfaceNameEnv.lookupWord?_single_storage_self storageName slot
  have hBranchResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident storageName) branchValue) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage storageInfo) branchValue) := by
    dsimp [SurfaceNamedStmt.resolve?, SurfaceNamedLValue.resolve?,
      SurfaceNameEnv.resolveIdentLValue?]
    rw [hLookupStorage]
    rfl
  have hDefaultResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident storageName) defaultValue) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage storageInfo) defaultValue) := by
    dsimp [SurfaceNamedStmt.resolve?, SurfaceNamedLValue.resolve?,
      SurfaceNameEnv.resolveIdentLValue?]
    rw [hLookupStorage]
    rfl
  have hSwitchResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.switch1
            (SurfaceNamedWordExpr.ident localName)
            label
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident storageName) branchValue)
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident storageName) defaultValue)) =
        some
          (SurfaceResolvedStmt.switch1
            (SurfaceResolvedWordExpr.local localInfo)
            label
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.storage storageInfo) branchValue)
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.storage storageInfo) defaultValue)) := by
    exact
      SurfaceNamedStmt.resolve?_switch1
        hDiscrResolve hBranchResolve hDefaultResolve
  have hStorageReturnResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident storageName)) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.storageLoad storageInfo)) := by
    dsimp [SurfaceNamedStmt.resolve?, SurfaceNamedWordExpr.resolve?,
      SurfaceNameEnv.resolveIdentRValue?]
    rw [hLookupStorage]
    rfl
  have hTailResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.switch1
              (SurfaceNamedWordExpr.ident localName)
              label
              (SurfaceNamedStmt.assign
                (SurfaceNamedLValue.ident storageName) branchValue)
              (SurfaceNamedStmt.assign
                (SurfaceNamedLValue.ident storageName) defaultValue))
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.ident storageName))) =
        some
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.switch1
              (SurfaceResolvedWordExpr.local localInfo)
              label
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo) branchValue)
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.storage storageInfo) defaultValue))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad storageInfo))) := by
    exact SurfaceNamedStmt.resolve?_seq hSwitchResolve hStorageReturnResolve
  have hBodyResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.seq
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident localName) discrValue)
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.switch1
                (SurfaceNamedWordExpr.ident localName)
                label
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) branchValue)
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident storageName) defaultValue))
              (SurfaceNamedStmt.returnWord
                (SurfaceNamedWordExpr.ident storageName)))) =
        some
          (SurfaceResolvedStmt.seq
            (SurfaceResolvedStmt.assign
              (SurfaceResolvedLValue.local localInfo) discrValue)
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.switch1
                (SurfaceResolvedWordExpr.local localInfo)
                label
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo) branchValue)
                (SurfaceResolvedStmt.assign
                  (SurfaceResolvedLValue.storage storageInfo) defaultValue))
              (SurfaceResolvedStmt.returnWord
                (SurfaceResolvedWordExpr.storageLoad storageInfo)))) := by
    exact SurfaceNamedStmt.resolve?_seq hLocalAssignResolve hTailResolve
  have hResolve :
      SurfaceNamedStmt.resolve? env
          (SurfaceNamedStmt.localDecl localName init
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.assign
                (SurfaceNamedLValue.ident localName) discrValue)
              (SurfaceNamedStmt.seq
                (SurfaceNamedStmt.switch1
                  (SurfaceNamedWordExpr.ident localName)
                  label
                  (SurfaceNamedStmt.assign
                    (SurfaceNamedLValue.ident storageName) branchValue)
                  (SurfaceNamedStmt.assign
                    (SurfaceNamedLValue.ident storageName) defaultValue))
                (SurfaceNamedStmt.returnWord
                  (SurfaceNamedWordExpr.ident storageName))))) =
        some
          (SurfaceResolvedStmt.localDecl localInfo init
            (SurfaceResolvedStmt.seq
              (SurfaceResolvedStmt.assign
                (SurfaceResolvedLValue.local localInfo) discrValue)
              (SurfaceResolvedStmt.seq
                (SurfaceResolvedStmt.switch1
                  (SurfaceResolvedWordExpr.local localInfo)
                  label
                  (SurfaceResolvedStmt.assign
                    (SurfaceResolvedLValue.storage storageInfo)
                    branchValue)
                  (SurfaceResolvedStmt.assign
                    (SurfaceResolvedLValue.storage storageInfo)
                    defaultValue))
                (SurfaceResolvedStmt.returnWord
                  (SurfaceResolvedWordExpr.storageLoad storageInfo))))) := by
    dsimp [localInfo, handle, localEnv]
    exact SurfaceNamedStmt.resolve?_localDecl hBodyResolve
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [hResolve]
  simpa [storageInfo] using
    SurfaceResolvedStmt.toSurfaceStmt?_localDecl_update_switch_storage_read
      localInfo init discrValue storageInfo label branchValue defaultValue

theorem SurfaceNamedStmt.toSurfaceStmt?_localDecl_returnWord_add_self_pure
    (env : SurfaceNameEnv) (name : String) (init rhs : Expr) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.localDecl
          name init
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.add
              (SurfaceNamedWordExpr.ident name)
              (SurfaceNamedWordExpr.pure rhs)))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.add
            (StateExpr.pure init)
            (StateExpr.pure rhs))) := by
  let localEnv :=
    env.pushScope
      (SurfaceNameScope.singleLocal name env.nextLocalHandle)
  let localInfo := SurfaceLocalInfo.uint256 env.nextLocalHandle
  have hSelf :
      SurfaceNamedWordExpr.resolve? localEnv
          (SurfaceNamedWordExpr.ident name) =
        some (SurfaceResolvedWordExpr.local localInfo) := by
    dsimp [localEnv, localInfo]
    exact
      SurfaceNamedWordExpr.resolve?_ident_local_self
        env name env.nextLocalHandle
  have hPure :
      SurfaceNamedWordExpr.resolve? localEnv
          (SurfaceNamedWordExpr.pure rhs) =
        some (SurfaceResolvedWordExpr.pure rhs) := by
    rfl
  have hReturnResolve :
      SurfaceNamedStmt.resolve? localEnv
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.add
              (SurfaceNamedWordExpr.ident name)
              (SurfaceNamedWordExpr.pure rhs))) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.add
              (SurfaceResolvedWordExpr.local localInfo)
              (SurfaceResolvedWordExpr.pure rhs))) := by
    dsimp [SurfaceNamedStmt.resolve?]
    rw [SurfaceNamedWordExpr.resolve?_add hSelf hPure]
  have hResolve :
      SurfaceNamedStmt.resolve? env
          (SurfaceNamedStmt.localDecl
            name init
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.add
                (SurfaceNamedWordExpr.ident name)
                (SurfaceNamedWordExpr.pure rhs)))) =
        some
          (SurfaceResolvedStmt.localDecl
            localInfo init
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.add
                (SurfaceResolvedWordExpr.local localInfo)
                (SurfaceResolvedWordExpr.pure rhs)))) := by
    dsimp [localInfo]
    exact SurfaceNamedStmt.resolve?_localDecl hReturnResolve
  have hLocal :
      SurfaceResolvedWordExpr.toStateExprWithLocal?
          localInfo init
          (SurfaceResolvedWordExpr.local localInfo) =
        some (StateExpr.pure init) :=
    SurfaceResolvedWordExpr.toStateExprWithLocal?_local_self
      localInfo init
  have hPureLower :
      SurfaceResolvedWordExpr.toStateExprWithLocal?
          localInfo init
          (SurfaceResolvedWordExpr.pure rhs) =
        some (StateExpr.pure rhs) := by
    rfl
  have hLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.localDecl
            localInfo init
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.add
                (SurfaceResolvedWordExpr.local localInfo)
                (SurfaceResolvedWordExpr.pure rhs)))) =
        some
          (SurfaceStmt.returnStateExpr
            (StateExpr.add
              (StateExpr.pure init)
              (StateExpr.pure rhs))) :=
    SurfaceResolvedStmt.toSurfaceStmt?_localDecl_returnWord_add_withLocal
      hLocal hPureLower
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [hResolve]
  exact hLower

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_pure
    (env : SurfaceNameEnv) (expr : Expr) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.pure expr)) =
      some (SurfaceStmt.returnExpr expr) := by
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_storage_self
    (name : String) (slot : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident name)) =
      some (SurfaceStmt.returnStateExpr (StateExpr.load slot)) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_returnWord_storage_self]
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_storage_add_pure_self
    (name : String) (slot rhs : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.add
            (SurfaceNamedWordExpr.ident name)
            (SurfaceNamedWordExpr.pure rhs))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.add
            (StateExpr.load slot)
            (StateExpr.pure rhs))) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?, SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_add
    (SurfaceNamedWordExpr.resolve?_ident_storage_self name slot)
    (SurfaceNamedWordExpr.resolve?_pure
      (SurfaceNameEnv.singleStorage name slot) rhs)]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_returnWord_add
      (by rfl) (by rfl)

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_storage_mul_pure_self
    (name : String) (slot rhs : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.mul
            (SurfaceNamedWordExpr.ident name)
            (SurfaceNamedWordExpr.pure rhs))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.mul
            (StateExpr.load slot)
            (StateExpr.pure rhs))) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?, SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_mul
    (SurfaceNamedWordExpr.resolve?_ident_storage_self name slot)
    (SurfaceNamedWordExpr.resolve?_pure
      (SurfaceNameEnv.singleStorage name slot) rhs)]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_returnWord_mul
      (by rfl) (by rfl)

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_storage_iszero_self
    (name : String) (slot : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.iszero
            (SurfaceNamedWordExpr.ident name))) =
      some
        (SurfaceStmt.returnStateExpr
          (StateExpr.iszero (StateExpr.load slot))) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?, SurfaceNamedStmt.resolve?]
  rw [SurfaceNamedWordExpr.resolve?_iszero
    (SurfaceNamedWordExpr.resolve?_ident_storage_self name slot)]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_returnWord_iszero
      (by rfl)

theorem SurfaceNamedStmt.toSurfaceStmt?_returnWord_local_rejected
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNamedStmt.toSurfaceStmt?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident name)) =
      none := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_returnWord_local_self]
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_assign_storage_self
    (name : String) (slot value : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.assign
          (SurfaceNamedLValue.ident name) value) =
      some (SurfaceStmt.storageStore slot value) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_assign_storage_self]
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_assign_local_rejected
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) (value : Expr) :
    SurfaceNamedStmt.toSurfaceStmt?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        (SurfaceNamedStmt.assign
          (SurfaceNamedLValue.ident name) value) =
      none := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_assign_local_self]
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_skip
    (env : SurfaceNameEnv) :
    SurfaceNamedStmt.toSurfaceStmt? env SurfaceNamedStmt.skip =
      some SurfaceStmt.skip := by
  rfl

theorem SurfaceNamedStmt.toSurfaceStmt?_seq
    {env : SurfaceNameEnv} {first second : SurfaceNamedStmt}
    {resolvedFirst resolvedSecond : SurfaceResolvedStmt}
    {firstStmt secondStmt : SurfaceStmt}
    (hFirstResolve :
      first.resolve? env = some resolvedFirst)
    (hSecondResolve :
      second.resolve? env = some resolvedSecond)
    (hFirstLower :
      resolvedFirst.toSurfaceStmt? = some firstStmt)
    (hSecondLower :
      resolvedSecond.toSurfaceStmt? = some secondStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.seq first second) =
      some (SurfaceStmt.seq firstStmt secondStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_seq hFirstResolve hSecondResolve]
  exact SurfaceResolvedStmt.toSurfaceStmt?_seq hFirstLower hSecondLower

theorem SurfaceNamedStmt.toSurfaceStmt?_ifThen
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {body : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedBody : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCondResolve :
      cond.resolve? env = some resolvedCond)
    (hBodyResolve :
      body.resolve? env = some resolvedBody)
    (hCondLower :
      resolvedCond.toPureExpr? = some condExpr)
    (hBodyLower :
      resolvedBody.toSurfaceStmt? = some bodyStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.ifThen cond body) =
      some (SurfaceStmt.ifThen condExpr bodyStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_ifThen hCondResolve hBodyResolve]
  exact SurfaceResolvedStmt.toSurfaceStmt?_ifThen hCondLower hBodyLower

theorem SurfaceNamedStmt.toSurfaceStmt?_ifElse
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {thenBranch elseBranch : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedThen resolvedElse : SurfaceResolvedStmt}
    {condExpr : Expr} {thenStmt elseStmt : SurfaceStmt}
    (hCondResolve :
      cond.resolve? env = some resolvedCond)
    (hThenResolve :
      thenBranch.resolve? env = some resolvedThen)
    (hElseResolve :
      elseBranch.resolve? env = some resolvedElse)
    (hCondLower :
      resolvedCond.toPureExpr? = some condExpr)
    (hThenLower :
      resolvedThen.toSurfaceStmt? = some thenStmt)
    (hElseLower :
      resolvedElse.toSurfaceStmt? = some elseStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.ifElse cond thenBranch elseBranch) =
      some (SurfaceStmt.switch1 condExpr 0 elseStmt thenStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_ifElse
    hCondResolve hThenResolve hElseResolve]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_ifElse
      hCondLower hThenLower hElseLower

theorem SurfaceNamedStmt.toSurfaceStmt?_switch1
    {env : SurfaceNameEnv} {discr : SurfaceNamedWordExpr}
    {label : Word} {branch defaultBranch : SurfaceNamedStmt}
    {resolvedDiscr : SurfaceResolvedWordExpr}
    {resolvedBranch resolvedDefault : SurfaceResolvedStmt}
    {discrExpr : Expr} {branchStmt defaultStmt : SurfaceStmt}
    (hDiscrResolve :
      discr.resolve? env = some resolvedDiscr)
    (hBranchResolve :
      branch.resolve? env = some resolvedBranch)
    (hDefaultResolve :
      defaultBranch.resolve? env = some resolvedDefault)
    (hDiscrLower :
      resolvedDiscr.toPureExpr? = some discrExpr)
    (hBranchLower :
      resolvedBranch.toSurfaceStmt? = some branchStmt)
    (hDefaultLower :
      resolvedDefault.toSurfaceStmt? = some defaultStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.switch1
          discr label branch defaultBranch) =
      some
        (SurfaceStmt.switch1
          discrExpr label branchStmt defaultStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_switch1
    hDiscrResolve hBranchResolve hDefaultResolve]
  exact
    SurfaceResolvedStmt.toSurfaceStmt?_switch1
      hDiscrLower hBranchLower hDefaultLower

theorem SurfaceNamedStmt.toSurfaceStmt?_forOnce
    {env : SurfaceNameEnv} {body : SurfaceNamedStmt}
    {resolvedBody : SurfaceResolvedStmt}
    {bodyStmt : SurfaceStmt}
    (hBodyResolve :
      body.resolve? env = some resolvedBody)
    (hBodyLower :
      resolvedBody.toSurfaceStmt? = some bodyStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.forOnce body) =
      some (SurfaceStmt.forOnce bodyStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_forOnce hBodyResolve]
  exact SurfaceResolvedStmt.toSurfaceStmt?_forOnce hBodyLower

theorem SurfaceNamedStmt.toSurfaceStmt?_forIf
    {env : SurfaceNameEnv} {cond : SurfaceNamedWordExpr}
    {body : SurfaceNamedStmt}
    {resolvedCond : SurfaceResolvedWordExpr}
    {resolvedBody : SurfaceResolvedStmt}
    {condExpr : Expr} {bodyStmt : SurfaceStmt}
    (hCondResolve :
      cond.resolve? env = some resolvedCond)
    (hBodyResolve :
      body.resolve? env = some resolvedBody)
    (hCondLower :
      resolvedCond.toPureExpr? = some condExpr)
    (hBodyLower :
      resolvedBody.toSurfaceStmt? = some bodyStmt) :
    SurfaceNamedStmt.toSurfaceStmt? env
        (SurfaceNamedStmt.forIf cond body) =
      some (SurfaceStmt.forIf condExpr bodyStmt) := by
  dsimp [SurfaceNamedStmt.toSurfaceStmt?]
  rw [SurfaceNamedStmt.resolve?_forIf hCondResolve hBodyResolve]
  exact SurfaceResolvedStmt.toSurfaceStmt?_forIf hCondLower hBodyLower

theorem SurfaceNamedStmt.toSurfaceProgram?_localDecl_returnWord_self
    (env : SurfaceNameEnv) (name : String) (init : Expr) :
    SurfaceNamedStmt.toSurfaceProgram? env
        (SurfaceNamedStmt.localDecl
          name init
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.ident name))) =
      some { body := SurfaceStmt.returnStateExpr (StateExpr.pure init) } := by
  dsimp [SurfaceNamedStmt.toSurfaceProgram?]
  rw [SurfaceNamedStmt.toSurfaceStmt?_localDecl_returnWord_self]

theorem SurfaceNamedStmt.toSurfaceProgram?_returnWord_storage_self
    (name : String) (slot : Expr) :
    SurfaceNamedStmt.toSurfaceProgram?
        (SurfaceNameEnv.singleStorage name slot)
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident name)) =
      some { body := SurfaceStmt.returnStateExpr (StateExpr.load slot) } := by
  dsimp [SurfaceNamedStmt.toSurfaceProgram?]
  rw [SurfaceNamedStmt.toSurfaceStmt?_returnWord_storage_self]

theorem SurfaceNameEnv.lookupLocalWord?_push_local_self
    (env : SurfaceNameEnv) (name : String)
    (handle : SurfaceLocalHandle) :
    SurfaceNameEnv.lookupLocalWord?
        (env.pushScope
          (SurfaceNameScope.singleLocal name handle))
        name =
      some (SurfaceLocalInfo.uint256 handle) := by
  dsimp [SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.pushScope,
    SurfaceNameScope.singleLocal]
  rw [if_pos rfl]

theorem SurfaceNameEnv.lookupLocalWord?_push_local_other
    (env : SurfaceNameEnv) {bound query : String}
    (handle : SurfaceLocalHandle) (hNe : query ≠ bound) :
    SurfaceNameEnv.lookupLocalWord?
        (env.pushScope
          (SurfaceNameScope.singleLocal bound handle))
        query =
      SurfaceNameEnv.lookupLocalWord? env query := by
  dsimp [SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.pushScope,
    SurfaceNameScope.singleLocal]
  rw [if_neg hNe]

def surfaceContractStorageNameEnv : SurfaceNameEnv :=
  SurfaceNameEnv.singleStorage "x" (Expr.lit 0)

theorem surfaceContractStorageNameEnv_lookup_x :
    SurfaceNameEnv.lookupStorageSlot?
        surfaceContractStorageNameEnv "x" =
      some (Expr.lit 0) := by
  rfl

theorem surfaceContractStorageNameEnv_lookup_unknown :
    SurfaceNameEnv.lookupStorageSlot?
        surfaceContractStorageNameEnv "y" = none := by
  rfl

def surfaceNestedNameEnv : SurfaceNameEnv :=
  surfaceContractStorageNameEnv.pushScope
    (SurfaceNameScope.singleLocal "y" { index := 1 })

theorem surfaceNestedNameEnv_lookup_outer_storage :
    SurfaceNameEnv.lookupStorageSlot?
        surfaceNestedNameEnv "x" =
      some (Expr.lit 0) := by
  rfl

theorem surfaceNestedNameEnv_lookup_inner_local :
    SurfaceNameEnv.lookupLocalWord?
        surfaceNestedNameEnv "y" =
      some (SurfaceLocalInfo.uint256 { index := 1 }) := by
  rfl

def surfaceLocalShadowedStorageNameEnv : SurfaceNameEnv :=
  surfaceContractStorageNameEnv.pushScope
    (SurfaceNameScope.singleLocal "x" { index := 1 })

theorem surfaceLocalShadowedStorageNameEnv_lookup_x :
    SurfaceNameEnv.lookupWord?
        surfaceLocalShadowedStorageNameEnv "x" =
      some
        (SurfaceWordRef.local
          (SurfaceLocalInfo.uint256 { index := 1 })) := by
  rfl

def surfaceLocalShadowsStorageNameEnv : SurfaceNameEnv :=
  surfaceContractStorageNameEnv.pushScope
    (SurfaceNameScope.singleLocal "x" SurfaceLocalHandle.first)

theorem surfaceLocalShadowsStorageNameEnv_lookup_local_x :
    SurfaceNameEnv.lookupLocalWord?
        surfaceLocalShadowsStorageNameEnv "x" =
      some (SurfaceLocalInfo.uint256 SurfaceLocalHandle.first) := by
  rfl

theorem surfaceLocalShadowsStorageNameEnv_lookup_outer_storage_x :
    SurfaceNameEnv.lookupStorageSlot?
        surfaceLocalShadowsStorageNameEnv "x" =
      some (Expr.lit 0) := by
  rfl

theorem surfaceLocalShadowsStorageNameEnv_lookup_word_x :
    SurfaceNameEnv.lookupWord?
        surfaceLocalShadowsStorageNameEnv "x" =
      some
        (SurfaceWordRef.local
          (SurfaceLocalInfo.uint256 SurfaceLocalHandle.first)) := by
  exact
    SurfaceNameEnv.lookupWord?_push_local_self
      surfaceContractStorageNameEnv "x" SurfaceLocalHandle.first

theorem surfaceContractStorageNameEnv_lookup_word_x :
    SurfaceNameEnv.lookupWord?
        surfaceContractStorageNameEnv "x" =
      some
        (SurfaceWordRef.storage
          (SurfaceStorageInfo.uint256 (Expr.lit 0))) := by
  rfl

def surfaceNamedReturnStorageStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.returnWord (SurfaceNamedWordExpr.ident "x")

def surfaceNamedReturnStorageProgram : SurfaceProgram :=
  { body := SurfaceStmt.returnStateExpr (StateExpr.load (Expr.lit 0)) }

def surfaceNamedReturnStorageArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedReturnStorageProgram

theorem surfaceNamedReturnStorageStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedReturnStorageStmt =
      some surfaceNamedReturnStorageProgram := by
  dsimp [surfaceNamedReturnStorageStmt,
    surfaceNamedReturnStorageProgram,
    surfaceContractStorageNameEnv]
  rw [SurfaceNamedStmt.toSurfaceProgram?_returnWord_storage_self]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedReturnStorageStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedReturnStorageStmt =
      some surfaceNamedReturnStorageArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedReturnStorageArtifact]
  rw [surfaceNamedReturnStorageStmt_toSurfaceProgram]

theorem surfaceNamedReturnStorageStmt_staticChecked :
    SolidCoreYulCore.FullYul.checkStmtFuel
        surfaceNamedReturnStorageArtifact.sourceArtifact.stmtArtifact.fuel
        initialStaticContext false true
        surfaceNamedReturnStorageArtifact.sourceArtifact.stmtArtifact.stmt =
      some initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_staticChecked
      surfaceNamedReturnStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedReturnStorageStmt

theorem surfaceNamedReturnStorageStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedReturnStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedReturnStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedReturnStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedReturnStorageStmt

def surfaceNamedStorageAssignSwitchStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.seq
    (SurfaceNamedStmt.assign
      (SurfaceNamedLValue.ident "x")
      (Expr.lit 5))
    (SurfaceNamedStmt.switch1
      (SurfaceNamedWordExpr.pure (Expr.lit 5))
      5
      surfaceNamedReturnStorageStmt
      (SurfaceNamedStmt.returnWord
        (SurfaceNamedWordExpr.add
          (SurfaceNamedWordExpr.ident "x")
          (SurfaceNamedWordExpr.pure (Expr.lit 1)))))

theorem surfaceNamedStorageAssignSwitchStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedStorageAssignSwitchStmt =
      some surfaceParsedContractStorageVarSwitchProgram := by
  have hFirstResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident "x")
            (Expr.lit 5)) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))
            (Expr.lit 5)) := by
    exact
      SurfaceNamedStmt.resolve?_assign_storage_self
        "x" (Expr.lit 0) (Expr.lit 5)
  have hDiscrResolve :
      SurfaceNamedWordExpr.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedWordExpr.pure (Expr.lit 5)) =
        some (SurfaceResolvedWordExpr.pure (Expr.lit 5)) := by
    rfl
  have hBranchResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          surfaceNamedReturnStorageStmt =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.storageLoad
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))) := by
    dsimp [surfaceNamedReturnStorageStmt]
    exact SurfaceNamedStmt.resolve?_returnWord_storage_self "x" (Expr.lit 0)
  have hDefaultResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.add
              (SurfaceNamedWordExpr.ident "x")
              (SurfaceNamedWordExpr.pure (Expr.lit 1)))) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.add
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0)))
              (SurfaceResolvedWordExpr.pure (Expr.lit 1)))) := by
    dsimp [SurfaceNamedStmt.resolve?, surfaceContractStorageNameEnv]
    rw [SurfaceNamedWordExpr.resolve?_add
      (SurfaceNamedWordExpr.resolve?_ident_storage_self
        "x" (Expr.lit 0))
      (SurfaceNamedWordExpr.resolve?_pure
        (SurfaceNameEnv.singleStorage "x" (Expr.lit 0)) (Expr.lit 1))]
  have hSecondResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedStmt.switch1
            (SurfaceNamedWordExpr.pure (Expr.lit 5))
            5
            surfaceNamedReturnStorageStmt
            (SurfaceNamedStmt.returnWord
              (SurfaceNamedWordExpr.add
                (SurfaceNamedWordExpr.ident "x")
                (SurfaceNamedWordExpr.pure (Expr.lit 1))))) =
        some
          (SurfaceResolvedStmt.switch1
            (SurfaceResolvedWordExpr.pure (Expr.lit 5))
            5
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0))))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.add
                (SurfaceResolvedWordExpr.storageLoad
                  (SurfaceStorageInfo.uint256 (Expr.lit 0)))
                (SurfaceResolvedWordExpr.pure (Expr.lit 1))))) := by
    exact
      SurfaceNamedStmt.resolve?_switch1
        hDiscrResolve hBranchResolve hDefaultResolve
  have hFirstLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))
            (Expr.lit 5)) =
        some (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 5)) := by
    rfl
  have hBranchLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.storageLoad
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))) =
        some
          (SurfaceStmt.returnStateExpr
            (StateExpr.load (Expr.lit 0))) := by
    rfl
  have hDefaultLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.add
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0)))
              (SurfaceResolvedWordExpr.pure (Expr.lit 1)))) =
        some
          (SurfaceStmt.returnStateExpr
            (StateExpr.add
              (StateExpr.load (Expr.lit 0))
              (StateExpr.pure (Expr.lit 1)))) := by
    exact
      SurfaceResolvedStmt.toSurfaceStmt?_returnWord_add
        (by rfl) (by rfl)
  have hSecondLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.switch1
            (SurfaceResolvedWordExpr.pure (Expr.lit 5))
            5
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0))))
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.add
                (SurfaceResolvedWordExpr.storageLoad
                  (SurfaceStorageInfo.uint256 (Expr.lit 0)))
                (SurfaceResolvedWordExpr.pure (Expr.lit 1))))) =
        some
          (SurfaceStmt.switch1
            (Expr.lit 5)
            5
            (SurfaceStmt.returnStateExpr
              (StateExpr.load (Expr.lit 0)))
            (SurfaceStmt.returnStateExpr
              (StateExpr.add
                (StateExpr.load (Expr.lit 0))
                (StateExpr.pure (Expr.lit 1))))) := by
    exact
      SurfaceResolvedStmt.toSurfaceStmt?_switch1
        (by rfl) hBranchLower hDefaultLower
  dsimp [surfaceNamedStorageAssignSwitchStmt,
    surfaceParsedContractStorageVarSwitchProgram,
    SurfaceStmt.switchCases,
    SurfaceNamedStmt.toSurfaceProgram?]
  rw [SurfaceNamedStmt.toSurfaceStmt?_seq
    hFirstResolve hSecondResolve hFirstLower hSecondLower]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedStorageAssignSwitchStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedStorageAssignSwitchStmt =
      some surfaceParsedContractStorageVarSwitchArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?]
  rw [surfaceNamedStorageAssignSwitchStmt_toSurfaceProgram]
  rfl

theorem surfaceNamedStorageAssignSwitchStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractStorageVarSwitchArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedStorageAssignSwitchStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedStorageAssignSwitchStmt

def surfaceNamedSwitchCasesBuiltinStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.switchCases
    (SurfaceNamedWordExpr.pure (Expr.lit 3))
    [ (1,
        SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.pure (Expr.lit 9)))
    , (2,
        SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.pure
            (Expr.addmod (Expr.lit 2) (Expr.lit 3) (Expr.lit 5)))) ]
    (SurfaceNamedStmt.returnWord
      (SurfaceNamedWordExpr.pure (Expr.lit 11)))

def surfaceNamedSwitchCasesBuiltinArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedSwitchBuiltinProgram

theorem surfaceNamedSwitchCasesBuiltinStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        SurfaceNameEnv.empty
        surfaceNamedSwitchCasesBuiltinStmt =
      some surfaceParsedSwitchBuiltinProgram := by
  rfl

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedSwitchCasesBuiltinStmt :
    compileSurfaceNamedStmtArtifact?
        SurfaceNameEnv.empty
        surfaceNamedSwitchCasesBuiltinStmt =
      some surfaceNamedSwitchCasesBuiltinArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedSwitchCasesBuiltinArtifact]
  rw [surfaceNamedSwitchCasesBuiltinStmt_toSurfaceProgram]

theorem surfaceNamedSwitchCasesBuiltinStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedSwitchCasesBuiltinArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedSwitchCasesBuiltinArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedSwitchCasesBuiltinStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedSwitchCasesBuiltinStmt

def surfaceNamedIfElseStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.ifElse
    (SurfaceNamedWordExpr.pure (Expr.lit 0))
    (SurfaceNamedStmt.returnWord
      (SurfaceNamedWordExpr.pure (Expr.lit 7)))
    (SurfaceNamedStmt.returnWord
      (SurfaceNamedWordExpr.pure (Expr.lit 11)))

def surfaceNamedIfElseArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceParsedIfElseProgram

theorem surfaceNamedIfElseStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        SurfaceNameEnv.empty
        surfaceNamedIfElseStmt =
      some surfaceParsedIfElseProgram := by
  rfl

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedIfElseStmt :
    compileSurfaceNamedStmtArtifact?
        SurfaceNameEnv.empty
        surfaceNamedIfElseStmt =
      some surfaceNamedIfElseArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedIfElseArtifact]
  rw [surfaceNamedIfElseStmt_toSurfaceProgram]

theorem surfaceNamedIfElseStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedIfElseArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedIfElseArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedIfElseStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedIfElseStmt

def surfaceNamedBoundedWhileStorageStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.seq
    (SurfaceNamedStmt.boundedWhile 2
      (SurfaceNamedWordExpr.pure (Expr.lit 1))
      (SurfaceNamedStmt.assign
        (SurfaceNamedLValue.ident "x")
        (Expr.add (Expr.lit 2) (Expr.lit 3))))
    surfaceNamedReturnStorageStmt

def surfaceNamedBoundedWhileStorageProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        (SurfaceStmt.boundedWhile 2 (Expr.lit 1)
          (SurfaceStmt.storageStore
            (Expr.lit 0) (Expr.add (Expr.lit 2) (Expr.lit 3))))
        (SurfaceStmt.returnStateExpr
          (StateExpr.load (Expr.lit 0))) }

def surfaceParsedContractStorageVarBoundedWhileSource : String :=
  "contract Main { uint256 x; function main() public returns (uint256) { boundedWhile 2 1 { x = 2 + 3; } return x; } }"

def surfaceNamedBoundedWhileStorageArtifact :
    SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedBoundedWhileStorageProgram

theorem surfaceNamedBoundedWhileStorageStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedBoundedWhileStorageStmt =
      some surfaceNamedBoundedWhileStorageProgram := by
  rfl

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedBoundedWhileStorageStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedBoundedWhileStorageStmt =
      some surfaceNamedBoundedWhileStorageArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedBoundedWhileStorageArtifact]
  rw [surfaceNamedBoundedWhileStorageStmt_toSurfaceProgram]

theorem surfaceNamedBoundedWhileStorageStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedBoundedWhileStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedBoundedWhileStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedBoundedWhileStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedBoundedWhileStorageStmt

def surfaceNamedStorageIszeroReturnStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.seq
    (SurfaceNamedStmt.assign
      (SurfaceNamedLValue.ident "x")
      (Expr.lit 0))
    (SurfaceNamedStmt.returnWord
      (SurfaceNamedWordExpr.iszero
        (SurfaceNamedWordExpr.ident "x")))

theorem surfaceNamedStorageIszeroReturnStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedStorageIszeroReturnStmt =
      some surfaceParsedStoredStateExprIszeroProgram := by
  have hFirstResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident "x")
            (Expr.lit 0)) =
        some
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))
            (Expr.lit 0)) := by
    exact
      SurfaceNamedStmt.resolve?_assign_storage_self
        "x" (Expr.lit 0) (Expr.lit 0)
  have hSecondResolve :
      SurfaceNamedStmt.resolve?
          surfaceContractStorageNameEnv
          (SurfaceNamedStmt.returnWord
            (SurfaceNamedWordExpr.iszero
              (SurfaceNamedWordExpr.ident "x"))) =
        some
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.iszero
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0))))) := by
    dsimp [SurfaceNamedStmt.resolve?, surfaceContractStorageNameEnv]
    rw [SurfaceNamedWordExpr.resolve?_iszero
      (SurfaceNamedWordExpr.resolve?_ident_storage_self
        "x" (Expr.lit 0))]
  have hFirstLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.assign
            (SurfaceResolvedLValue.storage
              (SurfaceStorageInfo.uint256 (Expr.lit 0)))
            (Expr.lit 0)) =
        some (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 0)) := by
    rfl
  have hSecondLower :
      SurfaceResolvedStmt.toSurfaceStmt?
          (SurfaceResolvedStmt.returnWord
            (SurfaceResolvedWordExpr.iszero
              (SurfaceResolvedWordExpr.storageLoad
                (SurfaceStorageInfo.uint256 (Expr.lit 0))))) =
        some
          (SurfaceStmt.returnStateExpr
            (StateExpr.iszero (StateExpr.load (Expr.lit 0)))) := by
    exact
      SurfaceResolvedStmt.toSurfaceStmt?_returnWord_iszero
        (by rfl)
  dsimp [surfaceNamedStorageIszeroReturnStmt,
    surfaceParsedStoredStateExprIszeroProgram,
    SurfaceNamedStmt.toSurfaceProgram?]
  rw [SurfaceNamedStmt.toSurfaceStmt?_seq
    hFirstResolve hSecondResolve hFirstLower hSecondLower]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedStorageIszeroReturnStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedStorageIszeroReturnStmt =
      some surfaceParsedStoredStateExprIszeroArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?]
  rw [surfaceNamedStorageIszeroReturnStmt_toSurfaceProgram]
  rfl

theorem surfaceNamedStorageIszeroReturnStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedStoredStateExprIszeroArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedStorageIszeroReturnStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedStorageIszeroReturnStmt

def surfaceNamedScopedLocalShadowsStorageStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "x" (Expr.lit 9)
    (SurfaceNamedStmt.returnWord (SurfaceNamedWordExpr.ident "x"))

theorem surfaceNamedScopedLocalShadowsStorageStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedScopedLocalShadowsStorageStmt =
      some surfaceParsedContractLocalShadowsStorageProgram := by
  dsimp [surfaceNamedScopedLocalShadowsStorageStmt,
    surfaceParsedContractLocalShadowsStorageProgram]
  rw [SurfaceNamedStmt.toSurfaceProgram?_localDecl_returnWord_self]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedScopedLocalShadowsStorageStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedScopedLocalShadowsStorageStmt =
      some surfaceParsedContractLocalShadowsStorageArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?]
  rw [surfaceNamedScopedLocalShadowsStorageStmt_toSurfaceProgram]
  rfl

theorem surfaceNamedScopedLocalShadowsStorageStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceParsedContractLocalShadowsStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedScopedLocalShadowsStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedScopedLocalShadowsStorageStmt

def surfaceNamedLocalAddReturnStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "x" (Expr.lit 9)
    (SurfaceNamedStmt.returnWord
      (SurfaceNamedWordExpr.add
        (SurfaceNamedWordExpr.ident "x")
        (SurfaceNamedWordExpr.pure (Expr.lit 4))))

def surfaceNamedLocalAddReturnProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.returnStateExpr
        (StateExpr.add
          (StateExpr.pure (Expr.lit 9))
          (StateExpr.pure (Expr.lit 4))) }

def surfaceNamedLocalAddReturnArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedLocalAddReturnProgram

theorem surfaceNamedLocalAddReturnStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAddReturnStmt =
      some surfaceNamedLocalAddReturnProgram := by
  dsimp [surfaceNamedLocalAddReturnStmt,
    surfaceNamedLocalAddReturnProgram,
    SurfaceNamedStmt.toSurfaceProgram?]
  rw [SurfaceNamedStmt.toSurfaceStmt?_localDecl_returnWord_add_self_pure]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAddReturnStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAddReturnStmt =
      some surfaceNamedLocalAddReturnArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedLocalAddReturnArtifact]
  rw [surfaceNamedLocalAddReturnStmt_toSurfaceProgram]

theorem surfaceNamedLocalAddReturnStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedLocalAddReturnArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedLocalAddReturnArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedLocalAddReturnStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAddReturnStmt

def surfaceNamedTwoLocalAddReturnStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "x" (Expr.lit 2)
    (SurfaceNamedStmt.localDecl
      "y" (Expr.lit 3)
      (SurfaceNamedStmt.returnWord
        (SurfaceNamedWordExpr.add
          (SurfaceNamedWordExpr.ident "x")
          (SurfaceNamedWordExpr.ident "y"))))

def surfaceNamedTwoLocalAddReturnProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.returnStateExpr
        (StateExpr.add
          (StateExpr.pure (Expr.lit 2))
          (StateExpr.pure (Expr.lit 3))) }

def surfaceNamedTwoLocalAddReturnArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedTwoLocalAddReturnProgram

theorem surfaceNamedTwoLocalAddReturnStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedTwoLocalAddReturnStmt =
      some surfaceNamedTwoLocalAddReturnProgram := by
  rfl

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedTwoLocalAddReturnStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedTwoLocalAddReturnStmt =
      some surfaceNamedTwoLocalAddReturnArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedTwoLocalAddReturnArtifact]
  rw [surfaceNamedTwoLocalAddReturnStmt_toSurfaceProgram]

theorem surfaceNamedTwoLocalAddReturnStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedTwoLocalAddReturnArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedTwoLocalAddReturnArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedTwoLocalAddReturnStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedTwoLocalAddReturnStmt

def surfaceNamedLocalAssignIfStorageStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "y" (Expr.lit 0)
    (SurfaceNamedStmt.seq
      (SurfaceNamedStmt.assign
        (SurfaceNamedLValue.ident "y")
        (Expr.lit 1))
      (SurfaceNamedStmt.seq
        (SurfaceNamedStmt.ifThen
          (SurfaceNamedWordExpr.ident "y")
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident "x")
            (Expr.lit 8)))
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident "x"))))

def surfaceNamedLocalAssignIfStorageProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        SurfaceStmt.skip
        (SurfaceStmt.seq
          (SurfaceStmt.ifThen (Expr.lit 1)
            (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 8)))
          (SurfaceStmt.returnStateExpr
            (StateExpr.load (Expr.lit 0)))) }

def surfaceNamedLocalAssignIfStorageArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedLocalAssignIfStorageProgram

theorem surfaceNamedLocalAssignIfStorageStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAssignIfStorageStmt =
      some surfaceNamedLocalAssignIfStorageProgram := by
  dsimp [SurfaceNamedStmt.toSurfaceProgram?,
    surfaceContractStorageNameEnv,
    surfaceNamedLocalAssignIfStorageStmt,
    surfaceNamedLocalAssignIfStorageProgram]
  rw [SurfaceNamedStmt.toSurfaceStmt?_localDecl_update_if_storage_read
    "y" "x" (Expr.lit 0) (Expr.lit 0) (Expr.lit 1) (Expr.lit 8)
    (by decide)]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAssignIfStorageStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAssignIfStorageStmt =
      some surfaceNamedLocalAssignIfStorageArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedLocalAssignIfStorageArtifact]
  rw [surfaceNamedLocalAssignIfStorageStmt_toSurfaceProgram]

theorem surfaceNamedLocalAssignIfStorageStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedLocalAssignIfStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedLocalAssignIfStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedLocalAssignIfStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAssignIfStorageStmt

def surfaceNamedLocalAssignSwitchStorageStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "y" (Expr.lit 0)
    (SurfaceNamedStmt.seq
      (SurfaceNamedStmt.assign
        (SurfaceNamedLValue.ident "y")
        (Expr.lit 2))
      (SurfaceNamedStmt.seq
        (SurfaceNamedStmt.switch1
          (SurfaceNamedWordExpr.ident "y")
          2
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident "x")
            (Expr.lit 8))
          (SurfaceNamedStmt.assign
            (SurfaceNamedLValue.ident "x")
            (Expr.lit 3)))
        (SurfaceNamedStmt.returnWord
          (SurfaceNamedWordExpr.ident "x"))))

def surfaceNamedLocalAssignSwitchStorageProgram : SurfaceProgram :=
  { body :=
      SurfaceStmt.seq
        SurfaceStmt.skip
        (SurfaceStmt.seq
          (SurfaceStmt.switch1 (Expr.lit 2) 2
            (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 8))
            (SurfaceStmt.storageStore (Expr.lit 0) (Expr.lit 3)))
          (SurfaceStmt.returnStateExpr
            (StateExpr.load (Expr.lit 0)))) }

def surfaceNamedLocalAssignSwitchStorageArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedLocalAssignSwitchStorageProgram

theorem surfaceNamedLocalAssignSwitchStorageStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAssignSwitchStorageStmt =
      some surfaceNamedLocalAssignSwitchStorageProgram := by
  dsimp [SurfaceNamedStmt.toSurfaceProgram?,
    surfaceContractStorageNameEnv,
    surfaceNamedLocalAssignSwitchStorageStmt,
    surfaceNamedLocalAssignSwitchStorageProgram]
  rw [
    SurfaceNamedStmt.toSurfaceStmt?_localDecl_update_switch_storage_read
      "y" "x" (Expr.lit 0) (Expr.lit 0) (Expr.lit 2)
      (Expr.lit 8) (Expr.lit 3) 2 (by decide)]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAssignSwitchStorageStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedLocalAssignSwitchStorageStmt =
      some surfaceNamedLocalAssignSwitchStorageArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedLocalAssignSwitchStorageArtifact]
  rw [surfaceNamedLocalAssignSwitchStorageStmt_toSurfaceProgram]

theorem surfaceNamedLocalAssignSwitchStorageStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedLocalAssignSwitchStorageArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedLocalAssignSwitchStorageArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedLocalAssignSwitchStorageStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedLocalAssignSwitchStorageStmt

def surfaceNamedNestedLocalShadowStmt : SurfaceNamedStmt :=
  SurfaceNamedStmt.localDecl
    "x" (Expr.lit 1)
    (SurfaceNamedStmt.localDecl
      "x" (Expr.lit 2)
      (SurfaceNamedStmt.returnWord (SurfaceNamedWordExpr.ident "x")))

theorem surfaceNamedNestedLocalShadowStmt_resolve :
    SurfaceNamedStmt.resolve?
        surfaceContractStorageNameEnv
        surfaceNamedNestedLocalShadowStmt =
      some
        (SurfaceResolvedStmt.localDecl
          (SurfaceLocalInfo.uint256 SurfaceLocalHandle.first)
          (Expr.lit 1)
          (SurfaceResolvedStmt.localDecl
            (SurfaceLocalInfo.uint256 { index := 1 })
            (Expr.lit 2)
            (SurfaceResolvedStmt.returnWord
              (SurfaceResolvedWordExpr.local
                (SurfaceLocalInfo.uint256 { index := 1 }))))) := by
  dsimp [surfaceNamedNestedLocalShadowStmt,
    surfaceContractStorageNameEnv,
    SurfaceNamedStmt.resolve?,
    SurfaceNamedWordExpr.resolve?,
    SurfaceNameEnv.resolveIdentRValue?,
    SurfaceNameEnv.lookupWord?,
    SurfaceNameEnv.lookupLocalWord?,
    SurfaceNameEnv.lookupLocalWordInScopes?,
    SurfaceNameEnv.lookupStorageInfo?,
    SurfaceNameEnv.nextLocalHandle,
    SurfaceNameEnv.pushScope,
    SurfaceNameScope.singleLocal,
    SurfaceWordRef.toRValue]
  simp [SurfaceNameEnv.singleStorage, SurfaceLocalHandle.first]

def surfaceNamedNestedLocalShadowProgram : SurfaceProgram :=
  { body := SurfaceStmt.returnStateExpr (StateExpr.pure (Expr.lit 2)) }

def surfaceNamedNestedLocalShadowArtifact : SurfaceProgramArtifact :=
  compileSurfaceProgramArtifact surfaceNamedNestedLocalShadowProgram

theorem surfaceNamedNestedLocalShadowStmt_toSurfaceProgram :
    SurfaceNamedStmt.toSurfaceProgram?
        surfaceContractStorageNameEnv
        surfaceNamedNestedLocalShadowStmt =
      some surfaceNamedNestedLocalShadowProgram := by
  dsimp [SurfaceNamedStmt.toSurfaceProgram?,
    surfaceNamedNestedLocalShadowStmt,
    surfaceNamedNestedLocalShadowProgram]
  rw [
    SurfaceNamedStmt.toSurfaceStmt?_nested_localDecl_shadow_return_inner_self]

theorem compileSurfaceNamedStmtArtifact?_surfaceNamedNestedLocalShadowStmt :
    compileSurfaceNamedStmtArtifact?
        surfaceContractStorageNameEnv
        surfaceNamedNestedLocalShadowStmt =
      some surfaceNamedNestedLocalShadowArtifact := by
  dsimp [compileSurfaceNamedStmtArtifact?,
    surfaceNamedNestedLocalShadowArtifact]
  rw [surfaceNamedNestedLocalShadowStmt_toSurfaceProgram]

theorem surfaceNamedNestedLocalShadowStmt_accepted_currentSolidCore :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      surfaceNamedNestedLocalShadowArtifact.sourceArtifact.stmtArtifact.fuel
      initialStaticContext false true
      surfaceNamedNestedLocalShadowArtifact.sourceArtifact.stmtArtifact.stmt
      initialStaticContext := by
  exact
    compileSurfaceNamedStmtArtifact?_accepted_currentSolidCore
      surfaceNamedNestedLocalShadowStmt_toSurfaceProgram
      compileSurfaceNamedStmtArtifact?_surfaceNamedNestedLocalShadowStmt

def parseSurfaceNamedWordAtom? (literal : String) :
    Option SurfaceNamedWordExpr :=
  match parseSurfaceExpr? literal with
  | some expr => some (SurfaceNamedWordExpr.pure expr)
  | none =>
      let name := literal.trimAscii.toString
      if name.isEmpty then
        none
      else
        some (SurfaceNamedWordExpr.ident name)

def parseSurfaceNamedWordBinaryWithAtom?
    (parseAtom? : String -> Option SurfaceNamedWordExpr)
    (literal op : String)
    (mk : SurfaceNamedWordExpr -> SurfaceNamedWordExpr ->
      SurfaceNamedWordExpr) :
    Option SurfaceNamedWordExpr :=
  match literal.splitOn op with
  | [lhsLiteral, rhsLiteral] =>
      match parseAtom? lhsLiteral, parseAtom? rhsLiteral with
      | some lhs, some rhs => some (mk lhs rhs)
      | _, _ => none
  | _ => none

def parseSurfaceNamedWordDerivedBinaryWithAtom?
    (parseAtom? : String -> Option SurfaceNamedWordExpr)
    (literal op : String)
    (mk : SurfaceNamedWordExpr -> SurfaceNamedWordExpr ->
      SurfaceNamedWordExpr) :
    Option SurfaceNamedWordExpr :=
  match parseSurfaceNamedWordBinaryWithAtom?
      parseAtom? literal op mk with
  | some expr => some (SurfaceNamedWordExpr.iszero expr)
  | none => none

def parseSurfaceNamedWordUnaryWithAtom?
    (parseAtom? : String -> Option SurfaceNamedWordExpr)
    (literal name : String)
    (mk : SurfaceNamedWordExpr -> SurfaceNamedWordExpr) :
    Option SurfaceNamedWordExpr :=
  match stripSurfaceStateUnary? name literal with
  | some inner =>
      match parseAtom? inner with
      | some expr => some (mk expr)
      | none => none
  | none => none

def parseSurfaceNamedWordExpr? (literal : String) :
    Option SurfaceNamedWordExpr :=
  match parseSurfaceNamedWordDerivedBinaryWithAtom?
      parseSurfaceNamedWordAtom? literal "!="
      (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.eq) with
  | some expr => some expr
  | none =>
      match parseSurfaceNamedWordBinaryWithAtom?
          parseSurfaceNamedWordAtom? literal "=="
          (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.eq) with
      | some expr => some expr
      | none =>
          match parseSurfaceNamedWordDerivedBinaryWithAtom?
              parseSurfaceNamedWordAtom? literal "<="
              (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.gt) with
          | some expr => some expr
          | none =>
              match parseSurfaceNamedWordDerivedBinaryWithAtom?
                  parseSurfaceNamedWordAtom? literal ">="
                  (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.lt) with
              | some expr => some expr
              | none =>
                  match parseSurfaceNamedWordBinaryWithAtom?
                      parseSurfaceNamedWordAtom? literal "<"
                      (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.lt) with
                  | some expr => some expr
                  | none =>
                      match parseSurfaceNamedWordBinaryWithAtom?
                          parseSurfaceNamedWordAtom? literal ">"
                          (SurfaceNamedWordExpr.binary SurfaceWordBinaryOp.gt) with
                      | some expr => some expr
                      | none =>
                          match parseSurfaceNamedWordBinaryWithAtom?
                              parseSurfaceNamedWordAtom? literal "&"
                              (SurfaceNamedWordExpr.binary
                                SurfaceWordBinaryOp.bitAnd) with
                          | some expr => some expr
                          | none =>
                              match parseSurfaceNamedWordBinaryWithAtom?
                                  parseSurfaceNamedWordAtom? literal "|"
                                  (SurfaceNamedWordExpr.binary
                                    SurfaceWordBinaryOp.bitOr) with
                              | some expr => some expr
                              | none =>
                                  match parseSurfaceNamedWordBinaryWithAtom?
                                      parseSurfaceNamedWordAtom? literal "^"
                                      (SurfaceNamedWordExpr.binary
                                        SurfaceWordBinaryOp.bitXor) with
                                  | some expr => some expr
                                  | none =>
                                      match parseSurfaceNamedWordBinaryWithAtom?
                                          parseSurfaceNamedWordAtom? literal "+"
                                          (SurfaceNamedWordExpr.binary
                                            SurfaceWordBinaryOp.add) with
                                      | some expr => some expr
                                      | none =>
                                          match parseSurfaceNamedWordBinaryWithAtom?
                                              parseSurfaceNamedWordAtom? literal "-"
                                              (SurfaceNamedWordExpr.binary
                                                SurfaceWordBinaryOp.sub) with
                                          | some expr => some expr
                                          | none =>
                                              match parseSurfaceNamedWordBinaryWithAtom?
                                                  parseSurfaceNamedWordAtom?
                                                  literal "*"
                                                  (SurfaceNamedWordExpr.binary
                                                    SurfaceWordBinaryOp.mul) with
                                              | some expr => some expr
                                              | none =>
                                                  match parseSurfaceNamedWordUnaryWithAtom?
                                                      parseSurfaceNamedWordAtom?
                                                      literal "not"
                                                      (SurfaceNamedWordExpr.unary
                                                        SurfaceWordUnaryOp.bitNot) with
                                                  | some expr => some expr
                                                  | none =>
                                                      match parseSurfaceNamedWordUnaryWithAtom?
                                                          parseSurfaceNamedWordAtom?
                                                          literal "iszero"
                                                          SurfaceNamedWordExpr.iszero with
                                                      | some expr => some expr
                                                      | none =>
                                                          parseSurfaceNamedWordAtom?
                                                            literal

def parseSurfaceStateAtom? (literal : String) : Option StateExpr :=
  match stripSurfaceSloadExpr? literal with
  | some slotLiteral =>
      match parseSurfaceExpr? slotLiteral with
      | some slot => some (StateExpr.load slot)
      | none => none
  | none =>
      match parseSurfaceExpr? literal with
      | some expr => some (StateExpr.pure expr)
      | none => none

def parseSurfaceStateAtomWithEnv?
    (env : SurfaceNameEnv) (literal : String) : Option StateExpr :=
  let name := literal.trimAscii.toString
  match SurfaceNameEnv.resolveIdentRValue? env name with
  | some resolved => resolved.toStateExpr?
  | none => parseSurfaceStateAtom? literal

theorem parseSurfaceStateAtomWithEnv?_local_shadows_storage :
    parseSurfaceStateAtomWithEnv?
        surfaceLocalShadowsStorageNameEnv "x" = none := by
  native_decide

def parseSurfaceStorageVarStateAtom? (literal : String) : Option StateExpr :=
  parseSurfaceStateAtomWithEnv? surfaceContractStorageNameEnv literal

def parseSurfaceStateBinaryWithAtom?
    (parseAtom? : String -> Option StateExpr)
    (literal op : String)
    (mk : StateExpr -> StateExpr -> StateExpr) :
    Option StateExpr :=
  match literal.splitOn op with
  | [lhsLiteral, rhsLiteral] =>
      match parseAtom? lhsLiteral, parseAtom? rhsLiteral with
      | some lhs, some rhs =>
          let expr := mk lhs rhs
          if expr.hasLoad? then some expr else none
      | _, _ => none
  | _ => none

def parseSurfaceStateBinary?
    (literal op : String)
    (mk : StateExpr -> StateExpr -> StateExpr) :
    Option StateExpr :=
  parseSurfaceStateBinaryWithAtom? parseSurfaceStateAtom?
    literal op mk

def parseSurfaceStateDerivedBinaryWithAtom?
    (parseAtom? : String -> Option StateExpr)
    (literal op : String)
    (mk : StateExpr -> StateExpr -> StateExpr) :
    Option StateExpr :=
  match parseSurfaceStateBinaryWithAtom? parseAtom? literal op mk with
  | some expr => some (StateExpr.iszero expr)
  | none => none

def parseSurfaceStateDerivedBinary?
    (literal op : String)
    (mk : StateExpr -> StateExpr -> StateExpr) :
    Option StateExpr :=
  parseSurfaceStateDerivedBinaryWithAtom? parseSurfaceStateAtom?
    literal op mk

def parseSurfaceStateUnaryWithAtom?
    (parseAtom? : String -> Option StateExpr)
    (literal name : String) (mk : StateExpr -> StateExpr) :
    Option StateExpr :=
  match stripSurfaceStateUnary? name literal with
  | some inner =>
      match parseAtom? inner with
      | some expr => some (mk expr)
      | none => none
  | none => none

def parseSurfaceStateUnary?
    (literal name : String) (mk : StateExpr -> StateExpr) :
    Option StateExpr :=
  parseSurfaceStateUnaryWithAtom? parseSurfaceStateAtom? literal name mk

def parseSurfaceStateExprWithAtom?
    (parseAtom? : String -> Option StateExpr)
    (literal : String) : Option StateExpr :=
  match parseSurfaceStateDerivedBinaryWithAtom?
      parseAtom? literal "!=" StateExpr.eq with
  | some expr => some expr
  | none =>
      match parseSurfaceStateBinaryWithAtom?
          parseAtom? literal "==" StateExpr.eq with
      | some expr => some expr
      | none =>
          match parseSurfaceStateDerivedBinaryWithAtom?
              parseAtom? literal "<=" StateExpr.gt with
          | some expr => some expr
          | none =>
              match parseSurfaceStateDerivedBinaryWithAtom?
                  parseAtom? literal ">=" StateExpr.lt with
              | some expr => some expr
              | none =>
                  match parseSurfaceStateBinaryWithAtom?
                      parseAtom? literal "<" StateExpr.lt with
                  | some expr => some expr
                  | none =>
                      match parseSurfaceStateBinaryWithAtom?
                          parseAtom? literal ">" StateExpr.gt with
                      | some expr => some expr
                      | none =>
                          match parseSurfaceStateBinaryWithAtom?
                              parseAtom? literal "&" StateExpr.bitAnd with
                          | some expr => some expr
                          | none =>
                              match parseSurfaceStateBinaryWithAtom?
                                  parseAtom? literal "|" StateExpr.bitOr with
                              | some expr => some expr
                              | none =>
                                  match parseSurfaceStateBinaryWithAtom?
                                      parseAtom? literal "^" StateExpr.bitXor with
                                  | some expr => some expr
                                  | none =>
                                      match parseSurfaceStateBinaryWithAtom?
                                          parseAtom? literal "+" StateExpr.add with
                                      | some expr => some expr
                                      | none =>
                                          match parseSurfaceStateBinaryWithAtom?
                                              parseAtom? literal "-" StateExpr.sub with
                                          | some expr => some expr
                                          | none =>
                                              match parseSurfaceStateBinaryWithAtom?
                                                  parseAtom? literal "*" StateExpr.mul with
                                              | some expr => some expr
                                              | none =>
                                                  match parseSurfaceStateUnaryWithAtom?
                                                      parseAtom? literal "not" StateExpr.bitNot with
                                                  | some expr => some expr
                                                  | none =>
                                                      match parseSurfaceStateUnaryWithAtom?
                                                          parseAtom? literal "iszero" StateExpr.iszero with
                                                      | some expr => some expr
                                                      | none =>
                                                          match parseAtom? literal with
                                                          | some expr =>
                                                              if expr.hasLoad? then
                                                                some expr
                                                              else
                                                                none
                                                          | none => none

def parseSurfaceStateExpr? (literal : String) : Option StateExpr :=
  parseSurfaceStateExprWithAtom? parseSurfaceStateAtom? literal

def parseSurfaceStorageVarStateExpr? (literal : String) :
    Option StateExpr :=
  parseSurfaceStateExprWithAtom? parseSurfaceStorageVarStateAtom? literal

def parseSurfaceTwoExprArgs? (args : String) : Option (Expr × Expr) :=
  match args.splitOn "," with
  | [lhs, rhs] =>
      match parseSurfaceExpr? lhs, parseSurfaceExpr? rhs with
      | some lhsExpr, some rhsExpr => some (lhsExpr, rhsExpr)
      | _, _ => none
  | _ => none

def stripSurfaceStore? (body : String) : Option String :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceSstorePrefix &&
      trimmed.endsWith surfaceSstoreSuffix then
    some
      ((((trimmed.drop surfaceSstorePrefix.length).dropEnd
        surfaceSstoreSuffix.length).trimAscii).toString)
  else
    none

def parseSurfaceStoreStmt? (body : String) : Option SurfaceStmt :=
  match stripSurfaceStore? body with
  | some storeArgs =>
      match parseSurfaceTwoExprArgs? storeArgs with
      | some (slot, value) =>
          some (SurfaceStmt.storageStore slot value)
      | none => none
  | none => none

def stripSurfaceStorageStore? (body : String) :
    Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.endsWith surfaceReturnSuffix then
    let bodyWithoutSuffix :=
      (trimmed.dropEnd surfaceReturnSuffix.length).toString
    match bodyWithoutSuffix.splitOn " = " with
    | [nameLiteral, valueLiteral] =>
        some (nameLiteral.trimAscii.toString,
          valueLiteral.trimAscii.toString)
    | _ => none
  else
    none

def parseSurfaceStorageStoreStmtWithEnv?
    (env : SurfaceNameEnv) (body : String) :
    Option SurfaceStmt :=
  match stripSurfaceStorageStore? body with
  | some (nameLiteral, valueLiteral) =>
      match SurfaceNameEnv.resolveIdentLValue? env nameLiteral,
          parseSurfaceExpr? valueLiteral with
      | some (SurfaceResolvedLValue.storage info), some value =>
          some (SurfaceStmt.storageStore info.slot value)
      | _, _ => none
  | none => none

theorem parseSurfaceStorageStoreStmtWithEnv?_local_shadows_storage :
    parseSurfaceStorageStoreStmtWithEnv?
        surfaceLocalShadowsStorageNameEnv "x = 8;" = none := by
  native_decide

def parseSurfaceStorageVarStoreStmt? (body : String) :
    Option SurfaceStmt :=
  parseSurfaceStorageStoreStmtWithEnv?
    surfaceContractStorageNameEnv body

def parseSurfaceNamedAssignStmt? (body : String) :
    Option SurfaceNamedStmt :=
  match stripSurfaceStorageStore? body with
  | some (nameLiteral, valueLiteral) =>
      match parseSurfaceExpr? valueLiteral with
      | some value =>
          some
            (SurfaceNamedStmt.assign
              (SurfaceNamedLValue.ident nameLiteral) value)
      | none => none
  | none => none

def parseSurfaceNamedReturnStmt? (body : String) :
    Option SurfaceNamedStmt :=
  match stripSurfaceReturn? body with
  | some returnLiteral =>
      match parseSurfaceNamedWordExpr? returnLiteral with
      | some returnExpr =>
          some (SurfaceNamedStmt.returnWord returnExpr)
      | none => none
  | none => none

def parseSurfacePlainReturnStmtWithStateExpr?
    (parseStateExpr? : String -> Option StateExpr)
    (body : String) : Option SurfaceStmt :=
  match stripSurfaceReturn? body with
  | some literal =>
      match parseStateExpr? literal with
      | some expr => some (SurfaceStmt.returnStateExpr expr)
      | none =>
          match parseSurfaceExpr? literal with
          | some expr => some (SurfaceStmt.returnExpr expr)
          | none => none
  | none => none

def parseSurfacePlainReturnStmt? (body : String) : Option SurfaceStmt :=
  parseSurfacePlainReturnStmtWithStateExpr?
    parseSurfaceStateExpr? body

def parseSurfaceReturnStmtWithStateExpr?
    (parseStateExpr? : String -> Option StateExpr)
    (body : String) : Option SurfaceStmt :=
  match stripSurfaceReturnSload? body with
  | some slotLiteral =>
      match parseSurfaceExpr? slotLiteral with
      | some slot => some (SurfaceStmt.storageLoadReturn slot)
      | none =>
          parseSurfacePlainReturnStmtWithStateExpr?
            parseStateExpr? body
  | none =>
      parseSurfacePlainReturnStmtWithStateExpr?
        parseStateExpr? body

def parseSurfaceReturnStmt? (body : String) : Option SurfaceStmt :=
  parseSurfaceReturnStmtWithStateExpr? parseSurfaceStateExpr? body

def parseSurfaceStorageVarReturnStmt? (body : String) :
    Option SurfaceStmt :=
  parseSurfaceReturnStmtWithStateExpr?
    parseSurfaceStorageVarStateExpr? body

def parseSurfaceReturnBody? (body : String) : Option SurfaceProgram :=
  match parseSurfaceReturnStmt? body with
  | some stmt => some { body := stmt }
  | none => none

def stripSurfaceStoreLoadReturn? (body : String) :
    Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceSstorePrefix &&
      trimmed.endsWith surfaceSstoreReturnSloadSuffix then
    let bodyWithoutWrapper :=
      ((trimmed.drop surfaceSstorePrefix.length).dropEnd
        surfaceSstoreReturnSloadSuffix.length).toString
    match bodyWithoutWrapper.splitOn surfaceSstoreReturnSloadMiddle with
    | [storeArgs, loadSlotLiteral] =>
        some (storeArgs.trimAscii.toString,
          loadSlotLiteral.trimAscii.toString)
    | _ => none
  else
    none

def parseSurfaceStoreLoadReturnBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceStoreLoadReturn? body with
  | some (storeArgs, loadSlotLiteral) =>
      match parseSurfaceTwoExprArgs? storeArgs,
          parseSurfaceExpr? loadSlotLiteral with
      | some (slot, value), some loadSlot =>
          some
            { body :=
                SurfaceStmt.seq
                  (SurfaceStmt.storageStore slot value)
                  (SurfaceStmt.storageLoadReturn loadSlot) }
      | _, _ => none
  | none => none

def parseSurfaceTwoStoreReturnBody? (body : String) :
    Option SurfaceProgram :=
  match body.trimAscii.toString.splitOn "; " with
  | [firstStore, secondStore, returnStmt] =>
      match parseSurfaceStoreStmt? (firstStore ++ ";"),
          parseSurfaceStoreStmt? (secondStore ++ ";"),
          parseSurfaceReturnStmt? returnStmt with
      | some firstStmt, some secondStmt, some afterStmt =>
          some
            { body :=
                SurfaceStmt.seq firstStmt
                  (SurfaceStmt.seq secondStmt afterStmt) }
      | _, _, _ => none
  | _ => none

def stripSurfaceBoundedWhile? (body : String) :
    Option (String × String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceBoundedWhilePrefix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceBoundedWhilePrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceBoundedWhileBodyOpen with
    | header :: restHead :: restTail =>
        let rest :=
          String.intercalate surfaceBoundedWhileBodyOpen
            (restHead :: restTail)
        match rest.splitOn surfaceBoundedWhileBodyClose with
        | [loopBody, afterBody] =>
            some (header.trimAscii.toString,
              loopBody.trimAscii.toString,
              afterBody.trimAscii.toString)
        | _ => none
    | _ => none
  else
    none

def parseSurfaceBoundedWhileHeader? (header : String) :
    Option (Nat × Expr) :=
  match header.splitOn " " with
  | [boundLiteral, condLiteral] =>
      match boundLiteral.trimAscii.toNat?,
          parseSurfaceExpr? condLiteral with
      | some bound, some cond => some (bound, cond)
      | _, _ => none
  | _ => none

def parseSurfaceNamedBoundedWhileHeader? (header : String) :
    Option (Nat × SurfaceNamedWordExpr) :=
  match header.splitOn " " with
  | [boundLiteral, condLiteral] =>
      match boundLiteral.trimAscii.toNat?,
          parseSurfaceNamedWordExpr? condLiteral with
      | some bound, some cond => some (bound, cond)
      | _, _ => none
  | _ => none

def parseSurfaceBoundedWhileReturnBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceBoundedWhile? body with
  | some (header, loopBody, afterBody) =>
      match parseSurfaceBoundedWhileHeader? header,
          parseSurfaceStoreStmt? loopBody,
          parseSurfaceReturnStmt? afterBody with
      | some (bound, cond), some bodyStmt, some afterStmt =>
          some
            { body :=
                SurfaceStmt.seq
                  (SurfaceStmt.boundedWhile bound cond bodyStmt)
                  afterStmt }
      | _, _, _ => none
  | none => none

def parseSurfaceStorageVarBoundedWhileReturnBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceBoundedWhile? body with
  | some (header, loopBody, afterBody) =>
      match parseSurfaceNamedBoundedWhileHeader? header,
          parseSurfaceNamedAssignStmt? loopBody,
          parseSurfaceNamedReturnStmt? afterBody with
      | some (bound, cond), some bodyStmt, some afterStmt =>
          SurfaceNamedStmt.toSurfaceProgram?
            surfaceContractStorageNameEnv
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.boundedWhile bound cond bodyStmt)
              afterStmt)
      | _, _, _ => none
  | none => none

def stripSurfaceSwitch? (body : String) : Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceSwitchPrefix &&
      trimmed.endsWith surfaceSwitchSuffix then
    let bodyWithoutWrapper :=
      ((trimmed.drop surfaceSwitchPrefix.length).dropEnd
        surfaceSwitchSuffix.length).toString
    match bodyWithoutWrapper.splitOn surfaceSwitchOpen with
    | [discrLiteral, casesText] =>
        some (discrLiteral.trimAscii.toString,
          casesText.trimAscii.toString)
    | _ => none
  else
    none

def parseSurfaceSwitchCaseWithReturn?
    (parseReturnStmt? : String -> Option SurfaceStmt)
    (caseText : String) :
    Option (Word × SurfaceStmt) :=
  match caseText.trimAscii.toString.splitOn surfaceSwitchCaseMiddle with
  | [labelLiteral, branchBody] =>
      match labelLiteral.trimAscii.toNat?,
          parseReturnStmt? branchBody with
      | some label, some branch => some (label, branch)
      | _, _ => none
  | _ => none

def parseSurfaceSwitchCase? (caseText : String) :
    Option (Word × SurfaceStmt) :=
  parseSurfaceSwitchCaseWithReturn? parseSurfaceReturnStmt? caseText

def parseSurfaceSwitchCaseTokensWithReturn?
    (parseReturnStmt? : String -> Option SurfaceStmt) :
    List String -> Option (List (Word × SurfaceStmt))
  | [] => some []
  | token :: rest =>
      let trimmed := token.trimAscii.toString
      if trimmed.isEmpty then
        parseSurfaceSwitchCaseTokensWithReturn?
          parseReturnStmt? rest
      else
        match parseSurfaceSwitchCaseWithReturn?
              parseReturnStmt? trimmed,
            parseSurfaceSwitchCaseTokensWithReturn?
              parseReturnStmt? rest with
        | some switchCase, some switchCases =>
            some (switchCase :: switchCases)
        | _, _ => none

def parseSurfaceSwitchCaseTokens? :
    List String -> Option (List (Word × SurfaceStmt)) :=
  parseSurfaceSwitchCaseTokensWithReturn? parseSurfaceReturnStmt?

def parseSurfaceSwitchCasesAndDefaultWithReturn?
    (parseReturnStmt? : String -> Option SurfaceStmt)
    (casesText : String) :
    Option (List (Word × SurfaceStmt) × SurfaceStmt) :=
  match casesText.splitOn surfaceSwitchDefaultMiddle with
  | [caseText, defaultBody] =>
      match parseSurfaceSwitchCaseTokensWithReturn?
          parseReturnStmt?
          (caseText.splitOn surfaceSwitchCasePrefix),
          parseReturnStmt? defaultBody with
      | some switchCases, some defaultBranch =>
          some (switchCases, defaultBranch)
      | _, _ => none
  | _ => none

def parseSurfaceSwitchCasesAndDefault?
    (casesText : String) :
    Option (List (Word × SurfaceStmt) × SurfaceStmt) :=
  parseSurfaceSwitchCasesAndDefaultWithReturn?
    parseSurfaceReturnStmt? casesText

def parseSurfaceNamedSwitchCaseWithReturn?
    (parseReturnStmt? : String -> Option SurfaceNamedStmt)
    (caseText : String) :
    Option (Word × SurfaceNamedStmt) :=
  match caseText.trimAscii.toString.splitOn surfaceSwitchCaseMiddle with
  | [labelLiteral, branchBody] =>
      match labelLiteral.trimAscii.toNat?,
          parseReturnStmt? branchBody with
      | some label, some branch => some (label, branch)
      | _, _ => none
  | _ => none

def parseSurfaceNamedSwitchCaseTokensWithReturn?
    (parseReturnStmt? : String -> Option SurfaceNamedStmt) :
    List String -> Option (List (Word × SurfaceNamedStmt))
  | [] => some []
  | token :: rest =>
      let trimmed := token.trimAscii.toString
      if trimmed.isEmpty then
        parseSurfaceNamedSwitchCaseTokensWithReturn?
          parseReturnStmt? rest
      else
        match parseSurfaceNamedSwitchCaseWithReturn?
              parseReturnStmt? trimmed,
            parseSurfaceNamedSwitchCaseTokensWithReturn?
              parseReturnStmt? rest with
        | some switchCase, some switchCases =>
            some (switchCase :: switchCases)
        | _, _ => none

def parseSurfaceNamedSwitchCasesAndDefaultWithReturn?
    (parseReturnStmt? : String -> Option SurfaceNamedStmt)
    (casesText : String) :
    Option (List (Word × SurfaceNamedStmt) × SurfaceNamedStmt) :=
  match casesText.splitOn surfaceSwitchDefaultMiddle with
  | [caseText, defaultBody] =>
      match parseSurfaceNamedSwitchCaseTokensWithReturn?
          parseReturnStmt?
          (caseText.splitOn surfaceSwitchCasePrefix),
          parseReturnStmt? defaultBody with
      | some switchCases, some defaultBranch =>
          some (switchCases, defaultBranch)
      | _, _ => none
  | _ => none

def stripSurfaceStorageVarAssignSwitch? (body : String) :
    Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceStorageVarAssignPrefix &&
      trimmed.endsWith surfaceSwitchSuffix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceStorageVarAssignPrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceStorageVarAssignSwitchMiddle with
    | [valueLiteral, switchTail] =>
        some (valueLiteral.trimAscii.toString,
          (surfaceSwitchPrefix ++ switchTail).trimAscii.toString)
    | _ => none
  else
    none

def parseSurfaceStorageVarAssignSwitchBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceStorageVarAssignSwitch? body with
  | some (valueLiteral, switchBody) =>
      match parseSurfaceExpr? valueLiteral, stripSurfaceSwitch? switchBody with
      | some value, some (discrLiteral, casesText) =>
          match parseSurfaceNamedWordExpr? discrLiteral,
              parseSurfaceNamedSwitchCasesAndDefaultWithReturn?
                parseSurfaceNamedReturnStmt? casesText with
          | some discr, some (switchCases, defaultBranch) =>
              SurfaceNamedStmt.toSurfaceProgramWithStorageGuard?
                surfaceContractStorageNameEnv
                (SurfaceNamedStmt.seq
                  (SurfaceNamedStmt.assign
                    (SurfaceNamedLValue.ident "x") value)
                  (SurfaceNamedStmt.switchCases
                    discr switchCases defaultBranch))
          | _, _ => none
      | _, _ => none
  | none => none

def parseSurfaceNamedSwitchBody?
    (env : SurfaceNameEnv) (body : String) : Option SurfaceProgram :=
  match stripSurfaceSwitch? body with
  | some (discrLiteral, casesText) =>
      match parseSurfaceNamedWordExpr? discrLiteral,
          parseSurfaceNamedSwitchCasesAndDefaultWithReturn?
            parseSurfaceNamedReturnStmt? casesText with
      | some discr, some (switchCases, defaultBranch) =>
          SurfaceNamedStmt.toSurfaceProgram? env
            (SurfaceNamedStmt.switchCases
              discr switchCases defaultBranch)
      | _, _ => none
  | none => none

def parseSurfaceSwitchBody? (body : String) : Option SurfaceProgram :=
  match parseSurfaceNamedSwitchBody? SurfaceNameEnv.empty body with
  | some program => some program
  | none =>
      match stripSurfaceSwitch? body with
      | some (discrLiteral, casesText) =>
          match parseSurfaceExpr? discrLiteral,
              parseSurfaceSwitchCasesAndDefault? casesText with
          | some discr, some (switchCases, defaultBranch) =>
              some
                { body :=
                    SurfaceStmt.switchCases discr switchCases defaultBranch }
          | _, _ => none
      | none => none

def parseSurfaceStoreThenSwitchLoadBody? (body : String) :
    Option SurfaceProgram :=
  let storePostSep := surfaceSstoreSuffix ++ " "
  match body.trimAscii.toString.splitOn storePostSep with
  | storeBody :: switchHead :: switchTail =>
      let switchBody :=
        String.intercalate storePostSep (switchHead :: switchTail)
      match parseSurfaceStoreStmt? (storeBody ++ surfaceSstoreSuffix),
          stripSurfaceSwitch? switchBody with
      | some (SurfaceStmt.storageStore slot value),
          some (discrLiteral, casesText) =>
          match stripSurfaceSloadExpr? discrLiteral,
              parseSurfaceSwitchCasesAndDefault? casesText with
          | some loadSlotLiteral, some (switchCases, defaultBranch) =>
              match parseSurfaceExpr? loadSlotLiteral with
              | some loadSlot =>
                  if slot = loadSlot then
                    some
                      { body :=
                          SurfaceStmt.seq
                            (SurfaceStmt.storageStore slot value)
                            (SurfaceStmt.switchCases value
                              switchCases defaultBranch) }
                  else
                    none
              | none => none
          | _, _ => none
      | _, _ => none
  | _ => none

def parseSurfacePostLoopStmt? (body : String) : Option SurfaceStmt :=
  match parseSurfaceReturnStmt? body with
  | some stmt => some stmt
  | none =>
      match parseSurfaceSwitchBody? body with
      | some program => some program.body
      | none => none

def stripSurfaceIfOnly? (body : String) : Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceIfPrefix &&
      trimmed.endsWith surfaceIfElseSuffix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceIfPrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceIfBodyOpen with
    | condLiteral :: bodyHead :: bodyTail =>
        let rest :=
          String.intercalate surfaceIfBodyOpen (bodyHead :: bodyTail)
        let ifBody :=
          ((rest.dropEnd surfaceIfElseSuffix.length).trimAscii).toString
        some (condLiteral.trimAscii.toString, ifBody)
    | _ => none
  else
    none

def parseSurfaceStorageVarPostLoopStmt? (body : String) :
    Option SurfaceStmt :=
  parseSurfaceStorageVarReturnStmt? body

def parseSurfaceStorageVarPostNamedStmt? (body : String) :
    Option SurfaceNamedStmt :=
  parseSurfaceNamedReturnStmt? body

def parseSurfaceStorageVarAssignPostBody? (body : String) :
    Option SurfaceProgram :=
  let assignPostSep := surfaceReturnSuffix ++ " "
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceStorageVarAssignPrefix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceStorageVarAssignPrefix.length).toString
    match bodyWithoutPrefix.splitOn assignPostSep with
    | valueLiteral :: afterHead :: afterTail =>
        let afterBody :=
          String.intercalate assignPostSep (afterHead :: afterTail)
        match parseSurfaceExpr? valueLiteral,
            parseSurfaceStorageVarPostNamedStmt? afterBody with
        | some value, some afterStmt =>
            SurfaceNamedStmt.toSurfaceProgram?
              surfaceContractStorageNameEnv
              (SurfaceNamedStmt.seq
                (SurfaceNamedStmt.assign
                  (SurfaceNamedLValue.ident "x") value)
                afterStmt)
        | _, _ => none
    | _ => none
  else
    none

def stripSurfaceStorageVarAssignIf? (body : String) :
    Option (String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceStorageVarAssignPrefix &&
      trimmed.endsWith surfaceIfElseSuffix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceStorageVarAssignPrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceStorageVarAssignIfMiddle with
    | [valueLiteral, ifTail] =>
        some (valueLiteral.trimAscii.toString,
          (surfaceIfPrefix ++ ifTail).trimAscii.toString)
    | _ => none
  else
    none

def parseSurfaceStorageVarAssignIfBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceStorageVarAssignIf? body with
  | some (valueLiteral, ifText) =>
      match parseSurfaceExpr? valueLiteral, stripSurfaceIfOnly? ifText with
      | some value, some (condLiteral, ifBody) =>
          match parseSurfaceNamedWordExpr? condLiteral,
              parseSurfaceNamedReturnStmt? ifBody with
          | some cond, some bodyStmt =>
              SurfaceNamedStmt.toSurfaceProgramWithStorageGuard?
                surfaceContractStorageNameEnv
                (SurfaceNamedStmt.seq
                  (SurfaceNamedStmt.assign
                    (SurfaceNamedLValue.ident "x") value)
                  (SurfaceNamedStmt.ifThen cond bodyStmt))
          | _, _ => none
      | _, _ => none
  | none => none

def parseSurfaceStoreThenIfLoadBody? (body : String) :
    Option SurfaceProgram :=
  let storeIfSep := surfaceSstoreSuffix ++ " "
  match body.trimAscii.toString.splitOn storeIfSep with
  | storeBody :: ifHead :: ifTail =>
      let ifText :=
        String.intercalate storeIfSep (ifHead :: ifTail)
      match parseSurfaceStoreStmt? (storeBody ++ surfaceSstoreSuffix),
          stripSurfaceIfOnly? ifText with
      | some (SurfaceStmt.storageStore slot value),
          some (condLiteral, ifBody) =>
          match stripSurfaceSloadExpr? condLiteral,
              parseSurfacePostLoopStmt? ifBody with
          | some guardSlotLiteral, some bodyStmt =>
              match parseSurfaceExpr? guardSlotLiteral with
              | some guardSlot =>
                  if slot = guardSlot then
                    some
                      { body :=
                          SurfaceStmt.storageStoreThenIfLoad
                            slot value bodyStmt }
                  else
                    none
              | none => none
          | _, _ => none
      | _, _ => none
  | _ => none

def parseSurfaceStoreThenPostBody? (body : String) :
    Option SurfaceProgram :=
  let storePostSep := surfaceSstoreSuffix ++ " "
  match body.trimAscii.toString.splitOn storePostSep with
  | storeBody :: afterHead :: afterTail =>
      let afterBody := String.intercalate storePostSep (afterHead :: afterTail)
      match parseSurfaceStoreStmt? (storeBody ++ surfaceSstoreSuffix),
          parseSurfacePostLoopStmt? afterBody with
      | some storeStmt, some afterStmt =>
          some { body := SurfaceStmt.seq storeStmt afterStmt }
      | _, _ => none
  | _ => none

def parseSurfaceBoundedWhilePostBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceBoundedWhile? body with
  | some (header, loopBody, afterBody) =>
      match parseSurfaceBoundedWhileHeader? header,
          parseSurfaceStoreStmt? loopBody,
          parseSurfacePostLoopStmt? afterBody with
      | some (bound, cond), some bodyStmt, some afterStmt =>
          some
            { body :=
                SurfaceStmt.seq
                  (SurfaceStmt.boundedWhile bound cond bodyStmt)
                  afterStmt }
      | _, _, _ => none
  | none => none

def stripSurfaceIfElse? (body : String) :
    Option (String × String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceIfPrefix &&
      trimmed.endsWith surfaceIfElseSuffix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceIfPrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceIfBodyOpen with
    | condLiteral :: bodyHead :: bodyTail =>
        let rest :=
          String.intercalate surfaceIfBodyOpen (bodyHead :: bodyTail)
        let restWithoutSuffix :=
          (rest.dropEnd surfaceIfElseSuffix.length).toString
        match restWithoutSuffix.splitOn surfaceIfElseMiddle with
        | [thenBody, elseBody] =>
            some (condLiteral.trimAscii.toString,
              thenBody.trimAscii.toString,
              elseBody.trimAscii.toString)
        | _ => none
    | _ => none
  else
    none

def parseSurfaceNamedIfElseBodyWith?
    (parseBranch? : String -> Option SurfaceNamedStmt)
    (env : SurfaceNameEnv) (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceIfElse? body with
  | some (condLiteral, thenBody, elseBody) =>
      match parseSurfaceNamedWordExpr? condLiteral,
          parseBranch? thenBody,
          parseBranch? elseBody with
      | some cond, some thenStmt, some elseStmt =>
          SurfaceNamedStmt.toSurfaceProgram? env
            (SurfaceNamedStmt.ifElse cond thenStmt elseStmt)
      | _, _, _ => none
  | none => none

def parseSurfaceNamedIfElseBody?
    (env : SurfaceNameEnv) (body : String) :
    Option SurfaceProgram :=
  parseSurfaceNamedIfElseBodyWith?
    parseSurfaceNamedReturnStmt? env body

def parseSurfaceIfElseBodyWith?
    (parseBranch? : String -> Option SurfaceStmt)
    (body : String) : Option SurfaceProgram :=
  match stripSurfaceIfElse? body with
  | some (condLiteral, thenBody, elseBody) =>
      match parseSurfaceExpr? condLiteral,
          parseBranch? thenBody,
          parseBranch? elseBody with
      | some cond, some thenStmt, some elseStmt =>
          some
            { body :=
                SurfaceStmt.switchCases cond [(0, elseStmt)] thenStmt }
      | _, _, _ => none
  | none => none

def parseSurfaceIfElseBody? (body : String) :
    Option SurfaceProgram :=
  match parseSurfaceNamedIfElseBody? SurfaceNameEnv.empty body with
  | some program => some program
  | none => parseSurfaceIfElseBodyWith? parseSurfaceReturnStmt? body

def stripSurfaceIf? (body : String) :
    Option (String × String × String) :=
  let trimmed := body.trimAscii.toString
  if trimmed.startsWith surfaceIfPrefix then
    let bodyWithoutPrefix :=
      (trimmed.drop surfaceIfPrefix.length).toString
    match bodyWithoutPrefix.splitOn surfaceIfBodyOpen with
    | condLiteral :: bodyHead :: bodyTail =>
        let rest :=
          String.intercalate surfaceIfBodyOpen (bodyHead :: bodyTail)
        match rest.splitOn surfaceIfBodyClose with
        | [ifBody, afterBody] =>
            some (condLiteral.trimAscii.toString,
              ifBody.trimAscii.toString,
              afterBody.trimAscii.toString)
        | _ => none
    | _ => none
  else
    none

def parseSurfaceIfPostBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceIf? body with
  | some (condLiteral, ifBody, afterBody) =>
      match parseSurfaceExpr? condLiteral,
          parseSurfaceStoreStmt? ifBody,
          parseSurfacePostLoopStmt? afterBody with
      | some cond, some bodyStmt, some afterStmt =>
          some
            { body :=
                SurfaceStmt.seq
                  (SurfaceStmt.ifThen cond bodyStmt)
                  afterStmt }
      | _, _, _ => none
  | none => none

def parseSurfaceStorageVarIfPostBody? (body : String) :
    Option SurfaceProgram :=
  match stripSurfaceIf? body with
  | some (condLiteral, ifBody, afterBody) =>
      match parseSurfaceNamedWordExpr? condLiteral,
          parseSurfaceNamedAssignStmt? ifBody,
          parseSurfaceNamedReturnStmt? afterBody with
      | some cond, some bodyStmt, some afterStmt =>
          SurfaceNamedStmt.toSurfaceProgram?
            surfaceContractStorageNameEnv
            (SurfaceNamedStmt.seq
              (SurfaceNamedStmt.ifThen cond bodyStmt)
              afterStmt)
      | _, _, _ => none
  | none => none

def parseGeneratedSurfaceBody? (body : String) : Option SurfaceProgram :=
  match parseSurfaceTwoStoreReturnBody? body with
  | some program => some program
  | none =>
      match parseSurfaceStoreLoadReturnBody? body with
      | some program => some program
      | none =>
          match parseSurfaceStoreThenSwitchLoadBody? body with
          | some program => some program
          | none =>
              match parseSurfaceStoreThenIfLoadBody? body with
              | some program => some program
              | none =>
                  match parseSurfaceStoreThenPostBody? body with
                  | some program => some program
                  | none =>
                      match parseSurfaceIfElseBody? body with
                      | some program => some program
                      | none =>
                          match parseSurfaceIfPostBody? body with
                          | some program => some program
                          | none =>
                              match parseSurfaceSwitchBody? body with
                              | some program => some program
                              | none =>
                                  match parseSurfaceBoundedWhilePostBody? body with
                                  | some program => some program
                                  | none => parseSurfaceReturnBody? body

def parseGeneratedSurfaceStorageBody? (body : String) :
    Option SurfaceProgram :=
  match parseSurfaceStorageVarIfPostBody? body with
  | some program => some program
  | none =>
      match parseSurfaceStorageVarAssignIfBody? body with
      | some program => some program
      | none =>
          match parseSurfaceStorageVarAssignSwitchBody? body with
          | some program => some program
          | none =>
              match parseSurfaceStorageVarBoundedWhileReturnBody? body with
              | some program => some program
              | none =>
                  match parseSurfaceStorageVarAssignPostBody? body with
                  | some program => some program
                  | none => parseGeneratedSurfaceBody? body

def parseGeneratedSurfaceProgram? (source : String) : Option SurfaceProgram :=
  match stripSurfaceProgramBody? source with
  | some body => parseGeneratedSurfaceBody? body
  | none => none

def stripSurfaceContractStorageFunctionBody? (source : String) :
    Option String :=
  let trimmed := source.trimAscii.toString
  if trimmed.startsWith surfaceContractStorageFunctionPrefix &&
      trimmed.endsWith surfaceContractFunctionSuffix then
    some
      ((((trimmed.drop surfaceContractStorageFunctionPrefix.length).dropEnd
        surfaceContractFunctionSuffix.length).trimAscii).toString)
  else
    none

def parseGeneratedSurfaceStorageFunction? (source : String) :
    Option SurfaceProgram :=
  match stripSurfaceContractStorageFunctionBody? source with
  | some body => parseGeneratedSurfaceStorageBody? body
  | none => none

def parseGeneratedSurfaceFunction? (source : String) :
    Option SurfaceProgram :=
  match stripSurfaceFunctionBody? source with
  | some body => parseGeneratedSurfaceBody? body
  | none => none

def parseSurfaceProgram? (source : String) : Option SurfaceProgram :=
  if source = surfaceBoundedLoopSwitchStorageBuiltinSource then
    some surfaceBoundedLoopSwitchStorageBuiltinProgram
  else if source = surfaceSwitchCasesStorageBuiltinSource then
    some surfaceSwitchCasesStorageBuiltinProgram
  else if source = surfaceParsedStateExprAddSource then
    some surfaceParsedStateExprAddProgram
  else if source = surfaceParsedStoredStateExprAddSource then
    some surfaceParsedStoredStateExprAddProgram
  else if source = surfaceParsedStoredStateExprMulSource then
    some surfaceParsedStoredStateExprMulProgram
  else if source = surfaceParsedStoredStateExprEqSource then
    some surfaceParsedStoredStateExprEqProgram
  else if source = surfaceParsedStoredStateExprLtSource then
    some surfaceParsedStoredStateExprLtProgram
  else if source = surfaceParsedStoredStateExprGtSource then
    some surfaceParsedStoredStateExprGtProgram
  else
    match parseGeneratedSurfaceProgram? source with
    | some program => some program
    | none =>
        match parseGeneratedSurfaceStorageFunction? source with
        | some program => some program
        | none => parseGeneratedSurfaceFunction? source

theorem parseSurfaceProgram?_surfaceBoundedLoopSwitchStorageBuiltinSource :
    parseSurfaceProgram? surfaceBoundedLoopSwitchStorageBuiltinSource =
      some surfaceBoundedLoopSwitchStorageBuiltinProgram := by
  simp [parseSurfaceProgram?]

theorem parseSurfaceProgram?_surfaceSwitchCasesStorageBuiltinSource :
    parseSurfaceProgram? surfaceSwitchCasesStorageBuiltinSource =
      some surfaceSwitchCasesStorageBuiltinProgram := by
  have hNe :
      surfaceSwitchCasesStorageBuiltinSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNe]
  simp

theorem parseSurfaceProgram?_surfaceParsedStateExprAddSource :
    parseSurfaceProgram? surfaceParsedStateExprAddSource =
      some surfaceParsedStateExprAddProgram := by
  have hNeBounded :
      surfaceParsedStateExprAddSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStateExprAddSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch]
  simp

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprAddSource :
    parseSurfaceProgram? surfaceParsedStoredStateExprAddSource =
      some surfaceParsedStoredStateExprAddProgram := by
  have hNeBounded :
      surfaceParsedStoredStateExprAddSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStoredStateExprAddSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  have hNeStateExpr :
      surfaceParsedStoredStateExprAddSource ≠ surfaceParsedStateExprAddSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch, if_neg hNeStateExpr]
  simp

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprMulSource :
    parseSurfaceProgram? surfaceParsedStoredStateExprMulSource =
      some surfaceParsedStoredStateExprMulProgram := by
  have hNeBounded :
      surfaceParsedStoredStateExprMulSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStoredStateExprMulSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  have hNeStateExpr :
      surfaceParsedStoredStateExprMulSource ≠ surfaceParsedStateExprAddSource := by
    decide
  have hNeStoredStateExpr :
      surfaceParsedStoredStateExprMulSource ≠
        surfaceParsedStoredStateExprAddSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch, if_neg hNeStateExpr,
    if_neg hNeStoredStateExpr]
  simp

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprEqSource :
    parseSurfaceProgram? surfaceParsedStoredStateExprEqSource =
      some surfaceParsedStoredStateExprEqProgram := by
  have hNeBounded :
      surfaceParsedStoredStateExprEqSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStoredStateExprEqSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  have hNeStateExpr :
      surfaceParsedStoredStateExprEqSource ≠ surfaceParsedStateExprAddSource := by
    decide
  have hNeStoredStateExpr :
      surfaceParsedStoredStateExprEqSource ≠
        surfaceParsedStoredStateExprAddSource := by
    decide
  have hNeStoredMul :
      surfaceParsedStoredStateExprEqSource ≠
        surfaceParsedStoredStateExprMulSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch, if_neg hNeStateExpr,
    if_neg hNeStoredStateExpr, if_neg hNeStoredMul]
  simp

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprLtSource :
    parseSurfaceProgram? surfaceParsedStoredStateExprLtSource =
      some surfaceParsedStoredStateExprLtProgram := by
  have hNeBounded :
      surfaceParsedStoredStateExprLtSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStoredStateExprLtSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  have hNeStateExpr :
      surfaceParsedStoredStateExprLtSource ≠ surfaceParsedStateExprAddSource := by
    decide
  have hNeStoredStateExpr :
      surfaceParsedStoredStateExprLtSource ≠
        surfaceParsedStoredStateExprAddSource := by
    decide
  have hNeStoredMul :
      surfaceParsedStoredStateExprLtSource ≠
        surfaceParsedStoredStateExprMulSource := by
    decide
  have hNeStoredEq :
      surfaceParsedStoredStateExprLtSource ≠
        surfaceParsedStoredStateExprEqSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch, if_neg hNeStateExpr,
    if_neg hNeStoredStateExpr, if_neg hNeStoredMul, if_neg hNeStoredEq]
  simp

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprGtSource :
    parseSurfaceProgram? surfaceParsedStoredStateExprGtSource =
      some surfaceParsedStoredStateExprGtProgram := by
  have hNeBounded :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceBoundedLoopSwitchStorageBuiltinSource := by
    decide
  have hNeSwitch :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceSwitchCasesStorageBuiltinSource := by
    decide
  have hNeStateExpr :
      surfaceParsedStoredStateExprGtSource ≠ surfaceParsedStateExprAddSource := by
    decide
  have hNeStoredStateExpr :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceParsedStoredStateExprAddSource := by
    decide
  have hNeStoredMul :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceParsedStoredStateExprMulSource := by
    decide
  have hNeStoredEq :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceParsedStoredStateExprEqSource := by
    decide
  have hNeStoredLt :
      surfaceParsedStoredStateExprGtSource ≠
        surfaceParsedStoredStateExprLtSource := by
    decide
  unfold parseSurfaceProgram?
  rw [if_neg hNeBounded, if_neg hNeSwitch, if_neg hNeStateExpr,
    if_neg hNeStoredStateExpr, if_neg hNeStoredMul, if_neg hNeStoredEq,
    if_neg hNeStoredLt]
  simp

theorem parseSurfaceProgram?_surfaceSwitchCasesStorageBuiltinSource_smoke :
    (parseSurfaceProgram?
      surfaceSwitchCasesStorageBuiltinSource).isSome = true := by
  rw [parseSurfaceProgram?_surfaceSwitchCasesStorageBuiltinSource]
  rfl

theorem parseSurfaceProgram?_some_of_isSome
    {sourceText : String}
    (hSome : (parseSurfaceProgram? sourceText).isSome = true) :
    ∃ program, parseSurfaceProgram? sourceText = some program := by
  cases hParsed : parseSurfaceProgram? sourceText with
  | none =>
      simp [hParsed] at hSome
  | some program =>
      exact ⟨program, rfl⟩

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprBitAndSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprBitAndSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprBitOrSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprBitOrSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprBitXorSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprBitXorSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprNeSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprNeSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprLeSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprLeSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprGeSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprGeSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprBitNotSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprBitNotSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoredStateExprIszeroSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoredStateExprIszeroSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoreThenIfLoadSwitchSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoreThenIfLoadSwitchSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoreThenIfLoadSkippedSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoreThenIfLoadSkippedSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedReturnBuiltinSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedReturnBuiltinSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedStoreLoadBuiltinSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoreLoadBuiltinSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarExprReturnSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedContractStorageVarExprReturnSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarSwitchSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedContractStorageVarSwitchSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarSwitchSource :
    parseSurfaceProgram? surfaceParsedContractStorageVarSwitchSource =
      some surfaceParsedContractStorageVarSwitchProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarSwitchTwoCaseSource :
    parseSurfaceProgram? surfaceParsedContractStorageVarSwitchTwoCaseSource =
      some surfaceParsedContractStorageVarSwitchTwoCaseProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarSwitchTwoCaseSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedContractStorageVarSwitchTwoCaseSource =
        some program := by
  rw [parseSurfaceProgram?_surfaceParsedContractStorageVarSwitchTwoCaseSource]
  exact ⟨surfaceParsedContractStorageVarSwitchTwoCaseProgram, rfl⟩

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarIfSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedContractStorageVarIfSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarIfSource :
    parseSurfaceProgram? surfaceParsedContractStorageVarIfSource =
      some surfaceParsedContractStorageVarIfProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedStoreThenSwitchLoadSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedStoreThenSwitchLoadSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedSwitchBuiltinSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedSwitchBuiltinSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceNamedSwitchBody?_surfaceParsedSwitchBuiltin :
    parseSurfaceNamedSwitchBody? SurfaceNameEnv.empty
        "switch 3 { case 1: return 9; case 2: return addmod(2, 3, 5); default: return 11; }" =
      some surfaceParsedSwitchBuiltinProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedSwitchBuiltinSource :
    parseSurfaceProgram? surfaceParsedSwitchBuiltinSource =
      some surfaceParsedSwitchBuiltinProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedBoundedWhileStorageSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedBoundedWhileStorageSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceStorageVarBoundedWhileReturnBody?_surfaceParsedContractStorageVarBoundedWhile :
    parseSurfaceStorageVarBoundedWhileReturnBody?
        "boundedWhile 2 1 { x = 2 + 3; } return x;" =
      some surfaceNamedBoundedWhileStorageProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarBoundedWhileSource :
    parseSurfaceProgram?
        surfaceParsedContractStorageVarBoundedWhileSource =
      some surfaceNamedBoundedWhileStorageProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedContractStorageVarBoundedWhileSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedContractStorageVarBoundedWhileSource =
        some program := by
  rw [parseSurfaceProgram?_surfaceParsedContractStorageVarBoundedWhileSource]
  exact ⟨surfaceNamedBoundedWhileStorageProgram, rfl⟩

theorem parseSurfaceProgram?_surfaceParsedBoundedWhileSwitchSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedBoundedWhileSwitchSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedIfStorageReturnSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedIfStorageReturnSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedIfElseSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedIfElseSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceNamedIfElseBody?_surfaceParsedIfElse :
    parseSurfaceNamedIfElseBody? SurfaceNameEnv.empty
        "if 0 { return 7; } else { return 11; }" =
      some surfaceParsedIfElseProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedIfElseSource :
    parseSurfaceProgram? surfaceParsedIfElseSource =
      some surfaceParsedIfElseProgram := by
  native_decide

theorem parseSurfaceProgram?_surfaceParsedFunctionIfStorageReturnSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedFunctionIfStorageReturnSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource_smoke :
    ∃ program,
      parseSurfaceProgram?
          surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

theorem parseSurfaceProgram?_surfaceParsedContractIfStorageReturnSource_smoke :
    ∃ program,
      parseSurfaceProgram? surfaceParsedContractIfStorageReturnSource =
        some program :=
  parseSurfaceProgram?_some_of_isSome (by native_decide)

structure SurfaceSourceCertificate where
  sourceText : String
  program : SurfaceProgram
  programCert : SurfaceProgramCertificate
  parsed : parseSurfaceProgram? sourceText = some program
  programCert_eq : programCert = compileSurfaceProgramCertificate program

def compileSurfaceSourceCertificate?
    (sourceText : String) : Option SurfaceSourceCertificate :=
  match hParsed : parseSurfaceProgram? sourceText with
  | some program =>
      some
        { sourceText := sourceText
          program := program
          programCert := compileSurfaceProgramCertificate program
          parsed := hParsed
          programCert_eq := rfl }
  | none => none

def compileSurfaceSourceStmt? (sourceText : String) : Option YulStmt :=
  (compileSurfaceSourceCertificate? sourceText).map
    (fun cert => cert.programCert.stmt)

def compileSurfaceSourceFuel? (sourceText : String) : Option Nat :=
  (compileSurfaceSourceCertificate? sourceText).map
    (fun cert => cert.programCert.fuel)

def SurfaceSourceCertificate.Verified
    (cert : SurfaceSourceCertificate) : Prop :=
  parseSurfaceProgram? cert.sourceText = some cert.program ∧
  SurfaceProgramCertificate.VerifiedForSource
    cert.program cert.programCert

def SurfaceSourceCertificate.VerifiedForText
    (sourceText : String) (cert : SurfaceSourceCertificate) : Prop :=
  cert.sourceText = sourceText ∧ SurfaceSourceCertificate.Verified cert

theorem SurfaceSourceCertificate.verified
    (cert : SurfaceSourceCertificate) :
    SurfaceSourceCertificate.Verified cert := by
  constructor
  · exact cert.parsed
  · rw [cert.programCert_eq]
    exact compileSurfaceProgramCertificate_verifiedForSource cert.program

theorem SurfaceSourceCertificate.verifiedForText
    (cert : SurfaceSourceCertificate) :
    SurfaceSourceCertificate.VerifiedForText cert.sourceText cert := by
  exact ⟨rfl, cert.verified⟩

theorem SurfaceSourceCertificate.dynamic_sound
    (cert : SurfaceSourceCertificate) (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        cert.programCert.fuel state.toConfig cert.programCert.stmt =
      (cert.program.eval state).toSymYulResults := by
  rw [cert.programCert_eq]
  exact
    SurfaceProgramCertificate.dynamic_sound
      (compileSurfaceProgramCertificate cert.program) state

theorem SurfaceSourceCertificate.staticChecked
    (cert : SurfaceSourceCertificate) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        cert.programCert.fuel initialStaticContext false true
        cert.programCert.stmt =
      some initialStaticContext := by
  rw [cert.programCert_eq]
  exact
    SurfaceProgramCertificate.staticChecked
      (compileSurfaceProgramCertificate cert.program)

theorem SurfaceSourceCertificate.accepted_currentSolidCore
    (cert : SurfaceSourceCertificate) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      cert.programCert.fuel initialStaticContext false true
      cert.programCert.stmt initialStaticContext := by
  rw [cert.programCert_eq]
  exact
    SurfaceProgramCertificate.accepted_currentSolidCore
      (compileSurfaceProgramCertificate cert.program)

theorem compileSurfaceSourceCertificate?_sourceText
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert) :
    cert.sourceText = sourceText := by
  unfold compileSurfaceSourceCertificate? at hCompile
  split at hCompile <;> cases hCompile
  rfl

theorem compileSurfaceSourceCertificate?_verifiedForText
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert) :
    SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  exact ⟨compileSurfaceSourceCertificate?_sourceText hCompile,
    cert.verified⟩

set_option maxRecDepth 4096 in
theorem compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    {sourceText : String}
    (hCompileSome :
      (compileSurfaceSourceCertificate? sourceText).isSome = true) :
    ∃ cert,
      compileSurfaceSourceCertificate? sourceText = some cert ∧
      SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  cases hCompile : compileSurfaceSourceCertificate? sourceText with
  | none =>
      simp [hCompile] at hCompileSome
  | some cert =>
      refine ⟨cert, rfl, ?_⟩
      exact And.intro
        (compileSurfaceSourceCertificate?_sourceText hCompile)
        (SurfaceSourceCertificate.verified cert)

theorem compileSurfaceSourceCertificate?_surfaceParsedReturnBuiltinSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate? surfaceParsedReturnBuiltinSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedReturnBuiltinSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoreLoadBuiltinSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate? surfaceParsedStoreLoadBuiltinSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoreLoadBuiltinSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractStorageVarExprReturnSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractStorageVarExprReturnSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractStorageVarExprReturnSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractStorageVarSwitchSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractStorageVarSwitchSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractStorageVarSwitchSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractStorageVarSwitchTwoCaseSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractStorageVarSwitchTwoCaseSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractStorageVarSwitchTwoCaseSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractStorageVarIfSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractStorageVarIfSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractStorageVarIfSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoreThenSwitchLoadSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoreThenSwitchLoadSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoreThenSwitchLoadSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedSwitchBuiltinSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate? surfaceParsedSwitchBuiltinSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedSwitchBuiltinSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedBoundedWhileStorageSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedBoundedWhileStorageSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedBoundedWhileStorageSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractStorageVarBoundedWhileSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractStorageVarBoundedWhileSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractStorageVarBoundedWhileSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedBoundedWhileSwitchSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedBoundedWhileSwitchSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedBoundedWhileSwitchSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedIfStorageReturnSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate? surfaceParsedIfStorageReturnSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedIfStorageReturnSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedIfElseSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate? surfaceParsedIfElseSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedIfElseSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedFunctionIfStorageReturnSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedFunctionIfStorageReturnSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedFunctionIfStorageReturnSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedPublicFunctionStoreThenIfLoadSwitchSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedContractIfStorageReturnSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedContractIfStorageReturnSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedContractIfStorageReturnSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprBitAndSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprBitAndSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprBitAndSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprBitOrSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprBitOrSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprBitOrSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprBitXorSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprBitXorSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprBitXorSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprNeSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprNeSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprNeSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprLeSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprLeSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprLeSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprGeSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprGeSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprGeSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprBitNotSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprBitNotSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprBitNotSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoredStateExprIszeroSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoredStateExprIszeroSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoredStateExprIszeroSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoreThenIfLoadSwitchSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoreThenIfLoadSwitchSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoreThenIfLoadSwitchSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_surfaceParsedStoreThenIfLoadSkippedSource_smoke :
    ∃ cert,
      compileSurfaceSourceCertificate?
          surfaceParsedStoreThenIfLoadSkippedSource =
        some cert ∧
      SurfaceSourceCertificate.VerifiedForText
        surfaceParsedStoreThenIfLoadSkippedSource cert :=
  compileSurfaceSourceCertificate?_verifiedForText_of_isSome
    (by native_decide)

theorem compileSurfaceSourceCertificate?_map_stmt
    (sourceText : String) :
    (compileSurfaceSourceCertificate? sourceText).map
        (fun cert => cert.programCert.stmt) =
      compileSurfaceSourceStmt? sourceText := by
  rfl

theorem compileSurfaceSourceCertificate?_map_fuel
    (sourceText : String) :
    (compileSurfaceSourceCertificate? sourceText).map
        (fun cert => cert.programCert.fuel) =
      compileSurfaceSourceFuel? sourceText := by
  rfl

theorem compileSurfaceSourceCertificate?_dynamic_sound
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (_hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert)
    (state : State) :
    SolidCoreYulCore.SymYul.evalStmtFuel
        cert.programCert.fuel state.toConfig cert.programCert.stmt =
      (cert.program.eval state).toSymYulResults := by
  exact cert.dynamic_sound state

theorem compileSurfaceSourceCertificate?_staticChecked
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (_hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert) :
    SolidCoreYulCore.FullYul.checkStmtFuel
        cert.programCert.fuel initialStaticContext false true
        cert.programCert.stmt =
      some initialStaticContext := by
  exact cert.staticChecked

theorem compileSurfaceSourceCertificate?_accepted_currentSolidCore
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (_hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert) :
    SolidCoreYulCore.FullYul.CompilerAcceptedStmt
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      cert.programCert.fuel initialStaticContext false true
      cert.programCert.stmt initialStaticContext := by
  exact cert.accepted_currentSolidCore

set_option maxRecDepth 4096 in
theorem compileSurfaceSourceStmt?_verified_certificate
    {sourceText : String} {stmt : YulStmt}
    (hCompile : compileSurfaceSourceStmt? sourceText = some stmt) :
    ∃ cert,
      compileSurfaceSourceCertificate? sourceText = some cert ∧
      cert.programCert.stmt = stmt ∧
      SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  unfold compileSurfaceSourceStmt? at hCompile
  cases hCert : compileSurfaceSourceCertificate? sourceText with
  | none =>
      simp [hCert] at hCompile
  | some cert =>
      simp [hCert] at hCompile
      have hSource : cert.sourceText = sourceText :=
        compileSurfaceSourceCertificate?_sourceText hCert
      refine Exists.intro cert ?_
      refine And.intro rfl ?_
      refine And.intro hCompile ?_
      exact And.intro hSource (SurfaceSourceCertificate.verified cert)

theorem compileSurfaceSourceStmt?_some_iff_verified_certificate
    {sourceText : String} {stmt : YulStmt} :
    compileSurfaceSourceStmt? sourceText = some stmt ↔
      ∃ cert,
        compileSurfaceSourceCertificate? sourceText = some cert ∧
        cert.programCert.stmt = stmt ∧
        SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  constructor
  · intro hCompile
    exact compileSurfaceSourceStmt?_verified_certificate hCompile
  · intro hCert
    rcases hCert with ⟨cert, hCompileCert, hStmt, _hVerified⟩
    unfold compileSurfaceSourceStmt?
    rw [hCompileCert]
    simp [hStmt]

theorem compileSurfaceSourceStmt?_sound_flat
    {sourceText : String} {stmt : YulStmt}
    (hCompile : compileSurfaceSourceStmt? sourceText = some stmt)
    (state : State) :
    ∃ cert,
      compileSurfaceSourceCertificate? sourceText = some cert ∧
      cert.programCert.stmt = stmt ∧
      SolidCoreYulCore.SymYul.evalStmtFuel
          cert.programCert.fuel state.toConfig stmt =
        (cert.program.eval state).toSymYulResults ∧
      SolidCoreYulCore.FullYul.checkStmtFuel
          cert.programCert.fuel initialStaticContext false true stmt =
        some initialStaticContext ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        cert.programCert.fuel initialStaticContext false true stmt
        initialStaticContext ∧
      SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  rcases compileSurfaceSourceStmt?_verified_certificate hCompile with
    ⟨cert, hCert, hStmt, hVerified⟩
  refine ⟨cert, hCert, hStmt, ?_, ?_, ?_, hVerified⟩
  · rw [← hStmt]
    exact cert.dynamic_sound state
  · rw [← hStmt]
    exact cert.staticChecked
  · rw [← hStmt]
    exact cert.accepted_currentSolidCore

end MVP
end Solidity
end SolidCore

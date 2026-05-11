import SolidCoreYulCore.Evm

namespace SolidCore
namespace Solidity
namespace Source

abbrev Word := SolidCoreYulCore.Word
abbrev Byte := Nat

def wordModulus : Nat :=
  SolidCoreYulCore.wordModulus

def normWord (value : Nat) : Word :=
  SolidCoreYulCore.norm value

def normByte (value : Nat) : Byte :=
  value % 256

def boolWord (value : Bool) : Word :=
  if value then 1 else 0

def wordTruthy (value : Word) : Bool :=
  !(SolidCoreYulCore.norm value == 0)

def wordEq (lhs rhs : Word) : Bool :=
  SolidCoreYulCore.norm lhs == SolidCoreYulCore.norm rhs

inductive Ty where
  | uint256 : Ty
  | bytesCalldata : Ty
  | fixedArray : Nat -> Ty -> Ty
  | tuple : List Ty -> Ty
  deriving Repr

inductive Value where
  | word : Word -> Value
  | bytes : List Byte -> Value
  | fixedArray : List Value -> Value
  | tuple : List Value -> Value
  deriving Repr

def Ty.defaultValue : Ty -> Value
  | Ty.uint256 => Value.word 0
  | Ty.bytesCalldata => Value.bytes []
  | Ty.fixedArray size elementTy =>
      Value.fixedArray (List.replicate size elementTy.defaultValue)
  | Ty.tuple elements =>
      Value.tuple (elements.map Ty.defaultValue)

def Value.asWord? : Value -> Option Word
  | Value.word value => some (SolidCoreYulCore.norm value)
  | _ => none

def Value.asBytes? : Value -> Option (List Byte)
  | Value.bytes bs => some (bs.map normByte)
  | _ => none

def Value.length? : Value -> Option Nat
  | Value.bytes bs => some bs.length
  | Value.fixedArray values => some values.length
  | Value.tuple values => some values.length
  | Value.word _ => none

def listUpdateAt? {α : Type} : List α -> Nat -> α -> Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value =>
      match listUpdateAt? rest index value with
      | some updated => some (head :: updated)
      | none => none

def listGet? {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, index + 1 => listGet? rest index

inductive RevertData where
  | panic : Word -> RevertData
  | custom : String -> List Value -> RevertData
  deriving Repr

def RevertData.overflow : RevertData :=
  RevertData.panic 0x11

def RevertData.divByZero : RevertData :=
  RevertData.panic 0x12

def RevertData.indexOutOfBounds : RevertData :=
  RevertData.panic 0x32

def RevertData.typeMismatch : RevertData :=
  RevertData.panic 0

def Value.expectWord : Value -> Except RevertData Word
  | Value.word value => Except.ok (SolidCoreYulCore.norm value)
  | _ => Except.error RevertData.typeMismatch

def Value.index? (container : Value) (index : Word) :
    Except RevertData Value :=
  match container with
  | Value.bytes bs =>
      match listGet? (bs.map normByte) (SolidCoreYulCore.norm index) with
      | some byte => Except.ok (Value.word byte)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.fixedArray values =>
      match listGet? values (SolidCoreYulCore.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.tuple values =>
      match listGet? values (SolidCoreYulCore.norm index) with
      | some value => Except.ok value
      | none => Except.error RevertData.indexOutOfBounds
  | Value.word _ =>
      Except.error RevertData.typeMismatch

def Value.setIndex? (container : Value) (index : Word) (value : Value) :
    Except RevertData Value :=
  match container with
  | Value.fixedArray values =>
      match listUpdateAt? values (SolidCoreYulCore.norm index) value with
      | some updated => Except.ok (Value.fixedArray updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.bytes bs =>
      match value.asWord? with
      | some w =>
          match listUpdateAt? (bs.map normByte)
              (SolidCoreYulCore.norm index) (normByte w) with
          | some updated => Except.ok (Value.bytes updated)
          | none => Except.error RevertData.indexOutOfBounds
      | none => Except.error RevertData.typeMismatch
  | Value.tuple values =>
      match listUpdateAt? values (SolidCoreYulCore.norm index) value with
      | some updated => Except.ok (Value.tuple updated)
      | none => Except.error RevertData.indexOutOfBounds
  | Value.word _ =>
      Except.error RevertData.typeMismatch

abbrev WordMap := List (Word × Word)

def WordMap.lookup? : WordMap -> Word -> Option Word
  | [], _ => none
  | (key, value) :: rest, query =>
      if wordEq key query then
        some (SolidCoreYulCore.norm value)
      else
        WordMap.lookup? rest query

def WordMap.insertLoop : WordMap -> Word -> Word -> WordMap
  | [], key, value =>
      [(SolidCoreYulCore.norm key, SolidCoreYulCore.norm value)]
  | (entryKey, entryValue) :: rest, key, value =>
      if wordEq entryKey key then
        (SolidCoreYulCore.norm key, SolidCoreYulCore.norm value) :: rest
      else
        (entryKey, entryValue) :: WordMap.insertLoop rest key value

structure Event where
  name : String
  indexed : List Value
  data : List Value
  deriving Repr

structure State where
  storage : WordMap
  events : List Event
  deriving Repr

def State.empty : State :=
  { storage := [], events := [] }

def State.loadSlot (state : State) (slot : Word) : Word :=
  match WordMap.lookup? state.storage slot with
  | some value => value
  | none => 0

def State.storeSlot (state : State) (slot value : Word) : State :=
  { state with storage := WordMap.insertLoop state.storage slot value }

abbrev Frame := List (String × Value)
abbrev LocalEnv := List Frame

def Frame.lookup? : Frame -> String -> Option Value
  | [], _ => none
  | (name, value) :: rest, query =>
      if name = query then
        some value
      else
        Frame.lookup? rest query

def Frame.assign? : Frame -> String -> Value -> Option Frame
  | [], _, _ => none
  | (name, oldValue) :: rest, query, value =>
      if name = query then
        some ((name, value) :: rest)
      else
        match Frame.assign? rest query value with
        | some updated => some ((name, oldValue) :: updated)
        | none => none

def LocalEnv.lookup? : LocalEnv -> String -> Option Value
  | [], _ => none
  | frame :: rest, name =>
      match Frame.lookup? frame name with
      | some value => some value
      | none => LocalEnv.lookup? rest name

def LocalEnv.assign? : LocalEnv -> String -> Value -> Option LocalEnv
  | [], _, _ => none
  | frame :: rest, name, value =>
      match Frame.assign? frame name value with
      | some updated => some (updated :: rest)
      | none =>
          match LocalEnv.assign? rest name value with
          | some updatedRest => some (frame :: updatedRest)
          | none => none

def LocalEnv.declare (locals : LocalEnv) (name : String) (value : Value) :
    LocalEnv :=
  match locals with
  | [] => [[(name, value)]]
  | frame :: rest => ((name, value) :: frame) :: rest

structure Runtime where
  state : State
  locals : LocalEnv
  deriving Repr

def Runtime.ofState (state : State) : Runtime :=
  { state, locals := [[]] }

def Runtime.pushScope (runtime : Runtime) : Runtime :=
  { runtime with locals := [] :: runtime.locals }

def Runtime.popScope (runtime : Runtime) : Runtime :=
  { runtime with locals := runtime.locals.drop 1 }

def Runtime.lookupLocal? (runtime : Runtime) (name : String) :
    Option Value :=
  LocalEnv.lookup? runtime.locals name

def Runtime.declareLocal
    (runtime : Runtime) (name : String) (value : Value) : Runtime :=
  { runtime with locals := LocalEnv.declare runtime.locals name value }

def Runtime.assignLocal?
    (runtime : Runtime) (name : String) (value : Value) :
    Option Runtime :=
  match LocalEnv.assign? runtime.locals name value with
  | some locals => some { runtime with locals }
  | none => none

structure StorageField where
  name : String
  slot : Word
  deriving Repr

structure EventDecl where
  name : String
  indexedCount : Nat
  deriving Repr

structure ErrorDecl where
  name : String
  selector : Word
  fields : List Ty
  deriving Repr

structure Context where
  storageFields : List StorageField
  eventDecls : List EventDecl
  checked : Bool
  deriving Repr

def Context.empty : Context :=
  { storageFields := [], eventDecls := [], checked := true }

def Context.storageSlot? (context : Context) (name : String) :
    Option Word :=
  match context.storageFields.find? (fun field => field.name == name) with
  | some field => some field.slot
  | none => none

def Context.eventDecl? (context : Context) (name : String) :
    Option EventDecl :=
  context.eventDecls.find? (fun event => event.name == name)

def Runtime.loadStorageField (context : Context)
    (runtime : Runtime) (name : String) : Except RevertData Value :=
  match context.storageSlot? name with
  | some slot => Except.ok (Value.word (runtime.state.loadSlot slot))
  | none => Except.error RevertData.typeMismatch

def Runtime.storeStorageField (context : Context)
    (runtime : Runtime) (name : String) (value : Value) :
    Except RevertData Runtime := do
  let slot ←
    match context.storageSlot? name with
    | some slot => Except.ok slot
    | none => Except.error RevertData.typeMismatch
  let word ← value.expectWord
  Except.ok { runtime with state := runtime.state.storeSlot slot word }

inductive UnaryOp where
  | bitNot : UnaryOp
  | logicalNot : UnaryOp
  | neg : UnaryOp
  deriving Repr

inductive BinaryOp where
  | add : BinaryOp
  | sub : BinaryOp
  | mul : BinaryOp
  | div : BinaryOp
  | mod : BinaryOp
  | bitAnd : BinaryOp
  | bitOr : BinaryOp
  | bitXor : BinaryOp
  | shl : BinaryOp
  | shr : BinaryOp
  | lt : BinaryOp
  | gt : BinaryOp
  | le : BinaryOp
  | ge : BinaryOp
  | eq : BinaryOp
  | ne : BinaryOp
  | boolAnd : BinaryOp
  | boolOr : BinaryOp
  deriving Repr

inductive Expr where
  | word : Word -> Expr
  | var : String -> Expr
  | storage : String -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | length : Expr -> Expr
  | index : Expr -> Expr -> Expr
  deriving Repr

inductive LValue where
  | var : String -> LValue
  | storage : String -> LValue
  | index : LValue -> Expr -> LValue
  deriving Repr

def LValue.toExpr : LValue -> Expr
  | LValue.var name => Expr.var name
  | LValue.storage name => Expr.storage name
  | LValue.index base idx => Expr.index base.toExpr idx

def checkedAdd (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  let raw := SolidCoreYulCore.norm lhs + SolidCoreYulCore.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCoreYulCore.addWord lhs rhs)

def checkedSub (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if checked && (SolidCoreYulCore.norm lhs < SolidCoreYulCore.norm rhs) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCoreYulCore.subWord lhs rhs)

def checkedMul (checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  let raw := SolidCoreYulCore.norm lhs * SolidCoreYulCore.norm rhs
  if checked && (wordModulus <= raw) then
    Except.error RevertData.overflow
  else
    Except.ok (SolidCoreYulCore.mulWord lhs rhs)

def checkedDiv (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SolidCoreYulCore.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCoreYulCore.divWord lhs rhs)

def checkedMod (_checked : Bool) (lhs rhs : Word) :
    Except RevertData Word :=
  if SolidCoreYulCore.norm rhs = 0 then
    Except.error RevertData.divByZero
  else
    Except.ok (SolidCoreYulCore.modWord lhs rhs)

def BinaryOp.applyWord
    (checked : Bool) (op : BinaryOp) (lhs rhs : Word) :
    Except RevertData Word :=
  match op with
  | BinaryOp.add => checkedAdd checked lhs rhs
  | BinaryOp.sub => checkedSub checked lhs rhs
  | BinaryOp.mul => checkedMul checked lhs rhs
  | BinaryOp.div => checkedDiv checked lhs rhs
  | BinaryOp.mod => checkedMod checked lhs rhs
  | BinaryOp.bitAnd => Except.ok (SolidCoreYulCore.andWord lhs rhs)
  | BinaryOp.bitOr => Except.ok (SolidCoreYulCore.orWord lhs rhs)
  | BinaryOp.bitXor => Except.ok (SolidCoreYulCore.xorWord lhs rhs)
  | BinaryOp.shl => Except.ok (SolidCoreYulCore.shlWord rhs lhs)
  | BinaryOp.shr => Except.ok (SolidCoreYulCore.shrWord rhs lhs)
  | BinaryOp.lt => Except.ok (SolidCoreYulCore.ltWord lhs rhs)
  | BinaryOp.gt => Except.ok (SolidCoreYulCore.gtWord lhs rhs)
  | BinaryOp.le =>
      Except.ok (boolWord (!(wordTruthy (SolidCoreYulCore.gtWord lhs rhs))))
  | BinaryOp.ge =>
      Except.ok (boolWord (!(wordTruthy (SolidCoreYulCore.ltWord lhs rhs))))
  | BinaryOp.eq => Except.ok (boolWord (wordEq lhs rhs))
  | BinaryOp.ne => Except.ok (boolWord (!(wordEq lhs rhs)))
  | BinaryOp.boolAnd => Except.ok (boolWord (wordTruthy lhs && wordTruthy rhs))
  | BinaryOp.boolOr => Except.ok (boolWord (wordTruthy lhs || wordTruthy rhs))

def BinaryOp.apply
    (checked : Bool) (op : BinaryOp) (lhs rhs : Value) :
    Except RevertData Value :=
  match op with
  | BinaryOp.eq =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          Except.ok (Value.word (boolWord (wordEq lhsWord rhsWord)))
      | _, _ => Except.error RevertData.typeMismatch
  | BinaryOp.ne =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          Except.ok (Value.word (boolWord (!(wordEq lhsWord rhsWord))))
      | _, _ => Except.error RevertData.typeMismatch
  | _ => do
      let lhsWord ← lhs.expectWord
      let rhsWord ← rhs.expectWord
      let value ← op.applyWord checked lhsWord rhsWord
      Except.ok (Value.word value)

def UnaryOp.apply (checked : Bool) (op : UnaryOp) (value : Value) :
    Except RevertData Value := do
  let word ← value.expectWord
  match op with
  | UnaryOp.bitNot =>
      Except.ok (Value.word (SolidCoreYulCore.notWord word))
  | UnaryOp.logicalNot =>
      Except.ok (Value.word (boolWord (!(wordTruthy word))))
  | UnaryOp.neg =>
      if checked && wordTruthy word then
        Except.error RevertData.overflow
      else
        Except.ok (Value.word (SolidCoreYulCore.subWord 0 word))

def Expr.eval (context : Context) (runtime : Runtime) :
    Expr -> Except RevertData Value
  | Expr.word value => Except.ok (Value.word (normWord value))
  | Expr.var name =>
      match runtime.lookupLocal? name with
      | some value => Except.ok value
      | none => Except.error RevertData.typeMismatch
  | Expr.storage name =>
      runtime.loadStorageField context name
  | Expr.unary op expr => do
      let value ← expr.eval context runtime
      op.apply context.checked value
  | Expr.binary BinaryOp.boolAnd lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        let rhsValue ← rhs.eval context runtime
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)))
      else
        Except.ok (Value.word 0)
  | Expr.binary BinaryOp.boolOr lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let lhsWord ← lhsValue.expectWord
      if wordTruthy lhsWord then
        Except.ok (Value.word 1)
      else
        let rhsValue ← rhs.eval context runtime
        let rhsWord ← rhsValue.expectWord
        Except.ok (Value.word (boolWord (wordTruthy rhsWord)))
  | Expr.binary op lhs rhs => do
      let lhsValue ← lhs.eval context runtime
      let rhsValue ← rhs.eval context runtime
      BinaryOp.apply context.checked op lhsValue rhsValue
  | Expr.length expr => do
      let value ← expr.eval context runtime
      match value.length? with
      | some len => Except.ok (Value.word len)
      | none => Except.error RevertData.typeMismatch
  | Expr.index base idx => do
      let baseValue ← base.eval context runtime
      let indexValue ← idx.eval context runtime
      let indexWord ← indexValue.expectWord
      baseValue.index? indexWord

def Expr.evalList (context : Context) (runtime : Runtime) :
    List Expr -> Except RevertData (List Value)
  | [] => Except.ok []
  | expr :: rest => do
      let value ← expr.eval context runtime
      let values ← Expr.evalList context runtime rest
      Except.ok (value :: values)

def LValue.read (context : Context) (runtime : Runtime) :
    LValue -> Except RevertData Value
  | LValue.var name =>
      match runtime.lookupLocal? name with
      | some value => Except.ok value
      | none => Except.error RevertData.typeMismatch
  | LValue.storage name =>
      runtime.loadStorageField context name
  | LValue.index base idx => do
      let baseValue ← base.read context runtime
      let indexValue ← idx.eval context runtime
      let indexWord ← indexValue.expectWord
      baseValue.index? indexWord

def LValue.write (context : Context) (runtime : Runtime)
    (target : LValue) (value : Value) : Except RevertData Runtime :=
  match target with
  | LValue.var name =>
      match runtime.assignLocal? name value with
      | some updated => Except.ok updated
      | none => Except.error RevertData.typeMismatch
  | LValue.storage name =>
      runtime.storeStorageField context name value
  | LValue.index base idx => do
      let baseValue ← base.read context runtime
      let indexValue ← idx.eval context runtime
      let indexWord ← indexValue.expectWord
      let updatedBase ← baseValue.setIndex? indexWord value
      base.write context runtime updatedBase

inductive Stmt where
  | skip : Stmt
  | block : List Stmt -> Stmt
  | varDecl : Ty -> String -> Option Expr -> Stmt
  | assign : LValue -> Expr -> Stmt
  | assignOp : LValue -> BinaryOp -> Expr -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break : Stmt
  | continue : Stmt
  | returnValues : List Expr -> Stmt
  | revert : String -> List Expr -> Stmt
  | emitEvent : String -> List Expr -> Stmt
  | unchecked : Stmt -> Stmt
  deriving Repr

inductive Result where
  | normal : Runtime -> Result
  | returned : Runtime -> List Value -> Result
  | reverted : Runtime -> RevertData -> Result
  | broke : Runtime -> Result
  | continued : Runtime -> Result
  deriving Repr

def Result.mapRuntime (f : Runtime -> Runtime) : Result -> Result
  | Result.normal runtime => Result.normal (f runtime)
  | Result.returned runtime values => Result.returned (f runtime) values
  | Result.reverted runtime data => Result.reverted (f runtime) data
  | Result.broke runtime => Result.broke (f runtime)
  | Result.continued runtime => Result.continued (f runtime)

def Result.runtime : Result -> Runtime
  | Result.normal runtime => runtime
  | Result.returned runtime _ => runtime
  | Result.reverted runtime _ => runtime
  | Result.broke runtime => runtime
  | Result.continued runtime => runtime

def Runtime.emitEvent (context : Context)
    (runtime : Runtime) (name : String) (values : List Value) :
    Except RevertData Runtime :=
  match context.eventDecl? name with
  | some decl =>
      let event : Event :=
        { name := name
          indexed := values.take decl.indexedCount
          data := values.drop decl.indexedCount }
      Except.ok
        { runtime with
          state := { runtime.state with
            events := runtime.state.events ++ [event] } }
  | none => Except.error RevertData.typeMismatch

def Stmt.findSwitchBranch? (value : Word) :
    List (Word × Stmt) -> Option Stmt
  | [] => none
  | (label, body) :: rest =>
      if wordEq label value then
        some body
      else
        Stmt.findSwitchBranch? value rest

mutual

def Stmt.eval (fuel : Nat) (context : Context)
    (runtime : Runtime) : Stmt -> Option Result :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun stmt =>
      match stmt with
      | Stmt.skip => some (Result.normal runtime)
      | Stmt.block body =>
          match Stmt.evalList fuel context runtime.pushScope body with
          | some result => some (result.mapRuntime Runtime.popScope)
          | none => none
      | Stmt.varDecl ty name init =>
          match init with
          | some expr =>
              match expr.eval context runtime with
              | Except.ok value =>
                  some (Result.normal (runtime.declareLocal name value))
              | Except.error err =>
                  some (Result.reverted runtime err)
          | none =>
              some
                (Result.normal
                  (runtime.declareLocal name ty.defaultValue))
      | Stmt.assign target expr =>
          match expr.eval context runtime with
          | Except.ok value =>
              match target.write context runtime value with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.assignOp target op expr =>
          match target.read context runtime, expr.eval context runtime with
          | Except.ok lhs, Except.ok rhs =>
              match BinaryOp.apply context.checked op lhs rhs with
              | Except.ok value =>
                  match target.write context runtime value with
                  | Except.ok updated => some (Result.normal updated)
                  | Except.error err => some (Result.reverted runtime err)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err, _ => some (Result.reverted runtime err)
          | _, Except.error err => some (Result.reverted runtime err)
      | Stmt.ifElse cond thenBranch elseBranch =>
          match cond.eval context runtime with
          | Except.ok value =>
              match value.expectWord with
              | Except.ok word =>
                  if wordTruthy word then
                    Stmt.eval fuel context runtime thenBranch
                  else
                    Stmt.eval fuel context runtime elseBranch
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.switch discr cases defaultBranch =>
          match discr.eval context runtime with
          | Except.ok value =>
              match value.expectWord with
              | Except.ok word =>
                  match Stmt.findSwitchBranch? word cases, defaultBranch with
                  | some branch, _ => Stmt.eval fuel context runtime branch
                  | none, some branch => Stmt.eval fuel context runtime branch
                  | none, none => some (Result.normal runtime)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.whileLoop cond body =>
          Stmt.evalWhile fuel context runtime cond body
      | Stmt.forLoop init cond post body =>
          let loopRuntime := runtime.pushScope
          match Stmt.eval fuel context loopRuntime init with
          | some (Result.normal initialized) =>
              match Stmt.evalFor fuel context initialized cond post body with
              | some result => some (result.mapRuntime Runtime.popScope)
              | none => none
          | some result => some (result.mapRuntime Runtime.popScope)
          | none => none
      | Stmt.break => some (Result.broke runtime)
      | Stmt.continue => some (Result.continued runtime)
      | Stmt.returnValues exprs =>
          match Expr.evalList context runtime exprs with
          | Except.ok values => some (Result.returned runtime values)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.revert name exprs =>
          match Expr.evalList context runtime exprs with
          | Except.ok values =>
              some (Result.reverted runtime (RevertData.custom name values))
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.emitEvent name exprs =>
          match Expr.evalList context runtime exprs with
          | Except.ok values =>
              match runtime.emitEvent context name values with
              | Except.ok updated => some (Result.normal updated)
              | Except.error err => some (Result.reverted runtime err)
          | Except.error err => some (Result.reverted runtime err)
      | Stmt.unchecked body =>
          Stmt.eval fuel { context with checked := false } runtime body

def Stmt.evalList (fuel : Nat) (context : Context)
    (runtime : Runtime) : List Stmt -> Option Result
  | [] => some (Result.normal runtime)
  | stmt :: rest =>
      match Stmt.eval fuel context runtime stmt with
      | some (Result.normal runtime') =>
          Stmt.evalList fuel context runtime' rest
      | some result => some result
      | none => none

def Stmt.evalWhile (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.eval context runtime with
      | Except.ok value =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match Stmt.eval fuel context runtime body with
                | some (Result.normal runtime') =>
                    Stmt.evalWhile fuel context runtime' cond body
                | some (Result.continued runtime') =>
                    Stmt.evalWhile fuel context runtime' cond body
                | some (Result.broke runtime') =>
                    some (Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Result.normal runtime)
          | Except.error err => some (Result.reverted runtime err)
      | Except.error err => some (Result.reverted runtime err)

def Stmt.evalFor (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.eval context runtime with
      | Except.ok value =>
          match value.expectWord with
          | Except.ok word =>
              if wordTruthy word then
                match Stmt.eval fuel context runtime body with
                | some (Result.normal runtime') =>
                    match Stmt.eval fuel context runtime' post with
                    | some (Result.normal posted) =>
                        Stmt.evalFor fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Result.continued runtime') =>
                    match Stmt.eval fuel context runtime' post with
                    | some (Result.normal posted) =>
                        Stmt.evalFor fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Result.broke runtime') =>
                    some (Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Result.normal runtime)
          | Except.error err => some (Result.reverted runtime err)
      | Except.error err => some (Result.reverted runtime err)

end

structure BindingDecl where
  name : String
  ty : Ty
  deriving Repr

structure FunctionDef where
  name : String
  selector? : Option Word
  params : List BindingDecl
  returns : List BindingDecl
  body : Stmt
  deriving Repr

inductive CallResult where
  | returned : State -> List Value -> CallResult
  | reverted : State -> RevertData -> CallResult
  deriving Repr

def BindingDecl.defaultBinding (decl : BindingDecl) : String × Value :=
  (decl.name, decl.ty.defaultValue)

def BindingDecl.bindArg (decl : BindingDecl) (value : Value) :
    String × Value :=
  (decl.name, value)

def FunctionDef.initialFrame? (function : FunctionDef)
    (args : List Value) : Option Frame :=
  if function.params.length = args.length then
    some
      ((function.params.zipWith BindingDecl.bindArg args) ++
        function.returns.map BindingDecl.defaultBinding)
  else
    none

def FunctionDef.collectReturns (function : FunctionDef)
    (runtime : Runtime) : Except RevertData (List Value) :=
  let rec collect : List BindingDecl -> Except RevertData (List Value)
    | [] => Except.ok []
    | decl :: rest => do
        let value ←
          match runtime.lookupLocal? decl.name with
          | some value => Except.ok value
          | none => Except.error RevertData.typeMismatch
        let values ← collect rest
        Except.ok (value :: values)
  collect function.returns

def FunctionDef.call? (fuel : Nat) (context : Context)
    (function : FunctionDef) (state : State) (args : List Value) :
    Option CallResult :=
  match function.initialFrame? args with
  | some frame =>
      let runtime : Runtime := { state, locals := [frame] }
      match Stmt.eval fuel context runtime function.body with
      | some (Result.normal runtime') =>
          match function.collectReturns runtime' with
          | Except.ok values => some (CallResult.returned runtime'.state values)
          | Except.error err =>
              some (CallResult.reverted runtime'.state err)
      | some (Result.returned runtime' values) =>
          if values.isEmpty then
            match function.collectReturns runtime' with
            | Except.ok namedValues =>
                some (CallResult.returned runtime'.state namedValues)
            | Except.error err =>
                some (CallResult.reverted runtime'.state err)
          else
            some (CallResult.returned runtime'.state values)
      | some (Result.reverted runtime' revert) =>
          some (CallResult.reverted runtime'.state revert)
      | some (Result.broke runtime') =>
          some (CallResult.reverted runtime'.state RevertData.typeMismatch)
      | some (Result.continued runtime') =>
          some (CallResult.reverted runtime'.state RevertData.typeMismatch)
      | none => none
  | none => none

structure Contract where
  storageFields : List StorageField
  eventDecls : List EventDecl
  errorDecls : List ErrorDecl
  functions : List FunctionDef
  deriving Repr

def Contract.context (contract : Contract) : Context :=
  { storageFields := contract.storageFields
    eventDecls := contract.eventDecls
    checked := true }

def Contract.findFunctionByName? (contract : Contract)
    (name : String) : Option FunctionDef :=
  contract.functions.find? (fun function => function.name == name)

def Contract.findFunctionBySelector? (contract : Contract)
    (selector : Word) : Option FunctionDef :=
  contract.functions.find? (fun function =>
    match function.selector? with
    | some candidate => wordEq candidate selector
    | none => false)

inductive CallTarget where
  | name : String -> CallTarget
  | selector : Word -> CallTarget
  deriving Repr

def Contract.findFunction? (contract : Contract) :
    CallTarget -> Option FunctionDef
  | CallTarget.name name => contract.findFunctionByName? name
  | CallTarget.selector selector => contract.findFunctionBySelector? selector

def Contract.call? (fuel : Nat) (contract : Contract)
    (target : CallTarget) (state : State) (args : List Value) :
    Option CallResult :=
  match contract.findFunction? target with
  | some function =>
      function.call? fuel contract.context state args
  | none => none

def uint256 (name : String) : BindingDecl :=
  { name, ty := Ty.uint256 }

def bytesCalldata (name : String) : BindingDecl :=
  { name, ty := Ty.bytesCalldata }

def fixedWordArray (size : Nat) : Ty :=
  Ty.fixedArray size Ty.uint256

def Expr.zero : Expr :=
  Expr.word 0

def Expr.one : Expr :=
  Expr.word 1

def Expr.add (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.add lhs rhs

def Expr.sub (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.sub lhs rhs

def Expr.mul (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.mul lhs rhs

def Expr.lt (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.lt lhs rhs

def Expr.eq (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.eq lhs rhs

def Expr.bitAnd (lhs rhs : Expr) : Expr :=
  Expr.binary BinaryOp.bitAnd lhs rhs

def Stmt.seq (stmts : List Stmt) : Stmt :=
  Stmt.block stmts

def compositionalControlExample : Stmt :=
  Stmt.block
    [ Stmt.varDecl Ty.uint256 "x" (some (Expr.word 0))
    , Stmt.whileLoop
        (Expr.lt (Expr.var "x") (Expr.word 4))
        (Stmt.block
          [ Stmt.ifElse
              (Expr.eq
                (Expr.bitAnd (Expr.var "x") (Expr.word 1))
                Expr.zero)
              (Stmt.assignOp (LValue.var "x") BinaryOp.add (Expr.word 2))
              (Stmt.assignOp (LValue.var "x") BinaryOp.add Expr.one)
          ])
    , Stmt.returnValues [Expr.var "x"]
    ]

def compositionalControlResult : Option Result :=
  Stmt.eval 20 Context.empty (Runtime.ofState State.empty)
    compositionalControlExample

end Source
end Solidity
end SolidCore

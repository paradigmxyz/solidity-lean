import SharedSemantics.Word
import SolidCoreYulCore.Evm

set_option maxHeartbeats 1000000

namespace SolidCoreYulCore

open SharedSemantics

namespace FullYul

abbrev Name := Nat
abbrev DataLabel := Nat

inductive SymbolicBytes where
  | empty
  | concrete : List Nat -> SymbolicBytes
  | literal : String -> SymbolicBytes
  | hexLiteral : String -> SymbolicBytes
  | memorySlice : Word -> Word -> SymbolicBytes
  | memorySnapshot : Nat -> Word -> Word -> SymbolicBytes
  | calldataSlice : Word -> Word -> SymbolicBytes
  | returndataSlice : Word -> Word -> SymbolicBytes
  | returndataSnapshot : Nat -> Word -> Word -> SymbolicBytes
  | codeSlice : Word -> Word -> SymbolicBytes
  | extcodeSlice : Word -> Word -> Word -> SymbolicBytes
  | objectData : DataLabel -> Word -> SymbolicBytes
  | callReturnData : Nat -> SymbolicBytes
  | concat : SymbolicBytes -> SymbolicBytes -> SymbolicBytes
  deriving DecidableEq, Repr

inductive Value where
  | word : Word -> Value
  | symbolicHash : SymbolicBytes -> Value
  | dataOffset : DataLabel -> Value
  | memoryWord : Word -> Value
  | memoryWordAt : Nat -> Word -> Value
  | calldataWord : Word -> Value
  | returndataWord : Word -> Value
  | returndataWordAt : Nat -> Word -> Value
  | storageWord : Word -> Value -> Value
  | transientWord : Word -> Value -> Value
  | callSuccess : Nat -> Value
  | unaryBuiltin : Evm.Builtin -> Value -> Value
  | binaryBuiltin : Evm.Builtin -> Value -> Value -> Value
  | ternaryBuiltin : Evm.Builtin -> Value -> Value -> Value -> Value
  deriving DecidableEq, Repr

def symbolicKeccak (bytes : SymbolicBytes) : Value :=
  Value.symbolicHash bytes

def symbolicDataSize : SymbolicBytes -> Word
  | SymbolicBytes.empty => 0
  | SymbolicBytes.concrete bytes => norm bytes.length
  | SymbolicBytes.literal _ => 32
  | SymbolicBytes.hexLiteral _ => 32
  | SymbolicBytes.memorySlice _ size => size
  | SymbolicBytes.memorySnapshot _ _ size => size
  | SymbolicBytes.calldataSlice _ size => size
  | SymbolicBytes.returndataSlice _ size => size
  | SymbolicBytes.returndataSnapshot _ _ size => size
  | SymbolicBytes.codeSlice _ size => size
  | SymbolicBytes.extcodeSlice _ _ size => size
  | SymbolicBytes.objectData _ size => size
  | SymbolicBytes.callReturnData _ => 32
  | SymbolicBytes.concat lhs rhs =>
      addWord (symbolicDataSize lhs) (symbolicDataSize rhs)

theorem symbolicKeccak_term_injective {lhs rhs : SymbolicBytes} :
    symbolicKeccak lhs = symbolicKeccak rhs -> lhs = rhs := by
  intro h
  cases h
  rfl

theorem symbolicKeccak_distinguishes_literal_terms {lhs rhs : String}
    (h : lhs ≠ rhs) :
    symbolicKeccak (SymbolicBytes.literal lhs) ≠
      symbolicKeccak (SymbolicBytes.literal rhs) := by
  intro hHash
  have hBytes := symbolicKeccak_term_injective hHash
  cases hBytes
  exact h rfl

theorem symbolicDataSize_concat (lhs rhs : SymbolicBytes) :
    symbolicDataSize (SymbolicBytes.concat lhs rhs) =
      addWord (symbolicDataSize lhs) (symbolicDataSize rhs) := by
  rfl

theorem symbolicDataSize_concrete (bytes : List Nat) :
    symbolicDataSize (SymbolicBytes.concrete bytes) = norm bytes.length := by
  rfl

theorem symbolicDataSize_objectData (label size : Word) :
    symbolicDataSize (SymbolicBytes.objectData label size) = size := by
  rfl

abbrev Env := List (Name × Value)

def lookup? : Env -> Name -> Option Value
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate = name then some value else lookup? rest name

def declare? (env : Env) (name : Name) (value : Value) : Option Env :=
  match lookup? env name with
  | some _ => none
  | none => some ((name, value) :: env)

def assign? : Env -> Name -> Value -> Option Env
  | [], _, _ => none
  | (candidate, current) :: rest, name, value =>
      if candidate = name then
        some ((candidate, value) :: rest)
      else
        match assign? rest name value with
        | some rest' => some ((candidate, current) :: rest')
        | none => none

def restoreOuter : Env -> Env -> Option Env
  | [], _ => some []
  | (name, _) :: rest, inner =>
      match lookup? inner name, restoreOuter rest inner with
      | some value, some rest' => some ((name, value) :: rest')
      | _, _ => none

theorem lookup_declared_head (name : Name) (value : Value) (env : Env) :
    lookup? ((name, value) :: env) name = some value := by
  simp [lookup?]

theorem declare_rejects_visible (name : Name) (current value : Value)
    (env : Env) :
    declare? ((name, current) :: env) name value = none := by
  simp [declare?, lookup?]

theorem declare_fresh_head (name : Name) (value : Value) (env : Env)
    (h : lookup? env name = none) :
    declare? env name value = some ((name, value) :: env) := by
  simp [declare?, h]

theorem assign_updates_head (name : Name) (oldValue newValue : Value)
    (env : Env) :
    assign? ((name, oldValue) :: env) name newValue =
      some ((name, newValue) :: env) := by
  simp [assign?]

theorem assign_updates_outer_under_local (outerName localName : Name)
    (oldOuter newOuter localValue : Value) (h : localName ≠ outerName) :
    assign? [(localName, localValue), (outerName, oldOuter)]
        outerName newOuter =
      some [(localName, localValue), (outerName, newOuter)] := by
  simp [assign?, h]

theorem restoreOuter_drops_local (outerName localName : Name)
    (outerValue localValue : Value) (h : localName ≠ outerName) :
    restoreOuter [(outerName, outerValue)]
        [(localName, localValue), (outerName, outerValue)] =
      some [(outerName, outerValue)] := by
  simp [restoreOuter, lookup?, h]

theorem restoreOuter_keeps_updated_outer (outerName localName : Name)
    (oldOuter newOuter localValue : Value) (h : localName ≠ outerName) :
    restoreOuter [(outerName, oldOuter)]
        [(localName, localValue), (outerName, newOuter)] =
      some [(outerName, newOuter)] := by
  simp [restoreOuter, lookup?, h]

theorem restoreOuter_preserves_outer_lookup
    {outer inner restored : Env} {name : Name} {outerValue : Value}
    (hRestore : restoreOuter outer inner = some restored)
    (hOuter : lookup? outer name = some outerValue) :
    lookup? restored name = lookup? inner name := by
  induction outer generalizing restored with
  | nil =>
      simp [lookup?] at hOuter
  | cons binding rest ih =>
      cases binding with
      | mk currentName currentValue =>
          by_cases hName : currentName = name
          · subst currentName
            simp [lookup?] at hOuter
            cases hInner : lookup? inner name with
            | none =>
                simp [restoreOuter, hInner] at hRestore
            | some innerValue =>
                cases hRest : restoreOuter rest inner with
                | none =>
                    simp [restoreOuter, hInner, hRest] at hRestore
                | some restoredRest =>
                    simp [restoreOuter, hInner, hRest] at hRestore
                    cases hRestore
                    simp [lookup?]
          · simp [lookup?, hName] at hOuter
            cases hInner : lookup? inner currentName with
            | none =>
                simp [restoreOuter, hInner] at hRestore
            | some innerValue =>
                cases hRest : restoreOuter rest inner with
                | none =>
                    simp [restoreOuter, hInner, hRest] at hRestore
                | some restoredRest =>
                    simp [restoreOuter, hInner, hRest] at hRestore
                    cases hRestore
                    simp [lookup?, hName]
                    exact ih hRest hOuter

theorem restoreOuter_drops_name_not_in_outer
    {outer inner restored : Env} {name : Name}
    (hRestore : restoreOuter outer inner = some restored)
    (hOuter : lookup? outer name = none) :
    lookup? restored name = none := by
  induction outer generalizing restored with
  | nil =>
      simp [restoreOuter] at hRestore
      cases hRestore
      simp [lookup?]
  | cons binding rest ih =>
      cases binding with
      | mk currentName currentValue =>
          have hName : currentName ≠ name := by
            intro hEq
            subst currentName
            simp [lookup?] at hOuter
          have hRestOuter : lookup? rest name = none := by
            simpa [lookup?, hName] using hOuter
          cases hInner : lookup? inner currentName with
          | none =>
              simp [restoreOuter, hInner] at hRestore
          | some innerValue =>
              cases hRest : restoreOuter rest inner with
              | none =>
                  simp [restoreOuter, hInner, hRest] at hRestore
              | some restoredRest =>
                  simp [restoreOuter, hInner, hRest] at hRestore
                  cases hRestore
                  simp [lookup?, hName, ih hRest hRestOuter]

inductive Expr where
  | value : Value -> Expr
  | var : Name -> Expr
  | keccak : SymbolicBytes -> Expr
  | dataSize : DataLabel -> Expr
  | dataOffset : DataLabel -> Expr
  | builtin : Evm.Builtin -> List Expr -> Expr
  deriving Repr

def evalExpr (env : Env) : Expr -> Option Value
  | Expr.value value => some value
  | Expr.var name => lookup? env name
  | Expr.keccak bytes => some (symbolicKeccak bytes)
  | Expr.dataSize _ => none
  | Expr.dataOffset _ => none
  | Expr.builtin _ _ => none

def evalExprs (env : Env) : List Expr -> Option (List Value)
  | [] => some []
  | expr :: rest =>
      match evalExprs env rest, evalExpr env expr with
      | some values, some value => some (value :: values)
      | _, _ => none

def declareMany? : Env -> List Name -> List Value -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values =>
      match declare? env name value with
      | some env' => declareMany? env' names values
      | none => none
  | _, _, _ => none

def assignMany? : Env -> List Name -> List Value -> Option Env
  | env, [], [] => some env
  | env, name :: names, value :: values =>
      match assign? env name value with
      | some env' => assignMany? env' names values
      | none => none
  | _, _, _ => none

def valueAsBool : Value -> Option Bool
  | Value.word value =>
      if norm value = 0 then some false else some true
  | Value.symbolicHash _ => none
  | Value.dataOffset _ => none
  | Value.memoryWord _ => none
  | Value.memoryWordAt _ _ => none
  | Value.calldataWord _ => none
  | Value.returndataWord _ => none
  | Value.returndataWordAt _ _ => none
  | Value.storageWord _ _ => none
  | Value.transientWord _ _ => none
  | Value.callSuccess _ => none
  | Value.unaryBuiltin _ _ => none
  | Value.binaryBuiltin _ _ _ => none
  | Value.ternaryBuiltin _ _ _ _ => none

inductive Stmt where
  | skip
  | expr : Expr -> Stmt
  | let1 : Name -> Option Expr -> Stmt
  | letMany : List Name -> Option (List Expr) -> Stmt
  | funDef : Name -> List Name -> List Name -> Stmt -> Stmt
  | assign : Name -> Expr -> Stmt
  | assignMany : List Name -> List Expr -> Stmt
  | letCall : List Name -> Name -> List Expr -> Stmt
  | assignCall : List Name -> Name -> List Expr -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | block : List Stmt -> Stmt
  | ifThen : Expr -> Stmt -> Stmt
  | switch : Expr -> List (Value × Stmt) -> Option Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break
  | continue
  | leave
  deriving Repr

structure CompilerProfile where
  valueOK : Value -> Prop
  builtinOK : Evm.Builtin -> Prop
  builtinOK_signature :
    ∀ {builtin : Evm.Builtin}, builtinOK builtin ->
      ∃ sig, builtin.signature? = some sig
  allowSymbolicKeccakExpr : Prop
  allowDataRefs : Prop
  allowFunctionDefs : Prop
  allowFunctionCalls : Prop
  allowSwitch : Prop

namespace CompilerProfile

structure Le (source target : CompilerProfile) : Prop where
  valueOK :
    ∀ {value : Value}, source.valueOK value -> target.valueOK value
  builtinOK :
    ∀ {builtin : Evm.Builtin}, source.builtinOK builtin ->
      target.builtinOK builtin
  symbolicKeccak :
    source.allowSymbolicKeccakExpr -> target.allowSymbolicKeccakExpr
  dataRefs : source.allowDataRefs -> target.allowDataRefs
  functionDefs : source.allowFunctionDefs -> target.allowFunctionDefs
  functionCalls : source.allowFunctionCalls -> target.allowFunctionCalls
  switch : source.allowSwitch -> target.allowSwitch

theorem Le.refl (profile : CompilerProfile) : Le profile profile where
  valueOK h := h
  builtinOK h := h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem Le.trans {first second third : CompilerProfile}
    (hFirst : Le first second) (hSecond : Le second third) :
    Le first third where
  valueOK h := hSecond.valueOK (hFirst.valueOK h)
  builtinOK h := hSecond.builtinOK (hFirst.builtinOK h)
  symbolicKeccak h := hSecond.symbolicKeccak (hFirst.symbolicKeccak h)
  dataRefs h := hSecond.dataRefs (hFirst.dataRefs h)
  functionDefs h := hSecond.functionDefs (hFirst.functionDefs h)
  functionCalls h := hSecond.functionCalls (hFirst.functionCalls h)
  switch h := hSecond.switch (hFirst.switch h)

inductive CurrentSolidCoreValue : Value -> Prop where
  | word (value : Word) : CurrentSolidCoreValue (Value.word value)

inductive CurrentSolidCoreBuiltin : Evm.Builtin -> Prop where
  | add : CurrentSolidCoreBuiltin Evm.Builtin.add
  | addmodOp : CurrentSolidCoreBuiltin Evm.Builtin.addmodOp
  | andOp : CurrentSolidCoreBuiltin Evm.Builtin.andOp
  | byteOp : CurrentSolidCoreBuiltin Evm.Builtin.byteOp
  | clzOp : CurrentSolidCoreBuiltin Evm.Builtin.clzOp
  | divOp : CurrentSolidCoreBuiltin Evm.Builtin.divOp
  | eqOp : CurrentSolidCoreBuiltin Evm.Builtin.eqOp
  | expOp : CurrentSolidCoreBuiltin Evm.Builtin.expOp
  | gtOp : CurrentSolidCoreBuiltin Evm.Builtin.gtOp
  | iszero : CurrentSolidCoreBuiltin Evm.Builtin.iszero
  | ltOp : CurrentSolidCoreBuiltin Evm.Builtin.ltOp
  | modOp : CurrentSolidCoreBuiltin Evm.Builtin.modOp
  | mul : CurrentSolidCoreBuiltin Evm.Builtin.mul
  | mulmodOp : CurrentSolidCoreBuiltin Evm.Builtin.mulmodOp
  | notOp : CurrentSolidCoreBuiltin Evm.Builtin.notOp
  | orOp : CurrentSolidCoreBuiltin Evm.Builtin.orOp
  | popOp : CurrentSolidCoreBuiltin Evm.Builtin.popOp
  | revertOp : CurrentSolidCoreBuiltin Evm.Builtin.revertOp
  | returnOp : CurrentSolidCoreBuiltin Evm.Builtin.returnOp
  | sarOp : CurrentSolidCoreBuiltin Evm.Builtin.sarOp
  | sdivOp : CurrentSolidCoreBuiltin Evm.Builtin.sdivOp
  | sgtOp : CurrentSolidCoreBuiltin Evm.Builtin.sgtOp
  | signextendOp : CurrentSolidCoreBuiltin Evm.Builtin.signextendOp
  | shlOp : CurrentSolidCoreBuiltin Evm.Builtin.shlOp
  | shrOp : CurrentSolidCoreBuiltin Evm.Builtin.shrOp
  | sload : CurrentSolidCoreBuiltin Evm.Builtin.sload
  | sltOp : CurrentSolidCoreBuiltin Evm.Builtin.sltOp
  | smodOp : CurrentSolidCoreBuiltin Evm.Builtin.smodOp
  | stopOp : CurrentSolidCoreBuiltin Evm.Builtin.stopOp
  | sstore : CurrentSolidCoreBuiltin Evm.Builtin.sstore
  | sub : CurrentSolidCoreBuiltin Evm.Builtin.sub
  | invalidOp : CurrentSolidCoreBuiltin Evm.Builtin.invalidOp
  | xorOp : CurrentSolidCoreBuiltin Evm.Builtin.xorOp

theorem CurrentSolidCoreBuiltin.signature {builtin : Evm.Builtin}
    (h : CurrentSolidCoreBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem CurrentSolidCoreBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : CurrentSolidCoreBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem CurrentSolidCoreBuiltin.semanticCoverage_exact_lane
    {builtin : Evm.Builtin} (h : CurrentSolidCoreBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive MemoryBuiltin : Evm.Builtin -> Prop where
  | mload : MemoryBuiltin Evm.Builtin.mload
  | mstore : MemoryBuiltin Evm.Builtin.mstore
  | mstore8 : MemoryBuiltin Evm.Builtin.mstore8

theorem MemoryBuiltin.signature {builtin : Evm.Builtin}
    (h : MemoryBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem MemoryBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : MemoryBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem MemoryBuiltin.semanticCoverage_memory_lane
    {builtin : Evm.Builtin} (h : MemoryBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryWrite := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive MemoryCopyBuiltin : Evm.Builtin -> Prop where
  | mcopyOp : MemoryCopyBuiltin Evm.Builtin.mcopyOp

theorem MemoryCopyBuiltin.signature {builtin : Evm.Builtin}
    (h : MemoryCopyBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem MemoryCopyBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : MemoryCopyBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem MemoryCopyBuiltin.semanticCoverage_memoryCopy
    {builtin : Evm.Builtin} (h : MemoryCopyBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive BufferBuiltin : Evm.Builtin -> Prop where
  | calldataloadOp : BufferBuiltin Evm.Builtin.calldataloadOp
  | calldatasizeOp : BufferBuiltin Evm.Builtin.calldatasizeOp
  | calldatacopyOp : BufferBuiltin Evm.Builtin.calldatacopyOp

theorem BufferBuiltin.signature {builtin : Evm.Builtin}
    (h : BufferBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem BufferBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : BufferBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem BufferBuiltin.semanticCoverage_buffer_lane
    {builtin : Evm.Builtin} (h : BufferBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive ReturnDataBuiltin : Evm.Builtin -> Prop where
  | returndataloadOp : ReturnDataBuiltin Evm.Builtin.returndataloadOp
  | returndatasizeOp : ReturnDataBuiltin Evm.Builtin.returndatasizeOp
  | returndatacopyOp : ReturnDataBuiltin Evm.Builtin.returndatacopyOp

theorem ReturnDataBuiltin.signature {builtin : Evm.Builtin}
    (h : ReturnDataBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem ReturnDataBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : ReturnDataBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem ReturnDataBuiltin.semanticCoverage_buffer_lane
    {builtin : Evm.Builtin} (h : ReturnDataBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive CodeBuiltin : Evm.Builtin -> Prop where
  | codecopyOp : CodeBuiltin Evm.Builtin.codecopyOp
  | codesizeOp : CodeBuiltin Evm.Builtin.codesizeOp

theorem CodeBuiltin.signature {builtin : Evm.Builtin}
    (h : CodeBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem CodeBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : CodeBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem CodeBuiltin.semanticCoverage_buffer_lane
    {builtin : Evm.Builtin} (h : CodeBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive MemoryHashBuiltin : Evm.Builtin -> Prop where
  | keccak256Op : MemoryHashBuiltin Evm.Builtin.keccak256Op

theorem MemoryHashBuiltin.signature {builtin : Evm.Builtin}
    (h : MemoryHashBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem MemoryHashBuiltin.claim_symbolic {builtin : Evm.Builtin}
    (h : MemoryHashBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.symbolic := by
  cases h <;> rfl

theorem MemoryHashBuiltin.semanticCoverage_memoryHash
    {builtin : Evm.Builtin} (h : MemoryHashBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryHash := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive ObjectDataBuiltin : Evm.Builtin -> Prop where
  | datacopyOp : ObjectDataBuiltin Evm.Builtin.datacopyOp

theorem ObjectDataBuiltin.signature {builtin : Evm.Builtin}
    (h : ObjectDataBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem ObjectDataBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : ObjectDataBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem ObjectDataBuiltin.semanticCoverage_objectDataCopy
    {builtin : Evm.Builtin} (h : ObjectDataBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.objectDataCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive ContextWordBuiltin : Evm.Builtin -> Prop where
  | addressOp : ContextWordBuiltin Evm.Builtin.addressOp
  | originOp : ContextWordBuiltin Evm.Builtin.originOp
  | callerOp : ContextWordBuiltin Evm.Builtin.callerOp
  | callvalueOp : ContextWordBuiltin Evm.Builtin.callvalueOp
  | gaspriceOp : ContextWordBuiltin Evm.Builtin.gaspriceOp
  | coinbaseOp : ContextWordBuiltin Evm.Builtin.coinbaseOp
  | timestampOp : ContextWordBuiltin Evm.Builtin.timestampOp
  | numberOp : ContextWordBuiltin Evm.Builtin.numberOp
  | difficultyOp : ContextWordBuiltin Evm.Builtin.difficultyOp
  | prevrandaoOp : ContextWordBuiltin Evm.Builtin.prevrandaoOp
  | gaslimitOp : ContextWordBuiltin Evm.Builtin.gaslimitOp
  | chainidOp : ContextWordBuiltin Evm.Builtin.chainidOp
  | selfbalanceOp : ContextWordBuiltin Evm.Builtin.selfbalanceOp
  | basefeeOp : ContextWordBuiltin Evm.Builtin.basefeeOp
  | msizeOp : ContextWordBuiltin Evm.Builtin.msizeOp
  | blobbasefeeOp : ContextWordBuiltin Evm.Builtin.blobbasefeeOp

theorem ContextWordBuiltin.signature {builtin : Evm.Builtin}
    (h : ContextWordBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem ContextWordBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : ContextWordBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem ContextWordBuiltin.semanticCoverage_contextWord
    {builtin : Evm.Builtin} (h : ContextWordBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.contextWord := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive CompilerAnnotationBuiltin : Evm.Builtin -> Prop where
  | memoryguardOp : CompilerAnnotationBuiltin Evm.Builtin.memoryguardOp

theorem CompilerAnnotationBuiltin.signature {builtin : Evm.Builtin}
    (h : CompilerAnnotationBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem CompilerAnnotationBuiltin.claim_abstracted {builtin : Evm.Builtin}
    (h : CompilerAnnotationBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h <;> rfl

theorem CompilerAnnotationBuiltin.semanticCoverage_compilerBuiltin
    {builtin : Evm.Builtin} (h : CompilerAnnotationBuiltin builtin) :
    builtin.semanticCoverage? =
      some Evm.SemanticCoverage.compilerBuiltin := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive CompilerArtifactBuiltin : Evm.Builtin -> Prop where
  | setimmutableOp : CompilerArtifactBuiltin Evm.Builtin.setimmutableOp
  | loadimmutableOp : CompilerArtifactBuiltin Evm.Builtin.loadimmutableOp
  | linkersymbolOp : CompilerArtifactBuiltin Evm.Builtin.linkersymbolOp

theorem CompilerArtifactBuiltin.signature {builtin : Evm.Builtin}
    (h : CompilerArtifactBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem CompilerArtifactBuiltin.claim_abstracted {builtin : Evm.Builtin}
    (h : CompilerArtifactBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h <;> rfl

theorem CompilerArtifactBuiltin.semanticCoverage_compilerBuiltin
    {builtin : Evm.Builtin} (h : CompilerArtifactBuiltin builtin) :
    builtin.semanticCoverage? =
      some Evm.SemanticCoverage.compilerBuiltin := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive VerbatimBuiltin : Evm.Builtin -> Prop where
  | verbatimOp (inputs outputs : Nat) :
      VerbatimBuiltin (Evm.Builtin.verbatimOp inputs outputs)

theorem VerbatimBuiltin.signature {builtin : Evm.Builtin}
    (h : VerbatimBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h
  simp [Evm.Builtin.signature?]

theorem VerbatimBuiltin.claim_abstracted {builtin : Evm.Builtin}
    (h : VerbatimBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h
  rfl

theorem VerbatimBuiltin.semanticCoverage_verbatim
    {builtin : Evm.Builtin} (h : VerbatimBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.verbatim := by
  cases h
  rfl

inductive LoweringEnvironmentBuiltin : Evm.Builtin -> Prop where
  | gasOp : LoweringEnvironmentBuiltin Evm.Builtin.gasOp
  | pcOp : LoweringEnvironmentBuiltin Evm.Builtin.pcOp

theorem LoweringEnvironmentBuiltin.signature {builtin : Evm.Builtin}
    (h : LoweringEnvironmentBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem LoweringEnvironmentBuiltin.claim_deferred {builtin : Evm.Builtin}
    (h : LoweringEnvironmentBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.deferredToLowering := by
  cases h <;> rfl

theorem LoweringEnvironmentBuiltin.semanticCoverage_loweringEnvironment
    {builtin : Evm.Builtin} (h : LoweringEnvironmentBuiltin builtin) :
    builtin.semanticCoverage? =
      some Evm.SemanticCoverage.loweringEnvironment := by
  cases h <;> rfl

inductive ExternalCallBuiltin : Evm.Builtin -> Prop where
  | callOp : ExternalCallBuiltin Evm.Builtin.callOp
  | callcodeOp : ExternalCallBuiltin Evm.Builtin.callcodeOp
  | delegatecallOp : ExternalCallBuiltin Evm.Builtin.delegatecallOp
  | staticcallOp : ExternalCallBuiltin Evm.Builtin.staticcallOp
  | log0Op : ExternalCallBuiltin Evm.Builtin.log0Op
  | log1Op : ExternalCallBuiltin Evm.Builtin.log1Op
  | log2Op : ExternalCallBuiltin Evm.Builtin.log2Op
  | log3Op : ExternalCallBuiltin Evm.Builtin.log3Op
  | log4Op : ExternalCallBuiltin Evm.Builtin.log4Op
  | createOp : ExternalCallBuiltin Evm.Builtin.createOp
  | create2Op : ExternalCallBuiltin Evm.Builtin.create2Op
  | selfdestructOp : ExternalCallBuiltin Evm.Builtin.selfdestructOp

theorem ExternalCallBuiltin.signature {builtin : Evm.Builtin}
    (h : ExternalCallBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem ExternalCallBuiltin.claim_abstracted {builtin : Evm.Builtin}
    (h : ExternalCallBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h <;> rfl

theorem ExternalCallBuiltin.semanticCoverage_hostEffect
    {builtin : Evm.Builtin} (h : ExternalCallBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.externalCall ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.log ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.contractCreation ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.selfdestruct := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive TransientStorageBuiltin : Evm.Builtin -> Prop where
  | tloadOp : TransientStorageBuiltin Evm.Builtin.tloadOp
  | tstoreOp : TransientStorageBuiltin Evm.Builtin.tstoreOp

theorem TransientStorageBuiltin.signature {builtin : Evm.Builtin}
    (h : TransientStorageBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem TransientStorageBuiltin.claim_exactYul {builtin : Evm.Builtin}
    (h : TransientStorageBuiltin builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h <;> rfl

theorem TransientStorageBuiltin.semanticCoverage_transientStorage
    {builtin : Evm.Builtin} (h : TransientStorageBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.transientStorage := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

inductive ExternalQueryBuiltin : Evm.Builtin -> Prop where
  | blockhashOp : ExternalQueryBuiltin Evm.Builtin.blockhashOp
  | balanceOp : ExternalQueryBuiltin Evm.Builtin.balanceOp
  | extcodesizeOp : ExternalQueryBuiltin Evm.Builtin.extcodesizeOp
  | extcodehashOp : ExternalQueryBuiltin Evm.Builtin.extcodehashOp
  | extcodecopyOp : ExternalQueryBuiltin Evm.Builtin.extcodecopyOp
  | blobhashOp : ExternalQueryBuiltin Evm.Builtin.blobhashOp

theorem ExternalQueryBuiltin.signature {builtin : Evm.Builtin}
    (h : ExternalQueryBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig := by
  cases h <;> simp [Evm.Builtin.signature?]

theorem ExternalQueryBuiltin.semanticCoverage_externalQuery
    {builtin : Evm.Builtin} (h : ExternalQueryBuiltin builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.externalQuery ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h <;> simp [Evm.Builtin.semanticCoverage?]

theorem ExternalCallBuiltin.iff {builtin : Evm.Builtin} :
    ExternalCallBuiltin builtin ↔
      builtin = Evm.Builtin.callOp ∨
      builtin = Evm.Builtin.callcodeOp ∨
      builtin = Evm.Builtin.delegatecallOp ∨
      builtin = Evm.Builtin.staticcallOp ∨
      builtin = Evm.Builtin.log0Op ∨
      builtin = Evm.Builtin.log1Op ∨
      builtin = Evm.Builtin.log2Op ∨
      builtin = Evm.Builtin.log3Op ∨
      builtin = Evm.Builtin.log4Op ∨
      builtin = Evm.Builtin.createOp ∨
      builtin = Evm.Builtin.create2Op ∨
      builtin = Evm.Builtin.selfdestructOp := by
  constructor
  · intro h
    cases h <;> simp
  · intro h
    rcases h with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ExternalCallBuiltin.callOp
    · exact ExternalCallBuiltin.callcodeOp
    · exact ExternalCallBuiltin.delegatecallOp
    · exact ExternalCallBuiltin.staticcallOp
    · exact ExternalCallBuiltin.log0Op
    · exact ExternalCallBuiltin.log1Op
    · exact ExternalCallBuiltin.log2Op
    · exact ExternalCallBuiltin.log3Op
    · exact ExternalCallBuiltin.log4Op
    · exact ExternalCallBuiltin.createOp
    · exact ExternalCallBuiltin.create2Op
    · exact ExternalCallBuiltin.selfdestructOp

def currentSolidCore : CompilerProfile where
  valueOK := CurrentSolidCoreValue
  builtinOK := CurrentSolidCoreBuiltin
  builtinOK_signature := CurrentSolidCoreBuiltin.signature
  allowSymbolicKeccakExpr := False
  allowDataRefs := False
  allowFunctionDefs := True
  allowFunctionCalls := True
  allowSwitch := True

theorem currentSolidCore_allowSwitch :
    currentSolidCore.allowSwitch := by
  trivial

theorem currentSolidCore_allowFunctionDefs :
    currentSolidCore.allowFunctionDefs := by
  trivial

theorem currentSolidCore_allowFunctionCalls :
    currentSolidCore.allowFunctionCalls := by
  trivial

def withMemoryBuiltins (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ MemoryBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact MemoryBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withMemoryCopyBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ MemoryCopyBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact MemoryCopyBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withBufferBuiltins (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ BufferBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact BufferBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withReturnDataBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ ReturnDataBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact ReturnDataBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withCodeBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ CodeBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact CodeBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withMemoryHashBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ MemoryHashBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact MemoryHashBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withObjectDataBuiltins (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ ObjectDataBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact ObjectDataBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := True
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withContextBuiltins (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ ContextWordBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact ContextWordBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withCompilerAnnotations (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ CompilerAnnotationBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact CompilerAnnotationBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withCompilerArtifactBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ CompilerArtifactBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact CompilerArtifactBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withVerbatimBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ VerbatimBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact VerbatimBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withLoweringEnvironmentBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ LoweringEnvironmentBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact LoweringEnvironmentBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withExternalCalls (profile : CompilerProfile) : CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ ExternalCallBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact ExternalCallBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withExternalQueryBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ ExternalQueryBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact ExternalQueryBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def withTransientStorageBuiltins (profile : CompilerProfile) :
    CompilerProfile where
  valueOK := profile.valueOK
  builtinOK := fun builtin =>
    profile.builtinOK builtin ∨ TransientStorageBuiltin builtin
  builtinOK_signature := by
    intro builtin h
    cases h with
    | inl hBuiltin => exact profile.builtinOK_signature hBuiltin
    | inr hBuiltin => exact TransientStorageBuiltin.signature hBuiltin
  allowSymbolicKeccakExpr := profile.allowSymbolicKeccakExpr
  allowDataRefs := profile.allowDataRefs
  allowFunctionDefs := profile.allowFunctionDefs
  allowFunctionCalls := profile.allowFunctionCalls
  allowSwitch := profile.allowSwitch

def currentSolidityEmittableNoExternalCallsNoVerbatim :
    CompilerProfile :=
  currentSolidCore
    |>.withMemoryBuiltins
    |>.withMemoryCopyBuiltins
    |>.withMemoryHashBuiltins
    |>.withBufferBuiltins
    |>.withReturnDataBuiltins
    |>.withCodeBuiltins
    |>.withObjectDataBuiltins
    |>.withContextBuiltins
    |>.withExternalQueryBuiltins
    |>.withTransientStorageBuiltins
    |>.withCompilerAnnotations
    |>.withCompilerArtifactBuiltins

def currentSolidityEmittableNoVerbatim : CompilerProfile :=
  currentSolidityEmittableNoExternalCallsNoVerbatim
    |>.withExternalCalls

abbrev currentSolidityEmittable : CompilerProfile :=
  currentSolidityEmittableNoVerbatim

def currentSolidityEmittableWithVerbatim : CompilerProfile :=
  currentSolidityEmittableNoVerbatim
    |>.withVerbatimBuiltins

def currentSolidityEmittableWithLoweringEnvironment :
    CompilerProfile :=
  currentSolidityEmittableNoVerbatim
    |>.withLoweringEnvironmentBuiltins

theorem currentSolidityEmittable_allowSwitch :
    currentSolidityEmittable.allowSwitch := by
  simpa [currentSolidityEmittable, currentSolidityEmittableNoVerbatim,
    currentSolidityEmittableNoExternalCallsNoVerbatim,
    withExternalCalls, withCompilerArtifactBuiltins,
    withCompilerAnnotations, withTransientStorageBuiltins,
    withExternalQueryBuiltins, withContextBuiltins,
    withObjectDataBuiltins, withCodeBuiltins, withReturnDataBuiltins,
    withBufferBuiltins, withMemoryHashBuiltins, withMemoryCopyBuiltins,
    withMemoryBuiltins] using currentSolidCore_allowSwitch

theorem currentSolidityEmittable_allowDataRefs :
    currentSolidityEmittable.allowDataRefs := by
  simp [currentSolidityEmittable, currentSolidityEmittableNoVerbatim,
    currentSolidityEmittableNoExternalCallsNoVerbatim,
    withExternalCalls, withCompilerArtifactBuiltins,
    withCompilerAnnotations, withTransientStorageBuiltins,
    withExternalQueryBuiltins, withContextBuiltins,
    withObjectDataBuiltins, withCodeBuiltins, withReturnDataBuiltins,
    withBufferBuiltins, withMemoryHashBuiltins, withMemoryCopyBuiltins,
    withMemoryBuiltins]

theorem currentSolidityEmittable_allowFunctionDefs :
    currentSolidityEmittable.allowFunctionDefs := by
  simpa [currentSolidityEmittable, currentSolidityEmittableNoVerbatim,
    currentSolidityEmittableNoExternalCallsNoVerbatim,
    withExternalCalls, withCompilerArtifactBuiltins,
    withCompilerAnnotations, withTransientStorageBuiltins,
    withExternalQueryBuiltins, withContextBuiltins,
    withObjectDataBuiltins, withCodeBuiltins, withReturnDataBuiltins,
    withBufferBuiltins, withMemoryHashBuiltins, withMemoryCopyBuiltins,
    withMemoryBuiltins] using currentSolidCore_allowFunctionDefs

theorem currentSolidityEmittable_allowFunctionCalls :
    currentSolidityEmittable.allowFunctionCalls := by
  simpa [currentSolidityEmittable, currentSolidityEmittableNoVerbatim,
    currentSolidityEmittableNoExternalCallsNoVerbatim,
    withExternalCalls, withCompilerArtifactBuiltins,
    withCompilerAnnotations, withTransientStorageBuiltins,
    withExternalQueryBuiltins, withContextBuiltins,
    withObjectDataBuiltins, withCodeBuiltins, withReturnDataBuiltins,
    withBufferBuiltins, withMemoryHashBuiltins, withMemoryCopyBuiltins,
    withMemoryBuiltins] using currentSolidCore_allowFunctionCalls

def CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin
    (builtin : Evm.Builtin) : Prop :=
  (((((((((((CurrentSolidCoreBuiltin builtin ∨ MemoryBuiltin builtin) ∨
    MemoryCopyBuiltin builtin) ∨ MemoryHashBuiltin builtin) ∨
    BufferBuiltin builtin) ∨ ReturnDataBuiltin builtin) ∨
    CodeBuiltin builtin) ∨ ObjectDataBuiltin builtin) ∨
    ContextWordBuiltin builtin) ∨ ExternalQueryBuiltin builtin) ∨
    TransientStorageBuiltin builtin) ∨ CompilerAnnotationBuiltin builtin) ∨
    CompilerArtifactBuiltin builtin

def CurrentSolidityEmittableNoVerbatimBuiltin
    (builtin : Evm.Builtin) : Prop :=
  CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin builtin ∨
    ExternalCallBuiltin builtin

abbrev CurrentSolidityEmittableBuiltin (builtin : Evm.Builtin) : Prop :=
  CurrentSolidityEmittableNoVerbatimBuiltin builtin

theorem currentSolidityEmittableNoExternalCallsNoVerbatim_builtinOK_iff
    (builtin : Evm.Builtin) :
    currentSolidityEmittableNoExternalCallsNoVerbatim.builtinOK builtin ↔
      CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin builtin := by
  rfl

theorem currentSolidityEmittableNoVerbatim_builtinOK_iff
    (builtin : Evm.Builtin) :
    currentSolidityEmittableNoVerbatim.builtinOK builtin ↔
      CurrentSolidityEmittableNoVerbatimBuiltin builtin := by
  rfl

theorem currentSolidityEmittable_builtinOK_iff
    (builtin : Evm.Builtin) :
    currentSolidityEmittable.builtinOK builtin ↔
      CurrentSolidityEmittableBuiltin builtin := by
  rfl

@[simp] theorem withMemoryBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withMemoryBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ MemoryBuiltin builtin :=
  Iff.rfl

@[simp] theorem withMemoryCopyBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withMemoryCopyBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ MemoryCopyBuiltin builtin :=
  Iff.rfl

@[simp] theorem withBufferBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withBufferBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ BufferBuiltin builtin :=
  Iff.rfl

@[simp] theorem withReturnDataBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withReturnDataBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ ReturnDataBuiltin builtin :=
  Iff.rfl

@[simp] theorem withCodeBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withCodeBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ CodeBuiltin builtin :=
  Iff.rfl

@[simp] theorem withMemoryHashBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withMemoryHashBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ MemoryHashBuiltin builtin :=
  Iff.rfl

@[simp] theorem withObjectDataBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withObjectDataBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ ObjectDataBuiltin builtin :=
  Iff.rfl

@[simp] theorem withContextBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withContextBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ ContextWordBuiltin builtin :=
  Iff.rfl

@[simp] theorem withCompilerAnnotations_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withCompilerAnnotations.builtinOK builtin ↔
      profile.builtinOK builtin ∨ CompilerAnnotationBuiltin builtin :=
  Iff.rfl

@[simp] theorem withCompilerArtifactBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withCompilerArtifactBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ CompilerArtifactBuiltin builtin :=
  Iff.rfl

@[simp] theorem withVerbatimBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withVerbatimBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ VerbatimBuiltin builtin :=
  Iff.rfl

@[simp] theorem withLoweringEnvironmentBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withLoweringEnvironmentBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ LoweringEnvironmentBuiltin builtin :=
  Iff.rfl

@[simp] theorem withExternalCalls_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withExternalCalls.builtinOK builtin ↔
      profile.builtinOK builtin ∨ ExternalCallBuiltin builtin :=
  Iff.rfl

@[simp] theorem withExternalQueryBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withExternalQueryBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ ExternalQueryBuiltin builtin :=
  Iff.rfl

@[simp] theorem withTransientStorageBuiltins_builtinOK_iff
    (profile : CompilerProfile) (builtin : Evm.Builtin) :
    profile.withTransientStorageBuiltins.builtinOK builtin ↔
      profile.builtinOK builtin ∨ TransientStorageBuiltin builtin :=
  Iff.rfl

theorem le_withMemoryBuiltins (profile : CompilerProfile) :
    Le profile profile.withMemoryBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withMemoryCopyBuiltins (profile : CompilerProfile) :
    Le profile profile.withMemoryCopyBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withBufferBuiltins (profile : CompilerProfile) :
    Le profile profile.withBufferBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withReturnDataBuiltins (profile : CompilerProfile) :
    Le profile profile.withReturnDataBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withCodeBuiltins (profile : CompilerProfile) :
    Le profile profile.withCodeBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withMemoryHashBuiltins (profile : CompilerProfile) :
    Le profile profile.withMemoryHashBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withObjectDataBuiltins (profile : CompilerProfile) :
    Le profile profile.withObjectDataBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs _h := trivial
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withContextBuiltins (profile : CompilerProfile) :
    Le profile profile.withContextBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withCompilerAnnotations (profile : CompilerProfile) :
    Le profile profile.withCompilerAnnotations where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withCompilerArtifactBuiltins (profile : CompilerProfile) :
    Le profile profile.withCompilerArtifactBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withVerbatimBuiltins (profile : CompilerProfile) :
    Le profile profile.withVerbatimBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withLoweringEnvironmentBuiltins (profile : CompilerProfile) :
    Le profile profile.withLoweringEnvironmentBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withExternalCalls (profile : CompilerProfile) :
    Le profile profile.withExternalCalls where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withExternalQueryBuiltins (profile : CompilerProfile) :
    Le profile profile.withExternalQueryBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem le_withTransientStorageBuiltins (profile : CompilerProfile) :
    Le profile profile.withTransientStorageBuiltins where
  valueOK h := h
  builtinOK h := Or.inl h
  symbolicKeccak h := h
  dataRefs h := h
  functionDefs h := h
  functionCalls h := h
  switch h := h

theorem currentSolidCore_le_withExternalCalls :
    Le currentSolidCore currentSolidCore.withExternalCalls :=
  le_withExternalCalls currentSolidCore

theorem currentSolidCore_le_withMemoryBuiltins :
    Le currentSolidCore currentSolidCore.withMemoryBuiltins :=
  le_withMemoryBuiltins currentSolidCore

theorem currentSolidCore_le_withMemoryCopyBuiltins :
    Le currentSolidCore currentSolidCore.withMemoryCopyBuiltins :=
  le_withMemoryCopyBuiltins currentSolidCore

theorem currentSolidCore_le_withBufferBuiltins :
    Le currentSolidCore currentSolidCore.withBufferBuiltins :=
  le_withBufferBuiltins currentSolidCore

theorem currentSolidCore_le_withReturnDataBuiltins :
    Le currentSolidCore currentSolidCore.withReturnDataBuiltins :=
  le_withReturnDataBuiltins currentSolidCore

theorem currentSolidCore_le_withCodeBuiltins :
    Le currentSolidCore currentSolidCore.withCodeBuiltins :=
  le_withCodeBuiltins currentSolidCore

theorem currentSolidCore_le_withMemoryHashBuiltins :
    Le currentSolidCore currentSolidCore.withMemoryHashBuiltins :=
  le_withMemoryHashBuiltins currentSolidCore

theorem currentSolidCore_le_withObjectDataBuiltins :
    Le currentSolidCore currentSolidCore.withObjectDataBuiltins :=
  le_withObjectDataBuiltins currentSolidCore

theorem currentSolidCore_le_withContextBuiltins :
    Le currentSolidCore currentSolidCore.withContextBuiltins :=
  le_withContextBuiltins currentSolidCore

theorem currentSolidCore_le_withCompilerAnnotations :
    Le currentSolidCore currentSolidCore.withCompilerAnnotations :=
  le_withCompilerAnnotations currentSolidCore

theorem currentSolidCore_le_withCompilerArtifactBuiltins :
    Le currentSolidCore currentSolidCore.withCompilerArtifactBuiltins :=
  le_withCompilerArtifactBuiltins currentSolidCore

theorem currentSolidCore_le_withVerbatimBuiltins :
    Le currentSolidCore currentSolidCore.withVerbatimBuiltins :=
  le_withVerbatimBuiltins currentSolidCore

theorem currentSolidCore_le_withLoweringEnvironmentBuiltins :
    Le currentSolidCore
      currentSolidCore.withLoweringEnvironmentBuiltins :=
  le_withLoweringEnvironmentBuiltins currentSolidCore

theorem currentSolidCore_le_withExternalQueryBuiltins :
    Le currentSolidCore currentSolidCore.withExternalQueryBuiltins :=
  le_withExternalQueryBuiltins currentSolidCore

theorem currentSolidCore_le_withTransientStorageBuiltins :
    Le currentSolidCore currentSolidCore.withTransientStorageBuiltins :=
  le_withTransientStorageBuiltins currentSolidCore

theorem currentSolidCore_builtin_claim_exactYul {builtin : Evm.Builtin}
    (h : currentSolidCore.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul :=
  CurrentSolidCoreBuiltin.claim_exactYul h

theorem currentSolidCore_builtin_semanticCoverage_exact_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard :=
  CurrentSolidCoreBuiltin.semanticCoverage_exact_lane h

theorem withMemoryBuiltins_accepts_mstore (profile : CompilerProfile) :
    (profile.withMemoryBuiltins).builtinOK Evm.Builtin.mstore := by
  exact Or.inr MemoryBuiltin.mstore

theorem withMemoryBuiltins_accepts_mload (profile : CompilerProfile) :
    (profile.withMemoryBuiltins).builtinOK Evm.Builtin.mload := by
  exact Or.inr MemoryBuiltin.mload

theorem withMemoryBuiltins_accepts_mstore8 (profile : CompilerProfile) :
    (profile.withMemoryBuiltins).builtinOK Evm.Builtin.mstore8 := by
  exact Or.inr MemoryBuiltin.mstore8

theorem withMemoryCopyBuiltins_accepts_mcopyOp
    (profile : CompilerProfile) :
    (profile.withMemoryCopyBuiltins).builtinOK Evm.Builtin.mcopyOp := by
  exact Or.inr MemoryCopyBuiltin.mcopyOp

theorem withBufferBuiltins_accepts_calldatacopyOp
    (profile : CompilerProfile) :
    (profile.withBufferBuiltins).builtinOK
      Evm.Builtin.calldatacopyOp := by
  exact Or.inr BufferBuiltin.calldatacopyOp

theorem withBufferBuiltins_accepts_calldataloadOp
    (profile : CompilerProfile) :
    (profile.withBufferBuiltins).builtinOK
      Evm.Builtin.calldataloadOp := by
  exact Or.inr BufferBuiltin.calldataloadOp

theorem withReturnDataBuiltins_accepts_returndatacopyOp
    (profile : CompilerProfile) :
    (profile.withReturnDataBuiltins).builtinOK
      Evm.Builtin.returndatacopyOp := by
  exact Or.inr ReturnDataBuiltin.returndatacopyOp

theorem withReturnDataBuiltins_accepts_returndataloadOp
    (profile : CompilerProfile) :
    (profile.withReturnDataBuiltins).builtinOK
      Evm.Builtin.returndataloadOp := by
  exact Or.inr ReturnDataBuiltin.returndataloadOp

theorem withCodeBuiltins_accepts_codecopyOp
    (profile : CompilerProfile) :
    (profile.withCodeBuiltins).builtinOK
      Evm.Builtin.codecopyOp := by
  exact Or.inr CodeBuiltin.codecopyOp

theorem withCodeBuiltins_accepts_codesizeOp
    (profile : CompilerProfile) :
    (profile.withCodeBuiltins).builtinOK
      Evm.Builtin.codesizeOp := by
  exact Or.inr CodeBuiltin.codesizeOp

theorem withMemoryHashBuiltins_accepts_keccak256Op
    (profile : CompilerProfile) :
    (profile.withMemoryHashBuiltins).builtinOK
      Evm.Builtin.keccak256Op := by
  exact Or.inr MemoryHashBuiltin.keccak256Op

theorem withObjectDataBuiltins_accepts_datacopyOp
    (profile : CompilerProfile) :
    (profile.withObjectDataBuiltins).builtinOK
      Evm.Builtin.datacopyOp := by
  exact Or.inr ObjectDataBuiltin.datacopyOp

theorem withContextBuiltins_accepts_difficultyOp
    (profile : CompilerProfile) :
    (profile.withContextBuiltins).builtinOK
      Evm.Builtin.difficultyOp := by
  exact Or.inr ContextWordBuiltin.difficultyOp

theorem withContextBuiltins_accepts_prevrandaoOp
    (profile : CompilerProfile) :
    (profile.withContextBuiltins).builtinOK
      Evm.Builtin.prevrandaoOp := by
  exact Or.inr ContextWordBuiltin.prevrandaoOp

theorem withCompilerAnnotations_accepts_memoryguardOp
    (profile : CompilerProfile) :
    (profile.withCompilerAnnotations).builtinOK
      Evm.Builtin.memoryguardOp := by
  exact Or.inr CompilerAnnotationBuiltin.memoryguardOp

theorem withCompilerArtifactBuiltins_accepts_setimmutableOp
    (profile : CompilerProfile) :
    (profile.withCompilerArtifactBuiltins).builtinOK
      Evm.Builtin.setimmutableOp := by
  exact Or.inr CompilerArtifactBuiltin.setimmutableOp

theorem withCompilerArtifactBuiltins_accepts_loadimmutableOp
    (profile : CompilerProfile) :
    (profile.withCompilerArtifactBuiltins).builtinOK
      Evm.Builtin.loadimmutableOp := by
  exact Or.inr CompilerArtifactBuiltin.loadimmutableOp

theorem withCompilerArtifactBuiltins_accepts_linkersymbolOp
    (profile : CompilerProfile) :
    (profile.withCompilerArtifactBuiltins).builtinOK
      Evm.Builtin.linkersymbolOp := by
  exact Or.inr CompilerArtifactBuiltin.linkersymbolOp

theorem withVerbatimBuiltins_accepts_verbatimOp
    (profile : CompilerProfile) (inputs outputs : Nat) :
    (profile.withVerbatimBuiltins).builtinOK
      (Evm.Builtin.verbatimOp inputs outputs) := by
  exact Or.inr (VerbatimBuiltin.verbatimOp inputs outputs)

theorem withLoweringEnvironmentBuiltins_accepts_gasOp
    (profile : CompilerProfile) :
    (profile.withLoweringEnvironmentBuiltins).builtinOK
      Evm.Builtin.gasOp := by
  exact Or.inr LoweringEnvironmentBuiltin.gasOp

theorem withLoweringEnvironmentBuiltins_accepts_pcOp
    (profile : CompilerProfile) :
    (profile.withLoweringEnvironmentBuiltins).builtinOK
      Evm.Builtin.pcOp := by
  exact Or.inr LoweringEnvironmentBuiltin.pcOp

theorem withExternalCalls_accepts_callOp (profile : CompilerProfile) :
    (profile.withExternalCalls).builtinOK Evm.Builtin.callOp := by
  exact Or.inr ExternalCallBuiltin.callOp

theorem withExternalCalls_accepts_log0Op (profile : CompilerProfile) :
    (profile.withExternalCalls).builtinOK Evm.Builtin.log0Op := by
  exact Or.inr ExternalCallBuiltin.log0Op

theorem withExternalCalls_accepts_createOp (profile : CompilerProfile) :
    (profile.withExternalCalls).builtinOK Evm.Builtin.createOp := by
  exact Or.inr ExternalCallBuiltin.createOp

theorem withExternalCalls_accepts_selfdestructOp (profile : CompilerProfile) :
    (profile.withExternalCalls).builtinOK Evm.Builtin.selfdestructOp := by
  exact Or.inr ExternalCallBuiltin.selfdestructOp

theorem withExternalQueryBuiltins_accepts_balanceOp
    (profile : CompilerProfile) :
    (profile.withExternalQueryBuiltins).builtinOK Evm.Builtin.balanceOp := by
  exact Or.inr ExternalQueryBuiltin.balanceOp

theorem withExternalQueryBuiltins_accepts_extcodecopyOp
    (profile : CompilerProfile) :
    (profile.withExternalQueryBuiltins).builtinOK Evm.Builtin.extcodecopyOp := by
  exact Or.inr ExternalQueryBuiltin.extcodecopyOp

theorem withTransientStorageBuiltins_accepts_tloadOp
    (profile : CompilerProfile) :
    (profile.withTransientStorageBuiltins).builtinOK Evm.Builtin.tloadOp := by
  exact Or.inr TransientStorageBuiltin.tloadOp

theorem withTransientStorageBuiltins_accepts_tstoreOp
    (profile : CompilerProfile) :
    (profile.withTransientStorageBuiltins).builtinOK Evm.Builtin.tstoreOp := by
  exact Or.inr TransientStorageBuiltin.tstoreOp

theorem currentSolidCore_withMemoryBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact MemoryBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withMemoryBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryWrite := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withMemoryCopyBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryCopyBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact MemoryCopyBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withMemoryCopyBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryCopyBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withMemoryHashBuiltins_builtin_claim_exact_or_symbolic
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryHashBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.symbolic := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      exact Or.inr (MemoryHashBuiltin.claim_symbolic hBuiltin)

theorem currentSolidCore_withMemoryHashBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withMemoryHashBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.memoryHash := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin
      exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem currentSolidCore_withBufferBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withBufferBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact BufferBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withBufferBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withBufferBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withReturnDataBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withReturnDataBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact ReturnDataBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withReturnDataBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withReturnDataBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferRead ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withCodeBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCodeBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact CodeBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withCodeBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCodeBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferSize ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withObjectDataBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withObjectDataBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact ObjectDataBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withObjectDataBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withObjectDataBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.objectDataCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withContextBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withContextBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact ContextWordBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withContextBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withContextBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.contextWord := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withCompilerAnnotations_builtin_claim_exact_or_abstracted
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCompilerAnnotations.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      exact Or.inr (CompilerAnnotationBuiltin.claim_abstracted hBuiltin)

theorem currentSolidCore_withCompilerAnnotations_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCompilerAnnotations.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.compilerBuiltin := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withCompilerArtifactBuiltins_builtin_claim_exact_or_abstracted
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCompilerArtifactBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      exact Or.inr (CompilerArtifactBuiltin.claim_abstracted hBuiltin)

theorem currentSolidCore_withCompilerArtifactBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withCompilerArtifactBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.compilerBuiltin := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withVerbatimBuiltins_builtin_claim_exact_or_abstracted
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withVerbatimBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      exact Or.inr (VerbatimBuiltin.claim_abstracted hBuiltin)

theorem currentSolidCore_withVerbatimBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withVerbatimBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.verbatim := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin
      simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withExternalCalls_builtin_claim_exact_or_abstracted
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withExternalCalls.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.abstractedBuiltin := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      exact Or.inr (ExternalCallBuiltin.claim_abstracted hBuiltin)

theorem currentSolidCore_withExternalCalls_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withExternalCalls.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.externalCall ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.log ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.contractCreation ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.selfdestruct := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withExternalQueryBuiltins_builtin_claim_exact_abstracted_or_symbolic
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withExternalQueryBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul ∨
      builtin.claim? = some Evm.ClaimKind.abstractedBuiltin ∨
      builtin.claim? = some Evm.ClaimKind.symbolic := by
  cases h with
  | inl hBuiltin =>
      exact Or.inl (CurrentSolidCoreBuiltin.claim_exactYul hBuiltin)
  | inr hBuiltin =>
      cases hBuiltin <;>
        first
        | exact Or.inr (Or.inr rfl)
        | exact Or.inr (Or.inl rfl)

theorem currentSolidCore_withExternalQueryBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withExternalQueryBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.externalQuery ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.bufferCopy := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem currentSolidCore_withTransientStorageBuiltins_builtin_claim_exactYul
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withTransientStorageBuiltins.builtinOK builtin) :
    builtin.claim? = some Evm.ClaimKind.exactYul := by
  cases h with
  | inl hBuiltin =>
      exact CurrentSolidCoreBuiltin.claim_exactYul hBuiltin
  | inr hBuiltin =>
      exact TransientStorageBuiltin.claim_exactYul hBuiltin

theorem currentSolidCore_withTransientStorageBuiltins_builtin_semanticCoverage_lane
    {builtin : Evm.Builtin}
    (h : currentSolidCore.withTransientStorageBuiltins.builtinOK builtin) :
    builtin.semanticCoverage? = some Evm.SemanticCoverage.pureWord ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.storage ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.controlHalt ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.discard ∨
      builtin.semanticCoverage? = some Evm.SemanticCoverage.transientStorage := by
  cases h with
  | inl hBuiltin =>
      cases CurrentSolidCoreBuiltin.semanticCoverage_exact_lane hBuiltin with
      | inl hPure => exact Or.inl hPure
      | inr hRest =>
          cases hRest with
          | inl hStorage => exact Or.inr (Or.inl hStorage)
          | inr hRest =>
              cases hRest with
              | inl hHalt => exact Or.inr (Or.inr (Or.inl hHalt))
              | inr hDiscard =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl hDiscard)))
  | inr hBuiltin =>
      cases hBuiltin <;> simp [Evm.Builtin.semanticCoverage?]

theorem builtinOK_has_claim (profile : CompilerProfile)
    {builtin : Evm.Builtin} (h : profile.builtinOK builtin) :
    ∃ claim, builtin.claim? = some claim := by
  rcases profile.builtinOK_signature h with ⟨sig, hSig⟩
  exact Evm.Builtin.claim?_of_signature? hSig

theorem builtinOK_has_semanticCoverage (profile : CompilerProfile)
    {builtin : Evm.Builtin} (h : profile.builtinOK builtin) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  rcases profile.builtinOK_signature h with ⟨sig, hSig⟩
  exact Evm.Builtin.semanticCoverage?_of_signature? hSig

theorem excludes_opaque (profile : CompilerProfile) (id : Nat) :
    ¬ profile.builtinOK (Evm.Builtin.opaque id) := by
  intro h
  rcases profile.builtinOK_signature h with ⟨sig, hSig⟩
  simp [Evm.Builtin.signature?] at hSig

end CompilerProfile

mutual
  inductive CompilerEmittableExpr (profile : CompilerProfile) : Expr -> Prop where
    | value {value : Value} :
        profile.valueOK value ->
        CompilerEmittableExpr profile (Expr.value value)
    | var (name : Name) :
        CompilerEmittableExpr profile (Expr.var name)
    | keccak {bytes : SymbolicBytes} :
        profile.allowSymbolicKeccakExpr ->
        CompilerEmittableExpr profile (Expr.keccak bytes)
    | dataSize {label : DataLabel} :
        profile.allowDataRefs ->
        CompilerEmittableExpr profile (Expr.dataSize label)
    | dataOffset {label : DataLabel} :
        profile.allowDataRefs ->
        CompilerEmittableExpr profile (Expr.dataOffset label)
    | builtin {builtin : Evm.Builtin} {args : List Expr} :
        profile.builtinOK builtin ->
        CompilerEmittableExprs profile args ->
        CompilerEmittableExpr profile (Expr.builtin builtin args)

  inductive CompilerEmittableExprs (profile : CompilerProfile) :
      List Expr -> Prop where
    | nil : CompilerEmittableExprs profile []
    | cons {expr : Expr} {rest : List Expr} :
        CompilerEmittableExpr profile expr ->
        CompilerEmittableExprs profile rest ->
        CompilerEmittableExprs profile (expr :: rest)
end

theorem CompilerEmittableExpr.builtin_has_signature
    {profile : CompilerProfile} {builtin : Evm.Builtin} {args : List Expr}
    (h : CompilerEmittableExpr profile (Expr.builtin builtin args)) :
    ∃ sig, builtin.signature? = some sig := by
  cases h with
  | builtin hBuiltin _ => exact profile.builtinOK_signature hBuiltin

theorem CompilerEmittableExpr.excludes_opaque
    (profile : CompilerProfile) (id : Nat) (args : List Expr) :
    ¬ CompilerEmittableExpr profile
      (Expr.builtin (Evm.Builtin.opaque id) args) := by
  intro h
  rcases CompilerEmittableExpr.builtin_has_signature h with ⟨sig, hSig⟩
  simp [Evm.Builtin.signature?] at hSig

mutual
  inductive CompilerEmittableStmt (profile : CompilerProfile) : Stmt -> Prop where
    | skip : CompilerEmittableStmt profile Stmt.skip
    | expr {expr : Expr} :
        CompilerEmittableExpr profile expr ->
        CompilerEmittableStmt profile (Stmt.expr expr)
    | let1None {name : Name} :
        CompilerEmittableStmt profile (Stmt.let1 name none)
    | let1Some {name : Name} {expr : Expr} :
        CompilerEmittableExpr profile expr ->
        CompilerEmittableStmt profile (Stmt.let1 name (some expr))
    | letManyNone {names : List Name} :
        CompilerEmittableStmt profile (Stmt.letMany names none)
    | letManySome {names : List Name} {exprs : List Expr} :
        CompilerEmittableExprs profile exprs ->
        CompilerEmittableStmt profile (Stmt.letMany names (some exprs))
    | funDef {name : Name} {params returns : List Name} {body : Stmt} :
        profile.allowFunctionDefs ->
        CompilerEmittableStmt profile body ->
        CompilerEmittableStmt profile (Stmt.funDef name params returns body)
    | assign {name : Name} {expr : Expr} :
        CompilerEmittableExpr profile expr ->
        CompilerEmittableStmt profile (Stmt.assign name expr)
    | assignMany {names : List Name} {exprs : List Expr} :
        CompilerEmittableExprs profile exprs ->
        CompilerEmittableStmt profile (Stmt.assignMany names exprs)
    | letCall {names : List Name} {fnName : Name} {args : List Expr} :
        profile.allowFunctionCalls ->
        CompilerEmittableExprs profile args ->
        CompilerEmittableStmt profile (Stmt.letCall names fnName args)
    | assignCall {names : List Name} {fnName : Name} {args : List Expr} :
        profile.allowFunctionCalls ->
        CompilerEmittableExprs profile args ->
        CompilerEmittableStmt profile (Stmt.assignCall names fnName args)
    | seq {first second : Stmt} :
        CompilerEmittableStmt profile first ->
        CompilerEmittableStmt profile second ->
        CompilerEmittableStmt profile (Stmt.seq first second)
    | block {stmts : List Stmt} :
        CompilerEmittableBlock profile stmts ->
        CompilerEmittableStmt profile (Stmt.block stmts)
    | ifThen {cond : Expr} {body : Stmt} :
        CompilerEmittableExpr profile cond ->
        CompilerEmittableStmt profile body ->
        CompilerEmittableStmt profile (Stmt.ifThen cond body)
    | switch {discr : Expr} {cases : List (Value × Stmt)}
        {defaultBranch : Option Stmt} :
        profile.allowSwitch ->
        CompilerEmittableExpr profile discr ->
        CompilerEmittableSwitchCases profile cases ->
        CompilerEmittableOptionalStmt profile defaultBranch ->
        CompilerEmittableStmt profile (Stmt.switch discr cases defaultBranch)
    | forLoop {pre : Stmt} {cond : Expr} {post body : Stmt} :
        CompilerEmittableStmt profile pre ->
        CompilerEmittableExpr profile cond ->
        CompilerEmittableStmt profile post ->
        CompilerEmittableStmt profile body ->
        CompilerEmittableStmt profile (Stmt.forLoop pre cond post body)
    | break : CompilerEmittableStmt profile Stmt.break
    | continue : CompilerEmittableStmt profile Stmt.continue
    | leave : CompilerEmittableStmt profile Stmt.leave

  inductive CompilerEmittableBlock (profile : CompilerProfile) :
      List Stmt -> Prop where
    | nil : CompilerEmittableBlock profile []
    | cons {stmt : Stmt} {rest : List Stmt} :
        CompilerEmittableStmt profile stmt ->
        CompilerEmittableBlock profile rest ->
        CompilerEmittableBlock profile (stmt :: rest)

  inductive CompilerEmittableSwitchCases (profile : CompilerProfile) :
      List (Value × Stmt) -> Prop where
    | nil : CompilerEmittableSwitchCases profile []
    | cons {label : Value} {branch : Stmt} {rest : List (Value × Stmt)} :
        profile.valueOK label ->
        CompilerEmittableStmt profile branch ->
        CompilerEmittableSwitchCases profile rest ->
        CompilerEmittableSwitchCases profile ((label, branch) :: rest)

  inductive CompilerEmittableOptionalStmt (profile : CompilerProfile) :
      Option Stmt -> Prop where
    | none : CompilerEmittableOptionalStmt profile none
    | some {stmt : Stmt} :
        CompilerEmittableStmt profile stmt ->
        CompilerEmittableOptionalStmt profile (some stmt)
end

theorem CompilerEmittableExpr.currentSolidCore_value
    {value : Value}
    (hValue : CompilerProfile.CurrentSolidCoreValue value) :
    CompilerEmittableExpr CompilerProfile.currentSolidCore
      (Expr.value value) :=
  CompilerEmittableExpr.value hValue

theorem CompilerEmittableExpr.currentSolidityEmittable_value
    {value : Value}
    (hValue :
      CompilerProfile.currentSolidityEmittable.valueOK value) :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.value value) :=
  CompilerEmittableExpr.value hValue

theorem CompilerEmittableExpr.currentSolidCore_var
    (name : Name) :
    CompilerEmittableExpr CompilerProfile.currentSolidCore
      (Expr.var name) :=
  CompilerEmittableExpr.var name

theorem CompilerEmittableExpr.currentSolidityEmittable_var
    (name : Name) :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.var name) :=
  CompilerEmittableExpr.var name

theorem CompilerEmittableExpr.currentSolidCore_builtin
    {builtin : Evm.Builtin} {args : List Expr}
    (hBuiltin : CompilerProfile.currentSolidCore.builtinOK builtin)
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidCore args) :
    CompilerEmittableExpr CompilerProfile.currentSolidCore
      (Expr.builtin builtin args) :=
  CompilerEmittableExpr.builtin hBuiltin hArgs

theorem CompilerEmittableExpr.currentSolidityEmittable_builtin
    {builtin : Evm.Builtin} {args : List Expr}
    (hBuiltin :
      CompilerProfile.currentSolidityEmittable.builtinOK builtin)
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable args) :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.builtin builtin args) :=
  CompilerEmittableExpr.builtin hBuiltin hArgs

theorem CompilerEmittableExpr.currentSolidityEmittable_builtinFromTable
    {builtin : Evm.Builtin} {args : List Expr}
    (hBuiltin : CompilerProfile.CurrentSolidityEmittableBuiltin builtin)
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable args) :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.builtin builtin args) :=
  CompilerEmittableExpr.currentSolidityEmittable_builtin
    ((CompilerProfile.currentSolidityEmittable_builtinOK_iff builtin).2
      hBuiltin)
    hArgs

theorem CompilerEmittableExpr.currentSolidityEmittable_dataSize
    {label : DataLabel} :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.dataSize label) :=
  CompilerEmittableExpr.dataSize
    CompilerProfile.currentSolidityEmittable_allowDataRefs

theorem CompilerEmittableExpr.currentSolidityEmittable_dataOffset
    {label : DataLabel} :
    CompilerEmittableExpr CompilerProfile.currentSolidityEmittable
      (Expr.dataOffset label) :=
  CompilerEmittableExpr.dataOffset
    CompilerProfile.currentSolidityEmittable_allowDataRefs

theorem CompilerEmittableExprs.currentSolidCore_nil :
    CompilerEmittableExprs CompilerProfile.currentSolidCore [] :=
  CompilerEmittableExprs.nil

theorem CompilerEmittableExprs.currentSolidityEmittable_nil :
    CompilerEmittableExprs CompilerProfile.currentSolidityEmittable [] :=
  CompilerEmittableExprs.nil

theorem CompilerEmittableExprs.currentSolidCore_cons
    {expr : Expr} {rest : List Expr}
    (hExpr :
      CompilerEmittableExpr CompilerProfile.currentSolidCore expr)
    (hRest :
      CompilerEmittableExprs CompilerProfile.currentSolidCore rest) :
    CompilerEmittableExprs CompilerProfile.currentSolidCore (expr :: rest) :=
  CompilerEmittableExprs.cons hExpr hRest

theorem CompilerEmittableExprs.currentSolidityEmittable_cons
    {expr : Expr} {rest : List Expr}
    (hExpr :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable expr)
    (hRest :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable rest) :
    CompilerEmittableExprs CompilerProfile.currentSolidityEmittable
      (expr :: rest) :=
  CompilerEmittableExprs.cons hExpr hRest

theorem CompilerEmittableBlock.currentSolidCore_nil :
    CompilerEmittableBlock CompilerProfile.currentSolidCore [] :=
  CompilerEmittableBlock.nil

theorem CompilerEmittableBlock.currentSolidityEmittable_nil :
    CompilerEmittableBlock CompilerProfile.currentSolidityEmittable [] :=
  CompilerEmittableBlock.nil

theorem CompilerEmittableBlock.currentSolidCore_cons
    {stmt : Stmt} {rest : List Stmt}
    (hStmt :
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt)
    (hRest :
      CompilerEmittableBlock CompilerProfile.currentSolidCore rest) :
    CompilerEmittableBlock CompilerProfile.currentSolidCore (stmt :: rest) :=
  CompilerEmittableBlock.cons hStmt hRest

theorem CompilerEmittableBlock.currentSolidityEmittable_cons
    {stmt : Stmt} {rest : List Stmt}
    (hStmt :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt)
    (hRest :
      CompilerEmittableBlock CompilerProfile.currentSolidityEmittable rest) :
    CompilerEmittableBlock CompilerProfile.currentSolidityEmittable
      (stmt :: rest) :=
  CompilerEmittableBlock.cons hStmt hRest

theorem CompilerEmittableSwitchCases.currentSolidCore_nil :
    CompilerEmittableSwitchCases CompilerProfile.currentSolidCore [] :=
  CompilerEmittableSwitchCases.nil

theorem CompilerEmittableSwitchCases.currentSolidityEmittable_nil :
    CompilerEmittableSwitchCases
      CompilerProfile.currentSolidityEmittable [] :=
  CompilerEmittableSwitchCases.nil

theorem CompilerEmittableSwitchCases.currentSolidCore_cons
    {label : Value} {branch : Stmt} {rest : List (Value × Stmt)}
    (hLabel : CompilerProfile.CurrentSolidCoreValue label)
    (hBranch :
      CompilerEmittableStmt CompilerProfile.currentSolidCore branch)
    (hRest :
      CompilerEmittableSwitchCases CompilerProfile.currentSolidCore rest) :
    CompilerEmittableSwitchCases CompilerProfile.currentSolidCore
      ((label, branch) :: rest) :=
  CompilerEmittableSwitchCases.cons hLabel hBranch hRest

theorem CompilerEmittableSwitchCases.currentSolidityEmittable_cons
    {label : Value} {branch : Stmt} {rest : List (Value × Stmt)}
    (hLabel :
      CompilerProfile.currentSolidityEmittable.valueOK label)
    (hBranch :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable branch)
    (hRest :
      CompilerEmittableSwitchCases
        CompilerProfile.currentSolidityEmittable rest) :
    CompilerEmittableSwitchCases CompilerProfile.currentSolidityEmittable
      ((label, branch) :: rest) :=
  CompilerEmittableSwitchCases.cons hLabel hBranch hRest

theorem CompilerEmittableOptionalStmt.currentSolidCore_none :
    CompilerEmittableOptionalStmt CompilerProfile.currentSolidCore
      (Option.none : Option Stmt) :=
  CompilerEmittableOptionalStmt.none

theorem CompilerEmittableOptionalStmt.currentSolidityEmittable_none :
    CompilerEmittableOptionalStmt
      CompilerProfile.currentSolidityEmittable
      (Option.none : Option Stmt) :=
  CompilerEmittableOptionalStmt.none

theorem CompilerEmittableOptionalStmt.currentSolidCore_some
    {stmt : Stmt}
    (hStmt :
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt) :
    CompilerEmittableOptionalStmt CompilerProfile.currentSolidCore
      (Option.some stmt) :=
  CompilerEmittableOptionalStmt.some hStmt

theorem CompilerEmittableOptionalStmt.currentSolidityEmittable_some
    {stmt : Stmt}
    (hStmt :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt) :
    CompilerEmittableOptionalStmt CompilerProfile.currentSolidityEmittable
      (Option.some stmt) :=
  CompilerEmittableOptionalStmt.some hStmt

theorem CompilerEmittableStmt.currentSolidCore_skip :
    CompilerEmittableStmt CompilerProfile.currentSolidCore Stmt.skip :=
  CompilerEmittableStmt.skip

theorem CompilerEmittableStmt.currentSolidityEmittable_skip :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      Stmt.skip :=
  CompilerEmittableStmt.skip

theorem CompilerEmittableStmt.currentSolidCore_expr
    {expr : Expr}
    (hExpr : CompilerEmittableExpr CompilerProfile.currentSolidCore expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore (Stmt.expr expr) :=
  CompilerEmittableStmt.expr hExpr

theorem CompilerEmittableStmt.currentSolidityEmittable_expr
    {expr : Expr}
    (hExpr :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.expr expr) :=
  CompilerEmittableStmt.expr hExpr

theorem CompilerEmittableStmt.currentSolidCore_let1None
    {name : Name} :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.let1 name none) :=
  CompilerEmittableStmt.let1None

theorem CompilerEmittableStmt.currentSolidityEmittable_let1None
    {name : Name} :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.let1 name none) :=
  CompilerEmittableStmt.let1None

theorem CompilerEmittableStmt.currentSolidCore_let1Some
    {name : Name} {expr : Expr}
    (hExpr : CompilerEmittableExpr CompilerProfile.currentSolidCore expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.let1 name (some expr)) :=
  CompilerEmittableStmt.let1Some hExpr

theorem CompilerEmittableStmt.currentSolidityEmittable_let1Some
    {name : Name} {expr : Expr}
    (hExpr :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.let1 name (some expr)) :=
  CompilerEmittableStmt.let1Some hExpr

theorem CompilerEmittableStmt.currentSolidCore_letManyNone
    {names : List Name} :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.letMany names none) :=
  CompilerEmittableStmt.letManyNone

theorem CompilerEmittableStmt.currentSolidityEmittable_letManyNone
    {names : List Name} :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.letMany names none) :=
  CompilerEmittableStmt.letManyNone

theorem CompilerEmittableStmt.currentSolidCore_letManySome
    {names : List Name} {exprs : List Expr}
    (hExprs :
      CompilerEmittableExprs CompilerProfile.currentSolidCore exprs) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.letMany names (some exprs)) :=
  CompilerEmittableStmt.letManySome hExprs

theorem CompilerEmittableStmt.currentSolidityEmittable_letManySome
    {names : List Name} {exprs : List Expr}
    (hExprs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable exprs) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.letMany names (some exprs)) :=
  CompilerEmittableStmt.letManySome hExprs

theorem CompilerEmittableStmt.currentSolidCore_assign
    {name : Name} {expr : Expr}
    (hExpr : CompilerEmittableExpr CompilerProfile.currentSolidCore expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.assign name expr) :=
  CompilerEmittableStmt.assign hExpr

theorem CompilerEmittableStmt.currentSolidityEmittable_assign
    {name : Name} {expr : Expr}
    (hExpr :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable expr) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.assign name expr) :=
  CompilerEmittableStmt.assign hExpr

theorem CompilerEmittableStmt.currentSolidCore_assignMany
    {names : List Name} {exprs : List Expr}
    (hExprs :
      CompilerEmittableExprs CompilerProfile.currentSolidCore exprs) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.assignMany names exprs) :=
  CompilerEmittableStmt.assignMany hExprs

theorem CompilerEmittableStmt.currentSolidityEmittable_assignMany
    {names : List Name} {exprs : List Expr}
    (hExprs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable exprs) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.assignMany names exprs) :=
  CompilerEmittableStmt.assignMany hExprs

theorem CompilerEmittableStmt.currentSolidCore_seq
    {first second : Stmt}
    (hFirst :
      CompilerEmittableStmt CompilerProfile.currentSolidCore first)
    (hSecond :
      CompilerEmittableStmt CompilerProfile.currentSolidCore second) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.seq first second) :=
  CompilerEmittableStmt.seq hFirst hSecond

theorem CompilerEmittableStmt.currentSolidityEmittable_seq
    {first second : Stmt}
    (hFirst :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable first)
    (hSecond :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable second) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.seq first second) :=
  CompilerEmittableStmt.seq hFirst hSecond

theorem CompilerEmittableStmt.currentSolidCore_block
    {stmts : List Stmt}
    (hBlock :
      CompilerEmittableBlock CompilerProfile.currentSolidCore stmts) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.block stmts) :=
  CompilerEmittableStmt.block hBlock

theorem CompilerEmittableStmt.currentSolidityEmittable_block
    {stmts : List Stmt}
    (hBlock :
      CompilerEmittableBlock CompilerProfile.currentSolidityEmittable stmts) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.block stmts) :=
  CompilerEmittableStmt.block hBlock

theorem CompilerEmittableStmt.currentSolidCore_ifThen
    {cond : Expr} {body : Stmt}
    (hCond :
      CompilerEmittableExpr CompilerProfile.currentSolidCore cond)
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidCore body) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.ifThen cond body) :=
  CompilerEmittableStmt.ifThen hCond hBody

theorem CompilerEmittableStmt.currentSolidityEmittable_ifThen
    {cond : Expr} {body : Stmt}
    (hCond :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable cond)
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable body) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.ifThen cond body) :=
  CompilerEmittableStmt.ifThen hCond hBody

theorem CompilerEmittableStmt.currentSolidCore_switch
    {discr : Expr} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt}
    (hDiscr :
      CompilerEmittableExpr CompilerProfile.currentSolidCore discr)
    (hCases :
      CompilerEmittableSwitchCases CompilerProfile.currentSolidCore cases)
    (hDefault :
      CompilerEmittableOptionalStmt CompilerProfile.currentSolidCore
        defaultBranch) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.switch discr cases defaultBranch) :=
  CompilerEmittableStmt.switch
    CompilerProfile.currentSolidCore_allowSwitch hDiscr hCases hDefault

theorem CompilerEmittableStmt.currentSolidityEmittable_switch
    {discr : Expr} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt}
    (hDiscr :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable discr)
    (hCases :
      CompilerEmittableSwitchCases
        CompilerProfile.currentSolidityEmittable cases)
    (hDefault :
      CompilerEmittableOptionalStmt
        CompilerProfile.currentSolidityEmittable defaultBranch) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.switch discr cases defaultBranch) :=
  CompilerEmittableStmt.switch
    CompilerProfile.currentSolidityEmittable_allowSwitch hDiscr hCases
      hDefault

theorem CompilerEmittableStmt.currentSolidCore_funDef
    {name : Name} {params returns : List Name} {body : Stmt}
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidCore body) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.funDef name params returns body) :=
  CompilerEmittableStmt.funDef
    CompilerProfile.currentSolidCore_allowFunctionDefs hBody

theorem CompilerEmittableStmt.currentSolidityEmittable_funDef
    {name : Name} {params returns : List Name} {body : Stmt}
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable body) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.funDef name params returns body) :=
  CompilerEmittableStmt.funDef
    CompilerProfile.currentSolidityEmittable_allowFunctionDefs hBody

theorem CompilerEmittableStmt.currentSolidCore_letCall
    {names : List Name} {fnName : Name} {args : List Expr}
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidCore args) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.letCall names fnName args) :=
  CompilerEmittableStmt.letCall
    CompilerProfile.currentSolidCore_allowFunctionCalls hArgs

theorem CompilerEmittableStmt.currentSolidityEmittable_letCall
    {names : List Name} {fnName : Name} {args : List Expr}
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable args) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.letCall names fnName args) :=
  CompilerEmittableStmt.letCall
    CompilerProfile.currentSolidityEmittable_allowFunctionCalls hArgs

theorem CompilerEmittableStmt.currentSolidCore_assignCall
    {names : List Name} {fnName : Name} {args : List Expr}
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidCore args) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.assignCall names fnName args) :=
  CompilerEmittableStmt.assignCall
    CompilerProfile.currentSolidCore_allowFunctionCalls hArgs

theorem CompilerEmittableStmt.currentSolidityEmittable_assignCall
    {names : List Name} {fnName : Name} {args : List Expr}
    (hArgs :
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable args) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.assignCall names fnName args) :=
  CompilerEmittableStmt.assignCall
    CompilerProfile.currentSolidityEmittable_allowFunctionCalls hArgs

theorem CompilerEmittableStmt.currentSolidCore_forLoop
    {pre : Stmt} {cond : Expr} {post body : Stmt}
    (hPre :
      CompilerEmittableStmt CompilerProfile.currentSolidCore pre)
    (hCond :
      CompilerEmittableExpr CompilerProfile.currentSolidCore cond)
    (hPost :
      CompilerEmittableStmt CompilerProfile.currentSolidCore post)
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidCore body) :
    CompilerEmittableStmt CompilerProfile.currentSolidCore
      (Stmt.forLoop pre cond post body) :=
  CompilerEmittableStmt.forLoop hPre hCond hPost hBody

theorem CompilerEmittableStmt.currentSolidityEmittable_forLoop
    {pre : Stmt} {cond : Expr} {post body : Stmt}
    (hPre :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable pre)
    (hCond :
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable cond)
    (hPost :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable post)
    (hBody :
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable body) :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      (Stmt.forLoop pre cond post body) :=
  CompilerEmittableStmt.forLoop hPre hCond hPost hBody

theorem CompilerEmittableStmt.currentSolidCore_break :
    CompilerEmittableStmt CompilerProfile.currentSolidCore Stmt.break :=
  CompilerEmittableStmt.break

theorem CompilerEmittableStmt.currentSolidityEmittable_break :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      Stmt.break :=
  CompilerEmittableStmt.break

theorem CompilerEmittableStmt.currentSolidCore_continue :
    CompilerEmittableStmt CompilerProfile.currentSolidCore Stmt.continue :=
  CompilerEmittableStmt.continue

theorem CompilerEmittableStmt.currentSolidityEmittable_continue :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      Stmt.continue :=
  CompilerEmittableStmt.continue

theorem CompilerEmittableStmt.currentSolidCore_leave :
    CompilerEmittableStmt CompilerProfile.currentSolidCore Stmt.leave :=
  CompilerEmittableStmt.leave

theorem CompilerEmittableStmt.currentSolidityEmittable_leave :
    CompilerEmittableStmt CompilerProfile.currentSolidityEmittable
      Stmt.leave :=
  CompilerEmittableStmt.leave

theorem compilerEmittableBuiltin_has_signature
    (profile : CompilerProfile) {builtin : Evm.Builtin}
    (h : profile.builtinOK builtin) :
    ∃ sig, builtin.signature? = some sig :=
  profile.builtinOK_signature h

def BuiltinSemanticEvidence (builtin : Evm.Builtin) : Prop :=
  (∃ sig, builtin.signature? = some sig) ∧
    (∃ claim, builtin.claim? = some claim) ∧
      ∃ coverage, builtin.semanticCoverage? = some coverage

def BuiltinNotOpaque (builtin : Evm.Builtin) : Prop :=
  ∀ id : Nat, builtin ≠ Evm.Builtin.opaque id

def BuiltinNotVerbatim (builtin : Evm.Builtin) : Prop :=
  ∀ inCount outCount : Nat,
    builtin ≠ Evm.Builtin.verbatimOp inCount outCount

def BuiltinNotLoweringEnvironment (builtin : Evm.Builtin) : Prop :=
  builtin ≠ Evm.Builtin.gasOp ∧ builtin ≠ Evm.Builtin.pcOp

def BuiltinCanonicalSolidityEmittableBoundary
    (builtin : Evm.Builtin) : Prop :=
  BuiltinNotOpaque builtin ∧
    BuiltinNotVerbatim builtin ∧
      BuiltinNotLoweringEnvironment builtin

theorem CompilerProfile.builtinOK_notOpaque
    (profile : CompilerProfile) {builtin : Evm.Builtin}
    (h : profile.builtinOK builtin) :
    BuiltinNotOpaque builtin := by
  intro id hEq
  cases hEq
  exact (CompilerProfile.excludes_opaque profile id) h

theorem BuiltinSemanticEvidence.has_signature
    {builtin : Evm.Builtin}
    (h : BuiltinSemanticEvidence builtin) :
    ∃ sig, builtin.signature? = some sig :=
  h.1

theorem BuiltinSemanticEvidence.has_claim
    {builtin : Evm.Builtin}
    (h : BuiltinSemanticEvidence builtin) :
    ∃ claim, builtin.claim? = some claim :=
  h.2.1

theorem BuiltinSemanticEvidence.has_semanticCoverage
    {builtin : Evm.Builtin}
    (h : BuiltinSemanticEvidence builtin) :
    ∃ coverage, builtin.semanticCoverage? = some coverage :=
  h.2.2

def BuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) (builtin : Evm.Builtin) : Prop :=
  ∃ claim, builtin.claim? = some claim ∧ claimOK claim

def DeferredBuiltinOnlyGasOrPc (builtin : Evm.Builtin) : Prop :=
  builtin.claim? = some Evm.ClaimKind.deferredToLowering ->
    builtin = Evm.Builtin.gasOp ∨ builtin = Evm.Builtin.pcOp

def ExactYulClaim (claim : Evm.ClaimKind) : Prop :=
  claim = Evm.ClaimKind.exactYul

def ExactOrAbstractedClaim (claim : Evm.ClaimKind) : Prop :=
  claim = Evm.ClaimKind.exactYul ∨
    claim = Evm.ClaimKind.abstractedBuiltin

def ExactAbstractedOrSymbolicClaim (claim : Evm.ClaimKind) : Prop :=
  claim = Evm.ClaimKind.exactYul ∨
    claim = Evm.ClaimKind.abstractedBuiltin ∨
      claim = Evm.ClaimKind.symbolic

def ExactAbstractedSymbolicOrDeferredClaim
    (claim : Evm.ClaimKind) : Prop :=
  claim = Evm.ClaimKind.exactYul ∨
    claim = Evm.ClaimKind.abstractedBuiltin ∨
      claim = Evm.ClaimKind.symbolic ∨
        claim = Evm.ClaimKind.deferredToLowering

def NonDeferredClaim (claim : Evm.ClaimKind) : Prop :=
  claim ≠ Evm.ClaimKind.deferredToLowering

def BuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop)
    (builtin : Evm.Builtin) : Prop :=
  ∃ coverage, builtin.semanticCoverage? = some coverage ∧ coverageOK coverage

def CurrentSolidCoreSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  coverage = Evm.SemanticCoverage.pureWord ∨
    coverage = Evm.SemanticCoverage.storage ∨
      coverage = Evm.SemanticCoverage.controlHalt ∨
        coverage = Evm.SemanticCoverage.discard

def CurrentSolidCoreWithMemorySemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.memoryRead ∨
    coverage = Evm.SemanticCoverage.memoryWrite

def CurrentSolidCoreWithMemoryCopySemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.memoryCopy

def CurrentSolidCoreWithMemoryHashSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.memoryHash

def CurrentSolidCoreWithBufferSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.bufferRead ∨
    coverage = Evm.SemanticCoverage.bufferSize ∨
    coverage = Evm.SemanticCoverage.bufferCopy

def CurrentSolidCoreWithReturnDataSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.bufferRead ∨
    coverage = Evm.SemanticCoverage.bufferSize ∨
    coverage = Evm.SemanticCoverage.bufferCopy

def CurrentSolidCoreWithCodeSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.bufferSize ∨
    coverage = Evm.SemanticCoverage.bufferCopy

def CurrentSolidCoreWithObjectDataSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.objectDataCopy

def CurrentSolidCoreWithContextSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.contextWord

def CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.compilerBuiltin

def CurrentSolidCoreWithCompilerArtifactsSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.compilerBuiltin

def CurrentSolidCoreWithVerbatimSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.verbatim

def CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.loweringEnvironment

def CurrentSolidCoreWithExternalCallsSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.externalCall ∨
    coverage = Evm.SemanticCoverage.log ∨
    coverage = Evm.SemanticCoverage.contractCreation ∨
    coverage = Evm.SemanticCoverage.selfdestruct

def CurrentSolidCoreWithExternalQuerySemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.externalQuery ∨
    coverage = Evm.SemanticCoverage.bufferCopy

def CurrentSolidCoreWithTransientStorageSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreSemanticCoverage coverage ∨
    coverage = Evm.SemanticCoverage.transientStorage

def CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidCoreWithMemorySemanticCoverage coverage ∨
    CurrentSolidCoreWithMemoryCopySemanticCoverage coverage ∨
    CurrentSolidCoreWithMemoryHashSemanticCoverage coverage ∨
    CurrentSolidCoreWithBufferSemanticCoverage coverage ∨
    CurrentSolidCoreWithReturnDataSemanticCoverage coverage ∨
    CurrentSolidCoreWithCodeSemanticCoverage coverage ∨
    CurrentSolidCoreWithObjectDataSemanticCoverage coverage ∨
    CurrentSolidCoreWithContextSemanticCoverage coverage ∨
    CurrentSolidCoreWithExternalQuerySemanticCoverage coverage ∨
    CurrentSolidCoreWithTransientStorageSemanticCoverage coverage ∨
    CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage coverage ∨
    CurrentSolidCoreWithCompilerArtifactsSemanticCoverage coverage

def CurrentSolidityEmittableNoVerbatimSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage ∨
    CurrentSolidCoreWithExternalCallsSemanticCoverage coverage

def CurrentSolidityEmittableWithVerbatimSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage ∨
    CurrentSolidCoreWithVerbatimSemanticCoverage coverage

def CurrentSolidityEmittableWithLoweringEnvironmentSemanticCoverage
    (coverage : Evm.SemanticCoverage) : Prop :=
  CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage ∨
    CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage coverage

theorem CompilerProfile.MemoryBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithMemorySemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithMemorySemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.MemoryCopyBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryCopyBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithMemoryCopySemanticCoverage
      builtin := by
  cases h
  exact
    ⟨Evm.SemanticCoverage.memoryCopy, rfl,
      Or.inr rfl⟩

theorem CompilerProfile.MemoryHashBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryHashBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithMemoryHashSemanticCoverage
      builtin := by
  cases h
  exact
    ⟨Evm.SemanticCoverage.memoryHash, rfl,
      Or.inr rfl⟩

theorem CompilerProfile.BufferBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.BufferBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithBufferSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithBufferSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.ReturnDataBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ReturnDataBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithReturnDataSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithReturnDataSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.CodeBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CodeBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithCodeSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithCodeSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.ObjectDataBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ObjectDataBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithObjectDataSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithObjectDataSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.ContextWordBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ContextWordBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithContextSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithContextSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.CompilerAnnotationBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CompilerAnnotationBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.CompilerArtifactBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CompilerArtifactBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.VerbatimBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.VerbatimBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithVerbatimSemanticCoverage builtin := by
  cases h
  exact
    ⟨Evm.SemanticCoverage.verbatim, rfl,
      Or.inr rfl⟩

theorem CompilerProfile.LoweringEnvironmentBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.LoweringEnvironmentBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage builtin := by
  cases h <;>
    exact
      ⟨Evm.SemanticCoverage.loweringEnvironment, rfl,
        Or.inr rfl⟩

theorem CompilerProfile.ExternalCallBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ExternalCallBuiltin builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreWithExternalCallsSemanticCoverage
      builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithExternalCallsSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.ExternalQueryBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ExternalQueryBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithExternalQuerySemanticCoverage builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithExternalQuerySemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.TransientStorageBuiltin.coverageEvidence_current
    {builtin : Evm.Builtin}
    (h : CompilerProfile.TransientStorageBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithTransientStorageSemanticCoverage builtin := by
  cases h <;>
    simp [BuiltinCoverageEvidence,
      CurrentSolidCoreWithTransientStorageSemanticCoverage,
      CurrentSolidCoreSemanticCoverage, Evm.Builtin.semanticCoverage?]

theorem CompilerProfile.builtinOK_semanticEvidence
    (profile : CompilerProfile)
    {builtin : Evm.Builtin}
    (h : profile.builtinOK builtin) :
    BuiltinSemanticEvidence builtin := by
  rcases profile.builtinOK_signature h with ⟨sig, hSig⟩
  exact
    ⟨⟨sig, hSig⟩,
      Evm.Builtin.claim?_of_signature? hSig,
      Evm.Builtin.semanticCoverage?_of_signature? hSig⟩

mutual
  def ExprBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : Expr -> Prop
    | Expr.value _ => True
    | Expr.var _ => True
    | Expr.keccak _ => True
    | Expr.dataSize _ => True
    | Expr.dataOffset _ => True
    | Expr.builtin builtin args =>
        builtinEvidence builtin ∧ ExprsBuiltinEvidence builtinEvidence args

  def ExprsBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : List Expr -> Prop
    | [] => True
    | expr :: rest =>
        ExprBuiltinEvidence builtinEvidence expr ∧
          ExprsBuiltinEvidence builtinEvidence rest
end

abbrev ExprBuiltinSemanticEvidence : Expr -> Prop :=
  ExprBuiltinEvidence BuiltinSemanticEvidence

abbrev ExprsBuiltinSemanticEvidence : List Expr -> Prop :=
  ExprsBuiltinEvidence BuiltinSemanticEvidence

abbrev ExprBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : Expr -> Prop :=
  ExprBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev ExprsBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : List Expr -> Prop :=
  ExprsBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev ExprBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : Expr -> Prop :=
  ExprBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev ExprsBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : List Expr -> Prop :=
  ExprsBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev ExprNoOpaqueEvidence : Expr -> Prop :=
  ExprBuiltinEvidence BuiltinNotOpaque

abbrev ExprsNoOpaqueEvidence : List Expr -> Prop :=
  ExprsBuiltinEvidence BuiltinNotOpaque

abbrev ExprCanonicalSolidityEmittableBoundaryEvidence : Expr -> Prop :=
  ExprBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

abbrev ExprsCanonicalSolidityEmittableBoundaryEvidence :
    List Expr -> Prop :=
  ExprsBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

mutual
  def StmtBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : Stmt -> Prop
    | Stmt.skip => True
    | Stmt.expr expr => ExprBuiltinEvidence builtinEvidence expr
    | Stmt.let1 _ none => True
    | Stmt.let1 _ (some expr) => ExprBuiltinEvidence builtinEvidence expr
    | Stmt.letMany _ none => True
    | Stmt.letMany _ (some exprs) =>
        ExprsBuiltinEvidence builtinEvidence exprs
    | Stmt.funDef _ _ _ body => StmtBuiltinEvidence builtinEvidence body
    | Stmt.assign _ expr => ExprBuiltinEvidence builtinEvidence expr
    | Stmt.assignMany _ exprs => ExprsBuiltinEvidence builtinEvidence exprs
    | Stmt.letCall _ _ args => ExprsBuiltinEvidence builtinEvidence args
    | Stmt.assignCall _ _ args => ExprsBuiltinEvidence builtinEvidence args
    | Stmt.seq first second =>
        StmtBuiltinEvidence builtinEvidence first ∧
          StmtBuiltinEvidence builtinEvidence second
    | Stmt.block stmts => BlockBuiltinEvidence builtinEvidence stmts
    | Stmt.ifThen cond body =>
        ExprBuiltinEvidence builtinEvidence cond ∧
          StmtBuiltinEvidence builtinEvidence body
    | Stmt.switch discr cases defaultBranch =>
        ExprBuiltinEvidence builtinEvidence discr ∧
          SwitchCasesBuiltinEvidence builtinEvidence cases ∧
            OptionalStmtBuiltinEvidence builtinEvidence defaultBranch
    | Stmt.forLoop pre cond post body =>
        StmtBuiltinEvidence builtinEvidence pre ∧
          ExprBuiltinEvidence builtinEvidence cond ∧
            StmtBuiltinEvidence builtinEvidence post ∧
              StmtBuiltinEvidence builtinEvidence body
    | Stmt.break => True
    | Stmt.continue => True
    | Stmt.leave => True

  def BlockBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : List Stmt -> Prop
    | [] => True
    | stmt :: rest =>
        StmtBuiltinEvidence builtinEvidence stmt ∧
          BlockBuiltinEvidence builtinEvidence rest

  def SwitchCasesBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : List (Value × Stmt) -> Prop
    | [] => True
    | (_, branch) :: rest =>
        StmtBuiltinEvidence builtinEvidence branch ∧
          SwitchCasesBuiltinEvidence builtinEvidence rest

  def OptionalStmtBuiltinEvidence
      (builtinEvidence : Evm.Builtin -> Prop) : Option Stmt -> Prop
    | none => True
    | some stmt => StmtBuiltinEvidence builtinEvidence stmt
end

abbrev StmtBuiltinSemanticEvidence : Stmt -> Prop :=
  StmtBuiltinEvidence BuiltinSemanticEvidence

abbrev BlockBuiltinSemanticEvidence : List Stmt -> Prop :=
  BlockBuiltinEvidence BuiltinSemanticEvidence

abbrev SwitchCasesBuiltinSemanticEvidence : List (Value × Stmt) -> Prop :=
  SwitchCasesBuiltinEvidence BuiltinSemanticEvidence

abbrev OptionalStmtBuiltinSemanticEvidence : Option Stmt -> Prop :=
  OptionalStmtBuiltinEvidence BuiltinSemanticEvidence

abbrev StmtBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : Stmt -> Prop :=
  StmtBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev BlockBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : List Stmt -> Prop :=
  BlockBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev SwitchCasesBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : List (Value × Stmt) -> Prop :=
  SwitchCasesBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev OptionalStmtBuiltinClaimEvidence
    (claimOK : Evm.ClaimKind -> Prop) : Option Stmt -> Prop :=
  OptionalStmtBuiltinEvidence (BuiltinClaimEvidence claimOK)

abbrev StmtBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : Stmt -> Prop :=
  StmtBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev BlockBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : List Stmt -> Prop :=
  BlockBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev SwitchCasesBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : List (Value × Stmt) -> Prop :=
  SwitchCasesBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev OptionalStmtBuiltinCoverageEvidence
    (coverageOK : Evm.SemanticCoverage -> Prop) : Option Stmt -> Prop :=
  OptionalStmtBuiltinEvidence (BuiltinCoverageEvidence coverageOK)

abbrev StmtNoOpaqueEvidence : Stmt -> Prop :=
  StmtBuiltinEvidence BuiltinNotOpaque

abbrev BlockNoOpaqueEvidence : List Stmt -> Prop :=
  BlockBuiltinEvidence BuiltinNotOpaque

abbrev SwitchCasesNoOpaqueEvidence : List (Value × Stmt) -> Prop :=
  SwitchCasesBuiltinEvidence BuiltinNotOpaque

abbrev OptionalStmtNoOpaqueEvidence : Option Stmt -> Prop :=
  OptionalStmtBuiltinEvidence BuiltinNotOpaque

abbrev StmtCanonicalSolidityEmittableBoundaryEvidence : Stmt -> Prop :=
  StmtBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

abbrev BlockCanonicalSolidityEmittableBoundaryEvidence
    : List Stmt -> Prop :=
  BlockBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

abbrev SwitchCasesCanonicalSolidityEmittableBoundaryEvidence
    : List (Value × Stmt) -> Prop :=
  SwitchCasesBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

abbrev OptionalStmtCanonicalSolidityEmittableBoundaryEvidence
    : Option Stmt -> Prop :=
  OptionalStmtBuiltinEvidence BuiltinCanonicalSolidityEmittableBoundary

theorem BuiltinClaimEvidence.mono
    {source target : Evm.ClaimKind -> Prop}
    (hImp : ∀ {claim : Evm.ClaimKind}, source claim -> target claim)
    {builtin : Evm.Builtin}
    (h : BuiltinClaimEvidence source builtin) :
    BuiltinClaimEvidence target builtin := by
  rcases h with ⟨claim, hClaim, hOK⟩
  exact ⟨claim, hClaim, hImp hOK⟩

theorem BuiltinCoverageEvidence.mono
    {source target : Evm.SemanticCoverage -> Prop}
    (hImp :
      ∀ {coverage : Evm.SemanticCoverage}, source coverage ->
        target coverage)
    {builtin : Evm.Builtin}
    (h : BuiltinCoverageEvidence source builtin) :
    BuiltinCoverageEvidence target builtin := by
  rcases h with ⟨coverage, hCoverage, hOK⟩
  exact ⟨coverage, hCoverage, hImp hOK⟩

theorem ExactYulClaim.to_exactOrAbstractedClaim
    {claim : Evm.ClaimKind}
    (h : ExactYulClaim claim) :
    ExactOrAbstractedClaim claim :=
  Or.inl h

theorem ExactYulClaim.to_exactAbstractedOrSymbolicClaim
    {claim : Evm.ClaimKind}
    (h : ExactYulClaim claim) :
    ExactAbstractedOrSymbolicClaim claim :=
  Or.inl h

theorem ExactOrAbstractedClaim.to_exactAbstractedOrSymbolicClaim
    {claim : Evm.ClaimKind}
    (h : ExactOrAbstractedClaim claim) :
    ExactAbstractedOrSymbolicClaim claim := by
  cases h with
  | inl hExact => exact Or.inl hExact
  | inr hAbstracted => exact Or.inr (Or.inl hAbstracted)

theorem ExactAbstractedOrSymbolicClaim.to_exactAbstractedSymbolicOrDeferredClaim
    {claim : Evm.ClaimKind}
    (h : ExactAbstractedOrSymbolicClaim claim) :
    ExactAbstractedSymbolicOrDeferredClaim claim := by
  cases h with
  | inl hExact => exact Or.inl hExact
  | inr hRest =>
      cases hRest with
      | inl hAbstracted => exact Or.inr (Or.inl hAbstracted)
      | inr hSymbolic => exact Or.inr (Or.inr (Or.inl hSymbolic))

theorem ExactYulClaim.to_nonDeferredClaim
    {claim : Evm.ClaimKind}
    (h : ExactYulClaim claim) :
    NonDeferredClaim claim := by
  cases h
  intro hDeferred
  cases hDeferred

theorem ExactOrAbstractedClaim.to_nonDeferredClaim
    {claim : Evm.ClaimKind}
    (h : ExactOrAbstractedClaim claim) :
    NonDeferredClaim claim := by
  cases h with
  | inl hExact =>
      exact ExactYulClaim.to_nonDeferredClaim hExact
  | inr hAbstracted =>
      cases hAbstracted
      intro hDeferred
      cases hDeferred

theorem ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim
    {claim : Evm.ClaimKind}
    (h : ExactAbstractedOrSymbolicClaim claim) :
    NonDeferredClaim claim := by
  cases h with
  | inl hExact =>
      exact ExactYulClaim.to_nonDeferredClaim hExact
  | inr hRest =>
      cases hRest with
      | inl hAbstracted =>
          exact
            ExactOrAbstractedClaim.to_nonDeferredClaim
              (Or.inr hAbstracted)
      | inr hSymbolic =>
          cases hSymbolic
          intro hDeferred
          cases hDeferred

theorem CurrentSolidCoreSemanticCoverage.to_withExternalCalls
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithExternalCallsSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withMemoryBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithMemorySemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withMemoryHashBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithMemoryHashSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withMemoryCopyBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithMemoryCopySemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withBufferBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithBufferSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withReturnDataBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithReturnDataSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withCodeBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithCodeSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withObjectDataBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithObjectDataSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withContextBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithContextSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withCompilerAnnotations
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withCompilerArtifacts
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithCompilerArtifactsSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithVerbatimSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withLoweringEnvironment
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withExternalQueryBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithExternalQuerySemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreSemanticCoverage.to_withTransientStorageBuiltins
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreSemanticCoverage coverage) :
    CurrentSolidCoreWithTransientStorageSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreWithMemorySemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithMemorySemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithMemoryCopySemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithMemoryCopySemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithMemoryHashSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithMemoryHashSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithBufferSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithBufferSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithReturnDataSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithReturnDataSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithCodeSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithCodeSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithObjectDataSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithObjectDataSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithContextSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithContextSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithExternalQuerySemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithExternalQuerySemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithTransientStorageSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithTransientStorageSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidCoreWithCompilerArtifactsSemanticCoverage.to_solidityNoExternalNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithCompilerArtifactsSemanticCoverage coverage) :
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      coverage := by
  simp [CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage, h]

theorem CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage.to_noVerbatim
    {coverage : Evm.SemanticCoverage}
    (h :
      CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
        coverage) :
    CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidCoreWithExternalCallsSemanticCoverage.to_solidityNoVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithExternalCallsSemanticCoverage coverage) :
    CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage :=
  Or.inr h

theorem CurrentSolidityEmittableNoVerbatimSemanticCoverage.to_withVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage) :
    CurrentSolidityEmittableWithVerbatimSemanticCoverage coverage :=
  Or.inl h

theorem CurrentSolidityEmittableNoVerbatimSemanticCoverage.to_withLoweringEnvironment
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidityEmittableNoVerbatimSemanticCoverage coverage) :
    CurrentSolidityEmittableWithLoweringEnvironmentSemanticCoverage
      coverage :=
  Or.inl h

theorem CurrentSolidCoreWithVerbatimSemanticCoverage.to_solidityWithVerbatim
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithVerbatimSemanticCoverage coverage) :
    CurrentSolidityEmittableWithVerbatimSemanticCoverage coverage :=
  Or.inr h

theorem CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage.to_solidityWithLoweringEnvironment
    {coverage : Evm.SemanticCoverage}
    (h : CurrentSolidCoreWithLoweringEnvironmentSemanticCoverage coverage) :
    CurrentSolidityEmittableWithLoweringEnvironmentSemanticCoverage
      coverage :=
  Or.inr h

mutual
  theorem ExprBuiltinEvidence.mono
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      ∀ {expr : Expr},
        ExprBuiltinEvidence source expr ->
          ExprBuiltinEvidence target expr
    | Expr.value _, _ => trivial
    | Expr.var _, _ => trivial
    | Expr.keccak _, _ => trivial
    | Expr.dataSize _, _ => trivial
    | Expr.dataOffset _, _ => trivial
    | Expr.builtin _ _, h =>
        ⟨hImp h.1, ExprsBuiltinEvidence.mono hImp h.2⟩

  theorem ExprsBuiltinEvidence.mono
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      ∀ {exprs : List Expr},
        ExprsBuiltinEvidence source exprs ->
          ExprsBuiltinEvidence target exprs
    | [], _ => trivial
    | _ :: _, h =>
        ⟨ExprBuiltinEvidence.mono hImp h.1,
          ExprsBuiltinEvidence.mono hImp h.2⟩
end

mutual
  private theorem stmtBuiltinEvidenceMonoAux
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      (stmt : Stmt) ->
        StmtBuiltinEvidence source stmt ->
          StmtBuiltinEvidence target stmt
    | Stmt.skip, _ => trivial
    | Stmt.expr _, h => ExprBuiltinEvidence.mono hImp h
    | Stmt.let1 _ none, _ => trivial
    | Stmt.let1 _ (some _), h => ExprBuiltinEvidence.mono hImp h
    | Stmt.letMany _ none, _ => trivial
    | Stmt.letMany _ (some _), h => ExprsBuiltinEvidence.mono hImp h
    | Stmt.funDef _ _ _ body, h => stmtBuiltinEvidenceMonoAux hImp body h
    | Stmt.assign _ _, h => ExprBuiltinEvidence.mono hImp h
    | Stmt.assignMany _ _, h => ExprsBuiltinEvidence.mono hImp h
    | Stmt.letCall _ _ _, h => ExprsBuiltinEvidence.mono hImp h
    | Stmt.assignCall _ _ _, h => ExprsBuiltinEvidence.mono hImp h
    | Stmt.seq first second, h =>
        ⟨stmtBuiltinEvidenceMonoAux hImp first h.1,
          stmtBuiltinEvidenceMonoAux hImp second h.2⟩
    | Stmt.block stmts, h => blockBuiltinEvidenceMonoAux hImp stmts h
    | Stmt.ifThen _ body, h =>
        ⟨ExprBuiltinEvidence.mono hImp h.1,
          stmtBuiltinEvidenceMonoAux hImp body h.2⟩
    | Stmt.switch _ cases defaultBranch, h =>
        ⟨ExprBuiltinEvidence.mono hImp h.1,
          switchCasesBuiltinEvidenceMonoAux hImp cases h.2.1,
          optionalStmtBuiltinEvidenceMonoAux hImp defaultBranch h.2.2⟩
    | Stmt.forLoop pre _ post body, h =>
        ⟨stmtBuiltinEvidenceMonoAux hImp pre h.1,
          ExprBuiltinEvidence.mono hImp h.2.1,
          stmtBuiltinEvidenceMonoAux hImp post h.2.2.1,
          stmtBuiltinEvidenceMonoAux hImp body h.2.2.2⟩
    | Stmt.break, _ => trivial
    | Stmt.continue, _ => trivial
    | Stmt.leave, _ => trivial

  private theorem blockBuiltinEvidenceMonoAux
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      (stmts : List Stmt) ->
        BlockBuiltinEvidence source stmts ->
          BlockBuiltinEvidence target stmts
    | [], _ => trivial
    | stmt :: rest, h =>
        ⟨stmtBuiltinEvidenceMonoAux hImp stmt h.1,
          blockBuiltinEvidenceMonoAux hImp rest h.2⟩

  private theorem switchCasesBuiltinEvidenceMonoAux
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      (cases : List (Value × Stmt)) ->
        SwitchCasesBuiltinEvidence source cases ->
          SwitchCasesBuiltinEvidence target cases
    | [], _ => trivial
    | (_, branch) :: rest, h =>
        ⟨stmtBuiltinEvidenceMonoAux hImp branch h.1,
          switchCasesBuiltinEvidenceMonoAux hImp rest h.2⟩

  private theorem optionalStmtBuiltinEvidenceMonoAux
      {source target : Evm.Builtin -> Prop}
      (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin) :
      (stmt? : Option Stmt) ->
        OptionalStmtBuiltinEvidence source stmt? ->
          OptionalStmtBuiltinEvidence target stmt?
    | none, _ => trivial
    | some stmt, h => stmtBuiltinEvidenceMonoAux hImp stmt h
end

theorem StmtBuiltinEvidence.mono
    {source target : Evm.Builtin -> Prop}
    (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin)
    {stmt : Stmt}
    (h : StmtBuiltinEvidence source stmt) :
    StmtBuiltinEvidence target stmt :=
  stmtBuiltinEvidenceMonoAux hImp stmt h

theorem BlockBuiltinEvidence.mono
    {source target : Evm.Builtin -> Prop}
    (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin)
    {stmts : List Stmt}
    (h : BlockBuiltinEvidence source stmts) :
    BlockBuiltinEvidence target stmts :=
  blockBuiltinEvidenceMonoAux hImp stmts h

theorem SwitchCasesBuiltinEvidence.mono
    {source target : Evm.Builtin -> Prop}
    (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin)
    {cases : List (Value × Stmt)}
    (h : SwitchCasesBuiltinEvidence source cases) :
    SwitchCasesBuiltinEvidence target cases :=
  switchCasesBuiltinEvidenceMonoAux hImp cases h

theorem OptionalStmtBuiltinEvidence.mono
    {source target : Evm.Builtin -> Prop}
    (hImp : ∀ {builtin : Evm.Builtin}, source builtin -> target builtin)
    {stmt? : Option Stmt}
    (h : OptionalStmtBuiltinEvidence source stmt?) :
    OptionalStmtBuiltinEvidence target stmt? :=
  optionalStmtBuiltinEvidenceMonoAux hImp stmt? h

theorem StmtBuiltinClaimEvidence.exactYul_to_exactOrAbstracted
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactYulClaim stmt) :
    StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim => ExactYulClaim.to_exactOrAbstractedClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinClaimEvidence.exactYul_to_exactAbstractedOrSymbolic
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactYulClaim stmt) :
    StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim => ExactYulClaim.to_exactAbstractedOrSymbolicClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinClaimEvidence.exactOrAbstracted_to_exactAbstractedOrSymbolic
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt) :
    StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim =>
          ExactOrAbstractedClaim.to_exactAbstractedOrSymbolicClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinClaimEvidence.exactYul_to_nonDeferred
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactYulClaim stmt) :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinClaimEvidence.exactOrAbstracted_to_nonDeferred
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt) :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim => ExactOrAbstractedClaim.to_nonDeferredClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinClaimEvidence.exactAbstractedOrSymbolic_to_nonDeferred
    {stmt : Stmt}
    (h : StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt) :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinClaimEvidence.mono
        (fun hClaim =>
          ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withExternalCalls
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithExternalCallsSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withExternalCalls hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withMemoryBuiltins
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemorySemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withMemoryBuiltins hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withMemoryHashBuiltins
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemoryHashSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withMemoryHashBuiltins hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withBufferBuiltins
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithBufferSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withBufferBuiltins hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withObjectDataBuiltins
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithObjectDataSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withObjectDataBuiltins hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withContextBuiltins
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithContextSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withContextBuiltins hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withCompilerAnnotations
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withCompilerAnnotations
            hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withCompilerArtifacts
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withCompilerArtifacts
            hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withVerbatim
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithVerbatimSemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withVerbatim hCoverage)
        hBuiltin)
    h

theorem StmtBuiltinCoverageEvidence.currentSolidCore_to_withExternalQuery
    {stmt : Stmt}
    (h : StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt) :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithExternalQuerySemanticCoverage stmt :=
  StmtBuiltinEvidence.mono
    (fun hBuiltin =>
      BuiltinCoverageEvidence.mono
        (fun hCoverage =>
          CurrentSolidCoreSemanticCoverage.to_withExternalQueryBuiltins
            hCoverage)
        hBuiltin)
    h

mutual
  theorem CompilerEmittableExpr.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {expr : Expr},
        CompilerEmittableExpr profile expr ->
          ExprBuiltinEvidence builtinEvidence expr
    | _, CompilerEmittableExpr.value _ => trivial
    | _, CompilerEmittableExpr.var _ => trivial
    | _, CompilerEmittableExpr.keccak _ => trivial
    | _, CompilerEmittableExpr.dataSize _ => trivial
    | _, CompilerEmittableExpr.dataOffset _ => trivial
    | _, CompilerEmittableExpr.builtin hBuiltinOK hArgs =>
        ⟨ hProfileBuiltin hBuiltinOK
        , CompilerEmittableExprs.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hArgs ⟩

  theorem CompilerEmittableExprs.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {exprs : List Expr},
        CompilerEmittableExprs profile exprs ->
          ExprsBuiltinEvidence builtinEvidence exprs
    | _, CompilerEmittableExprs.nil => trivial
    | _, CompilerEmittableExprs.cons hExpr hRest =>
        ⟨ CompilerEmittableExpr.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hExpr
        , CompilerEmittableExprs.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hRest ⟩
end

theorem CompilerEmittableExpr.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {expr : Expr},
      CompilerEmittableExpr profile expr ->
        ExprBuiltinSemanticEvidence expr :=
  CompilerEmittableExpr.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerEmittableExprs.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {exprs : List Expr},
      CompilerEmittableExprs profile exprs ->
        ExprsBuiltinSemanticEvidence exprs :=
  CompilerEmittableExprs.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

mutual
  theorem CompilerEmittableStmt.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {stmt : Stmt},
        CompilerEmittableStmt profile stmt ->
          StmtBuiltinEvidence builtinEvidence stmt
    | _, CompilerEmittableStmt.skip => trivial
    | _, CompilerEmittableStmt.expr hExpr =>
        CompilerEmittableExpr.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hExpr
    | _, CompilerEmittableStmt.let1None => trivial
    | _, CompilerEmittableStmt.let1Some hExpr =>
        CompilerEmittableExpr.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hExpr
    | _, CompilerEmittableStmt.letManyNone => trivial
    | _, CompilerEmittableStmt.letManySome hExprs =>
        CompilerEmittableExprs.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hExprs
    | _, CompilerEmittableStmt.funDef _ hBody =>
        by
          simpa using
            (CompilerEmittableStmt.builtinEvidence
              (profile := profile) (builtinEvidence := builtinEvidence)
              hProfileBuiltin hBody)
    | _, CompilerEmittableStmt.assign hExpr =>
        CompilerEmittableExpr.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hExpr
    | _, CompilerEmittableStmt.assignMany hExprs =>
        CompilerEmittableExprs.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hExprs
    | _, CompilerEmittableStmt.letCall _ hArgs =>
        CompilerEmittableExprs.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hArgs
    | _, CompilerEmittableStmt.assignCall _ hArgs =>
        CompilerEmittableExprs.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hArgs
    | _, CompilerEmittableStmt.seq hFirst hSecond =>
        ⟨ CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hFirst
        , CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hSecond ⟩
    | _, CompilerEmittableStmt.block hBlock =>
        CompilerEmittableBlock.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hBlock
    | _, CompilerEmittableStmt.ifThen hCond hBody =>
        ⟨ CompilerEmittableExpr.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hCond
        , CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hBody ⟩
    | _, CompilerEmittableStmt.switch _ hDiscr hCases hDefault =>
        ⟨ CompilerEmittableExpr.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hDiscr
        , CompilerEmittableSwitchCases.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hCases
        , CompilerEmittableOptionalStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hDefault ⟩
    | _, CompilerEmittableStmt.forLoop hPre hCond hPost hBody =>
        ⟨ CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hPre
        , CompilerEmittableExpr.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hCond
        , CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hPost
        , CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hBody ⟩
    | _, CompilerEmittableStmt.break => trivial
    | _, CompilerEmittableStmt.continue => trivial
    | _, CompilerEmittableStmt.leave => trivial

  theorem CompilerEmittableBlock.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {stmts : List Stmt},
        CompilerEmittableBlock profile stmts ->
          BlockBuiltinEvidence builtinEvidence stmts
    | _, CompilerEmittableBlock.nil => trivial
    | _, CompilerEmittableBlock.cons hStmt hRest =>
        ⟨ CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hStmt
        , CompilerEmittableBlock.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hRest ⟩

  theorem CompilerEmittableSwitchCases.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {cases : List (Value × Stmt)},
        CompilerEmittableSwitchCases profile cases ->
          SwitchCasesBuiltinEvidence builtinEvidence cases
    | _, CompilerEmittableSwitchCases.nil => trivial
    | _, CompilerEmittableSwitchCases.cons _ hBranch hRest =>
        ⟨ CompilerEmittableStmt.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hBranch
        , CompilerEmittableSwitchCases.builtinEvidence
            (profile := profile) (builtinEvidence := builtinEvidence)
            hProfileBuiltin hRest ⟩

  theorem CompilerEmittableOptionalStmt.builtinEvidence
      {profile : CompilerProfile}
      {builtinEvidence : Evm.Builtin -> Prop}
      (hProfileBuiltin :
        ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
          builtinEvidence builtin) :
      ∀ {stmt? : Option Stmt},
        CompilerEmittableOptionalStmt profile stmt? ->
          OptionalStmtBuiltinEvidence builtinEvidence stmt?
    | _, CompilerEmittableOptionalStmt.none => trivial
    | _, CompilerEmittableOptionalStmt.some hStmt =>
        CompilerEmittableStmt.builtinEvidence
          (profile := profile) (builtinEvidence := builtinEvidence)
          hProfileBuiltin hStmt
end

theorem CompilerEmittableStmt.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt profile stmt ->
        StmtBuiltinSemanticEvidence stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerEmittableBlock.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {stmts : List Stmt},
      CompilerEmittableBlock profile stmts ->
        BlockBuiltinSemanticEvidence stmts :=
  CompilerEmittableBlock.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerEmittableSwitchCases.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {cases : List (Value × Stmt)},
      CompilerEmittableSwitchCases profile cases ->
        SwitchCasesBuiltinSemanticEvidence cases :=
  CompilerEmittableSwitchCases.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerEmittableOptionalStmt.builtinSemanticEvidence
    {profile : CompilerProfile} :
    ∀ {stmt? : Option Stmt},
      CompilerEmittableOptionalStmt profile stmt? ->
        OptionalStmtBuiltinSemanticEvidence stmt? :=
  CompilerEmittableOptionalStmt.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinSemanticEvidence)
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerEmittableExpr.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {expr : Expr},
      CompilerEmittableExpr profile expr ->
        ExprNoOpaqueEvidence expr :=
  CompilerEmittableExpr.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerEmittableExprs.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {exprs : List Expr},
      CompilerEmittableExprs profile exprs ->
        ExprsNoOpaqueEvidence exprs :=
  CompilerEmittableExprs.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerEmittableStmt.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt profile stmt ->
        StmtNoOpaqueEvidence stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerEmittableBlock.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {stmts : List Stmt},
      CompilerEmittableBlock profile stmts ->
        BlockNoOpaqueEvidence stmts :=
  CompilerEmittableBlock.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerEmittableSwitchCases.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {cases : List (Value × Stmt)},
      CompilerEmittableSwitchCases profile cases ->
        SwitchCasesNoOpaqueEvidence cases :=
  CompilerEmittableSwitchCases.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerEmittableOptionalStmt.noOpaqueEvidence
    {profile : CompilerProfile} :
    ∀ {stmt? : Option Stmt},
      CompilerEmittableOptionalStmt profile stmt? ->
        OptionalStmtNoOpaqueEvidence stmt? :=
  CompilerEmittableOptionalStmt.builtinEvidence
    (profile := profile)
    (builtinEvidence := BuiltinNotOpaque)
    (fun hBuiltin => CompilerProfile.builtinOK_notOpaque profile hBuiltin)

theorem CompilerProfile.currentSolidCore_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.builtinOK builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_builtin_claim_exactYul h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.builtinOK builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_builtinClaimEvidence_exactYul h)

theorem CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withMemoryBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withMemoryCopyBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryCopyBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withMemoryCopyBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withMemoryCopyBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryCopyBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withMemoryCopyBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryHashBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtin_claim_exact_or_symbolic
      h with
  | inl hExact =>
      exact
        ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hSymbolic =>
      exact
        ⟨Evm.ClaimKind.symbolic, hSymbolic, Or.inr (Or.inr rfl)⟩

theorem CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryHashBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim =>
      ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinClaimEvidence
      h)

theorem CompilerProfile.currentSolidCore_withBufferBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withBufferBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withBufferBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withBufferBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withBufferBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withBufferBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withReturnDataBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withReturnDataBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withReturnDataBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withReturnDataBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withReturnDataBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withReturnDataBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withCodeBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCodeBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withCodeBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withCodeBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCodeBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withCodeBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withObjectDataBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withObjectDataBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withContextBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withContextBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withContextBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withContextBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withContextBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withContextBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerAnnotations.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactOrAbstractedClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withCompilerAnnotations_builtin_claim_exact_or_abstracted
      h with
  | inl hExact =>
      exact ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hAbstracted =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin, hAbstracted, Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerAnnotations.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactOrAbstractedClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinClaimEvidence
      h)

theorem CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactOrAbstractedClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtin_claim_exact_or_abstracted
      h with
  | inl hExact =>
      exact ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hAbstracted =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin, hAbstracted, Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactOrAbstractedClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinClaimEvidence
      h)

theorem CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withVerbatimBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactOrAbstractedClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtin_claim_exact_or_abstracted
      h with
  | inl hExact =>
      exact ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hAbstracted =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin, hAbstracted, Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withVerbatimBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactOrAbstractedClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinClaimEvidence
      h)

theorem CompilerProfile.currentSolidCore_withExternalCalls_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalCalls.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactOrAbstractedClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withExternalCalls_builtin_claim_exact_or_abstracted
      h with
  | inl hExact =>
      exact ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hAbstracted =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin, hAbstracted, Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withExternalCalls_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalCalls.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactOrAbstractedClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withExternalCalls_builtinClaimEvidence h)

theorem CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalQueryBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin := by
  cases
    CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtin_claim_exact_abstracted_or_symbolic
      h with
  | inl hExact =>
      exact ⟨Evm.ClaimKind.exactYul, hExact, Or.inl rfl⟩
  | inr hRest =>
      cases hRest with
      | inl hAbstracted =>
          exact
            ⟨Evm.ClaimKind.abstractedBuiltin, hAbstracted,
              Or.inr (Or.inl rfl)⟩
      | inr hSymbolic =>
          exact
            ⟨Evm.ClaimKind.symbolic, hSymbolic,
              Or.inr (Or.inr rfl)⟩

theorem CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalQueryBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim =>
      ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtinClaimEvidence
      h)

theorem CompilerProfile.currentSolidCore_withTransientStorageBuiltins_builtinClaimEvidence_exactYul
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withTransientStorageBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence ExactYulClaim builtin :=
  ⟨Evm.ClaimKind.exactYul,
    CompilerProfile.currentSolidCore_withTransientStorageBuiltins_builtin_claim_exactYul
      h,
    rfl⟩

theorem CompilerProfile.currentSolidCore_withTransientStorageBuiltins_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withTransientStorageBuiltins.builtinOK
      builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  BuiltinClaimEvidence.mono
    (fun hClaim => ExactYulClaim.to_nonDeferredClaim hClaim)
    (CompilerProfile.currentSolidCore_withTransientStorageBuiltins_builtinClaimEvidence_exactYul
      h)

theorem CompilerProfile.currentSolidCore_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.builtinOK builtin) :
    BuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage builtin := by
  cases CompilerProfile.currentSolidCore_builtin_semanticCoverage_exact_lane h with
  | inl hPure =>
      exact
        ⟨Evm.SemanticCoverage.pureWord, hPure, Or.inl rfl⟩
  | inr hRest =>
      cases hRest with
      | inl hStorage =>
          exact
            ⟨Evm.SemanticCoverage.storage, hStorage,
              Or.inr (Or.inl rfl)⟩
      | inr hRest =>
          cases hRest with
          | inl hHalt =>
              exact
                ⟨Evm.SemanticCoverage.controlHalt, hHalt,
                  Or.inr (Or.inr (Or.inl rfl))⟩
          | inr hDiscard =>
              exact
                ⟨Evm.SemanticCoverage.discard, hDiscard,
                  Or.inr (Or.inr (Or.inr rfl))⟩

theorem CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithMemorySemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withMemoryBuiltins
  | inr hBuiltin =>
      cases hBuiltin with
      | mload =>
          exact
            ⟨Evm.SemanticCoverage.memoryRead, rfl,
              Or.inr (Or.inl rfl)⟩
      | mstore =>
          exact
            ⟨Evm.SemanticCoverage.memoryWrite, rfl,
              Or.inr (Or.inr rfl)⟩
      | mstore8 =>
          exact
            ⟨Evm.SemanticCoverage.memoryWrite, rfl,
              Or.inr (Or.inr rfl)⟩

theorem CompilerProfile.currentSolidCore_withMemoryCopyBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryCopyBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithMemoryCopySemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withMemoryCopyBuiltins
  | inr hBuiltin =>
      cases hBuiltin
      exact
        ⟨Evm.SemanticCoverage.memoryCopy, rfl,
          Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withMemoryHashBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithMemoryHashSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withMemoryHashBuiltins
  | inr hBuiltin =>
      cases hBuiltin
      exact
        ⟨Evm.SemanticCoverage.memoryHash, rfl,
          Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withBufferBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withBufferBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithBufferSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withBufferBuiltins
  | inr hBuiltin =>
      cases hBuiltin with
      | calldataloadOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferRead, rfl,
              Or.inr (Or.inl rfl)⟩
      | calldatasizeOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferSize, rfl,
              Or.inr (Or.inr (Or.inl rfl))⟩
      | calldatacopyOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferCopy, rfl,
              Or.inr (Or.inr (Or.inr rfl))⟩

theorem CompilerProfile.currentSolidCore_withReturnDataBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withReturnDataBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithReturnDataSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withReturnDataBuiltins
  | inr hBuiltin =>
      cases hBuiltin with
      | returndataloadOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferRead, rfl,
              Or.inr (Or.inl rfl)⟩
      | returndatasizeOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferSize, rfl,
              Or.inr (Or.inr (Or.inl rfl))⟩
      | returndatacopyOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferCopy, rfl,
              Or.inr (Or.inr (Or.inr rfl))⟩

theorem CompilerProfile.currentSolidCore_withCodeBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCodeBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithCodeSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withCodeBuiltins
  | inr hBuiltin =>
      cases hBuiltin with
      | codecopyOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferCopy, rfl,
              Or.inr (Or.inr rfl)⟩
      | codesizeOp =>
          exact
            ⟨Evm.SemanticCoverage.bufferSize, rfl,
              Or.inr (Or.inl rfl)⟩

theorem CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withObjectDataBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithObjectDataSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withObjectDataBuiltins
  | inr hBuiltin =>
      cases hBuiltin <;>
        exact
          ⟨Evm.SemanticCoverage.objectDataCopy, rfl,
            Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withContextBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withContextBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithContextSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withContextBuiltins
  | inr hBuiltin =>
      cases hBuiltin <;>
        exact
          ⟨Evm.SemanticCoverage.contextWord, rfl,
            Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerAnnotations.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withCompilerAnnotations
  | inr hBuiltin =>
      cases hBuiltin
      exact
        ⟨Evm.SemanticCoverage.compilerBuiltin, rfl,
          Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withCompilerArtifacts
  | inr hBuiltin =>
      cases hBuiltin <;>
        exact
          ⟨Evm.SemanticCoverage.compilerBuiltin, rfl,
            Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withVerbatimBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithVerbatimSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withVerbatim
  | inr hBuiltin =>
      cases hBuiltin
      exact
        ⟨Evm.SemanticCoverage.verbatim, rfl,
          Or.inr rfl⟩

theorem CompilerProfile.currentSolidCore_withExternalCalls_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalCalls.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithExternalCallsSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withExternalCalls
  | inr hBuiltin =>
      cases hBuiltin <;>
        first
        | exact
            ⟨Evm.SemanticCoverage.externalCall, rfl,
              Or.inr (Or.inl rfl)⟩
        | exact
            ⟨Evm.SemanticCoverage.log, rfl,
              Or.inr (Or.inr (Or.inl rfl))⟩
        | exact
            ⟨Evm.SemanticCoverage.contractCreation, rfl,
              Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
        | exact
            ⟨Evm.SemanticCoverage.selfdestruct, rfl,
              Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withExternalQueryBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithExternalQuerySemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withExternalQueryBuiltins
  | inr hBuiltin =>
      cases hBuiltin <;>
        first
        | exact
            ⟨Evm.SemanticCoverage.externalQuery, rfl,
              Or.inr (Or.inl rfl)⟩
        | exact
            ⟨Evm.SemanticCoverage.bufferCopy, rfl,
              Or.inr (Or.inr rfl)⟩

theorem CompilerProfile.currentSolidCore_withTransientStorageBuiltins_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidCore.withTransientStorageBuiltins.builtinOK
      builtin) :
    BuiltinCoverageEvidence
      CurrentSolidCoreWithTransientStorageSemanticCoverage builtin := by
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin).mono
          CurrentSolidCoreSemanticCoverage.to_withTransientStorageBuiltins
  | inr hBuiltin =>
      cases hBuiltin <;>
        exact
          ⟨Evm.SemanticCoverage.transientStorage, rfl,
            Or.inr rfl⟩

theorem CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim.builtinOK
        builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin := by
  simp [CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
    at h
  rcases h with h | hArtifact
  · rcases h with h | hAnnotation
    · rcases h with h | hTransient
      · rcases h with h | hExternalQuery
        · rcases h with h | hContext
          · rcases h with h | hObject
            · rcases h with h | hCode
              · rcases h with h | hReturnData
                · rcases h with h | hBuffer
                  · rcases h with h | hMemoryHash
                    · rcases h with h | hMemoryCopy
                      · rcases h with hCore | hMemory
                        · exact
                            (CompilerProfile.currentSolidCore_builtinClaimEvidence_exactYul
                              hCore).mono
                              (fun hClaim =>
                                ExactYulClaim.to_exactAbstractedOrSymbolicClaim
                                  hClaim)
                        · exact
                            ⟨Evm.ClaimKind.exactYul,
                              CompilerProfile.MemoryBuiltin.claim_exactYul
                                hMemory,
                              Or.inl rfl⟩
                      · exact
                          ⟨Evm.ClaimKind.exactYul,
                            CompilerProfile.MemoryCopyBuiltin.claim_exactYul
                              hMemoryCopy,
                            Or.inl rfl⟩
                    · exact
                        ⟨Evm.ClaimKind.symbolic,
                          CompilerProfile.MemoryHashBuiltin.claim_symbolic
                            hMemoryHash,
                          Or.inr (Or.inr rfl)⟩
                  · exact
                      ⟨Evm.ClaimKind.exactYul,
                        CompilerProfile.BufferBuiltin.claim_exactYul hBuffer,
                        Or.inl rfl⟩
                · exact
                    ⟨Evm.ClaimKind.exactYul,
                      CompilerProfile.ReturnDataBuiltin.claim_exactYul
                        hReturnData,
                      Or.inl rfl⟩
              · exact
                  ⟨Evm.ClaimKind.exactYul,
                    CompilerProfile.CodeBuiltin.claim_exactYul hCode,
                    Or.inl rfl⟩
            · exact
                ⟨Evm.ClaimKind.exactYul,
                  CompilerProfile.ObjectDataBuiltin.claim_exactYul hObject,
                  Or.inl rfl⟩
          · exact
              ⟨Evm.ClaimKind.exactYul,
                CompilerProfile.ContextWordBuiltin.claim_exactYul hContext,
                Or.inl rfl⟩
        · exact
            CompilerProfile.currentSolidCore_withExternalQueryBuiltins_builtinClaimEvidence
              (Or.inr hExternalQuery)
      · exact
          ⟨Evm.ClaimKind.exactYul,
            CompilerProfile.TransientStorageBuiltin.claim_exactYul hTransient,
            Or.inl rfl⟩
    · exact
        ⟨Evm.ClaimKind.abstractedBuiltin,
          CompilerProfile.CompilerAnnotationBuiltin.claim_abstracted
            hAnnotation,
          Or.inr (Or.inl rfl)⟩
  · exact
      ⟨Evm.ClaimKind.abstractedBuiltin,
        CompilerProfile.CompilerArtifactBuiltin.claim_abstracted hArtifact,
        Or.inr (Or.inl rfl)⟩

theorem CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim.builtinOK
        builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  (CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinClaimEvidence
    h).mono
    (fun hClaim =>
      ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)

theorem CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoVerbatim.builtinOK builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin := by
  simp [CompilerProfile.currentSolidityEmittableNoVerbatim] at h
  cases h with
  | inl hBuiltin =>
      exact
        CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinClaimEvidence
          hBuiltin
  | inr hExternal =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin,
          CompilerProfile.ExternalCallBuiltin.claim_abstracted hExternal,
          Or.inr (Or.inl rfl)⟩

theorem CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoVerbatim.builtinOK builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  (CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence h).mono
    (fun hClaim =>
      ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)

theorem CompilerProfile.currentSolidityEmittable_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidityEmittable.builtinOK builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin :=
  CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence h

theorem CompilerProfile.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidityEmittable.builtinOK builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence_nonDeferred
    h

theorem CompilerProfile.currentSolidityEmittableNoVerbatim_noDeferredClaims
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoVerbatim.builtinOK builtin) :
    builtin.claim? ≠ some Evm.ClaimKind.deferredToLowering := by
  intro hDeferred
  rcases
    CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence_nonDeferred
      h with
    ⟨claim, hClaim, hNonDeferred⟩
  have hSome : some claim = some Evm.ClaimKind.deferredToLowering :=
    hClaim.symm.trans hDeferred
  cases hSome
  exact hNonDeferred rfl

theorem CompilerProfile.currentSolidityEmittable_noDeferredClaims
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidityEmittable.builtinOK builtin) :
    builtin.claim? ≠ some Evm.ClaimKind.deferredToLowering :=
  CompilerProfile.currentSolidityEmittableNoVerbatim_noDeferredClaims h

theorem CompilerProfile.currentSolidityEmittable_excludes_gasOp :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.gasOp := by
  intro h
  exact
    (CompilerProfile.currentSolidityEmittable_noDeferredClaims h)
      Evm.Builtin.gas_claim_deferred

theorem CompilerProfile.currentSolidityEmittable_excludes_pcOp :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK
      Evm.Builtin.pcOp := by
  intro h
  exact
    (CompilerProfile.currentSolidityEmittable_noDeferredClaims h)
      Evm.Builtin.pc_claim_deferred

theorem CompilerProfile.currentSolidityEmittable_excludes_opaque (id : Nat) :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK
      (Evm.Builtin.opaque id) :=
  CompilerProfile.excludes_opaque
    CompilerProfile.currentSolidityEmittable id

theorem CompilerProfile.currentSolidityEmittableWithVerbatim_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithVerbatim.builtinOK
        builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin := by
  simp [CompilerProfile.currentSolidityEmittableWithVerbatim] at h
  cases h with
  | inl hBuiltin =>
      exact
        CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence
          hBuiltin
  | inr hVerbatim =>
      exact
        ⟨Evm.ClaimKind.abstractedBuiltin,
          CompilerProfile.VerbatimBuiltin.claim_abstracted hVerbatim,
          Or.inr (Or.inl rfl)⟩

theorem CompilerProfile.currentSolidityEmittableWithVerbatim_builtinClaimEvidence_nonDeferred
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithVerbatim.builtinOK
        builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  (CompilerProfile.currentSolidityEmittableWithVerbatim_builtinClaimEvidence
    h).mono
    (fun hClaim =>
      ExactAbstractedOrSymbolicClaim.to_nonDeferredClaim hClaim)

theorem CompilerProfile.currentSolidityEmittableWithLoweringEnvironment_builtinClaimEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
        builtin) :
    BuiltinClaimEvidence ExactAbstractedSymbolicOrDeferredClaim
      builtin := by
  simp [CompilerProfile.currentSolidityEmittableWithLoweringEnvironment]
    at h
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidityEmittableNoVerbatim_builtinClaimEvidence
          hBuiltin).mono
          (fun hClaim =>
            ExactAbstractedOrSymbolicClaim.to_exactAbstractedSymbolicOrDeferredClaim
              hClaim)
  | inr hLowering =>
      exact
        ⟨Evm.ClaimKind.deferredToLowering,
          CompilerProfile.LoweringEnvironmentBuiltin.claim_deferred hLowering,
          Or.inr (Or.inr (Or.inr rfl))⟩

theorem CompilerProfile.currentSolidityEmittableWithLoweringEnvironment_deferredClaims_only_gas_or_pc
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
        builtin)
    (hDeferred :
      builtin.claim? = some Evm.ClaimKind.deferredToLowering) :
    builtin = Evm.Builtin.gasOp ∨ builtin = Evm.Builtin.pcOp := by
  simp [CompilerProfile.currentSolidityEmittableWithLoweringEnvironment] at h
  cases h with
  | inl hBuiltin =>
      exact
        False.elim
          ((CompilerProfile.currentSolidityEmittableNoVerbatim_noDeferredClaims
              hBuiltin)
            hDeferred)
  | inr hLowering =>
      cases hLowering with
      | gasOp => exact Or.inl rfl
      | pcOp => exact Or.inr rfl

theorem CompilerProfile.currentSolidityEmittableWithLoweringEnvironment_deferredBuiltinBoundary
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
        builtin) :
    DeferredBuiltinOnlyGasOrPc builtin :=
  CompilerProfile.currentSolidityEmittableWithLoweringEnvironment_deferredClaims_only_gas_or_pc
    h

theorem CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim.builtinOK
        builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage
      builtin := by
  simp [CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim]
    at h
  rcases h with h | hArtifact
  · rcases h with h | hAnnotation
    · rcases h with h | hTransient
      · rcases h with h | hExternalQuery
        · rcases h with h | hContext
          · rcases h with h | hObject
            · rcases h with h | hCode
              · rcases h with h | hReturnData
                · rcases h with h | hBuffer
                  · rcases h with h | hMemoryHash
                    · rcases h with h | hMemoryCopy
                      · rcases h with hCore | hMemory
                        · exact
                            (CompilerProfile.currentSolidCore_builtinCoverageEvidence
                              hCore).mono
                              (fun hCoverage =>
                                (CurrentSolidCoreSemanticCoverage.to_withMemoryBuiltins
                                  hCoverage)
                                  |>.to_solidityNoExternalNoVerbatim)
                        · exact
                            (CompilerProfile.MemoryBuiltin.coverageEvidence_current
                              hMemory).mono
                              (fun hCoverage =>
                                hCoverage.to_solidityNoExternalNoVerbatim)
                      · exact
                          (CompilerProfile.MemoryCopyBuiltin.coverageEvidence_current
                            hMemoryCopy).mono
                            (fun hCoverage =>
                              hCoverage.to_solidityNoExternalNoVerbatim)
                    · exact
                        (CompilerProfile.MemoryHashBuiltin.coverageEvidence_current
                          hMemoryHash).mono
                          (fun hCoverage =>
                            hCoverage.to_solidityNoExternalNoVerbatim)
                  · exact
                      (CompilerProfile.BufferBuiltin.coverageEvidence_current
                        hBuffer).mono
                        (fun hCoverage =>
                          hCoverage.to_solidityNoExternalNoVerbatim)
                · exact
                    (CompilerProfile.ReturnDataBuiltin.coverageEvidence_current
                      hReturnData).mono
                      (fun hCoverage =>
                        hCoverage.to_solidityNoExternalNoVerbatim)
              · exact
                  (CompilerProfile.CodeBuiltin.coverageEvidence_current
                    hCode).mono
                    (fun hCoverage =>
                      hCoverage.to_solidityNoExternalNoVerbatim)
            · exact
                (CompilerProfile.ObjectDataBuiltin.coverageEvidence_current
                  hObject).mono
                  (fun hCoverage =>
                    hCoverage.to_solidityNoExternalNoVerbatim)
          · exact
              (CompilerProfile.ContextWordBuiltin.coverageEvidence_current
                hContext).mono
                (fun hCoverage =>
                  hCoverage.to_solidityNoExternalNoVerbatim)
        · exact
            (CompilerProfile.ExternalQueryBuiltin.coverageEvidence_current
              hExternalQuery).mono
              (fun hCoverage =>
                hCoverage.to_solidityNoExternalNoVerbatim)
      · exact
          (CompilerProfile.TransientStorageBuiltin.coverageEvidence_current
            hTransient).mono
            (fun hCoverage =>
              hCoverage.to_solidityNoExternalNoVerbatim)
    · exact
        (CompilerProfile.CompilerAnnotationBuiltin.coverageEvidence_current
          hAnnotation).mono
          (fun hCoverage =>
            hCoverage.to_solidityNoExternalNoVerbatim)
  · exact
      (CompilerProfile.CompilerArtifactBuiltin.coverageEvidence_current
        hArtifact).mono
        (fun hCoverage =>
          hCoverage.to_solidityNoExternalNoVerbatim)

theorem CompilerProfile.currentSolidityEmittableNoVerbatim_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableNoVerbatim.builtinOK builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableNoVerbatimSemanticCoverage builtin := by
  simp [CompilerProfile.currentSolidityEmittableNoVerbatim] at h
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidityEmittableNoExternalCallsNoVerbatim_builtinCoverageEvidence
          hBuiltin).mono
          (fun hCoverage => hCoverage.to_noVerbatim)
  | inr hExternal =>
      exact
        (CompilerProfile.ExternalCallBuiltin.coverageEvidence_current
          hExternal).mono
          (fun hCoverage => hCoverage.to_solidityNoVerbatim)

theorem CompilerProfile.currentSolidityEmittable_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidityEmittable.builtinOK builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableNoVerbatimSemanticCoverage builtin :=
  CompilerProfile.currentSolidityEmittableNoVerbatim_builtinCoverageEvidence h

theorem CompilerProfile.currentSolidityEmittable_excludes_verbatim
    (inCount outCount : Nat) :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK
      (Evm.Builtin.verbatimOp inCount outCount) := by
  intro h
  rcases
    CompilerProfile.currentSolidityEmittable_builtinCoverageEvidence h with
    ⟨coverage, hCoverage, hOK⟩
  have hCoverageEq : coverage = Evm.SemanticCoverage.verbatim := by
    have hSome :
        some Evm.SemanticCoverage.verbatim = some coverage := by
      simpa [Evm.Builtin.semanticCoverage?] using hCoverage
    cases hSome
    rfl
  subst coverage
  simp [CurrentSolidityEmittableNoVerbatimSemanticCoverage,
    CurrentSolidityEmittableNoExternalCallsNoVerbatimSemanticCoverage,
    CurrentSolidCoreWithMemorySemanticCoverage,
    CurrentSolidCoreWithMemoryCopySemanticCoverage,
    CurrentSolidCoreWithMemoryHashSemanticCoverage,
    CurrentSolidCoreWithBufferSemanticCoverage,
    CurrentSolidCoreWithReturnDataSemanticCoverage,
    CurrentSolidCoreWithCodeSemanticCoverage,
    CurrentSolidCoreWithObjectDataSemanticCoverage,
    CurrentSolidCoreWithContextSemanticCoverage,
    CurrentSolidCoreWithExternalQuerySemanticCoverage,
    CurrentSolidCoreWithTransientStorageSemanticCoverage,
    CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage,
    CurrentSolidCoreWithCompilerArtifactsSemanticCoverage,
    CurrentSolidCoreWithExternalCallsSemanticCoverage,
    CurrentSolidCoreSemanticCoverage] at hOK

theorem CompilerProfile.currentSolidityEmittable_builtinBoundary
    {builtin : Evm.Builtin}
    (h : CompilerProfile.currentSolidityEmittable.builtinOK builtin) :
    BuiltinCanonicalSolidityEmittableBoundary builtin := by
  refine ⟨?_, ?_, ?_⟩
  · exact CompilerProfile.builtinOK_notOpaque
      CompilerProfile.currentSolidityEmittable h
  · intro inCount outCount hEq
    cases hEq
    exact
      (CompilerProfile.currentSolidityEmittable_excludes_verbatim
        inCount outCount) h
  · constructor
    · intro hEq
      cases hEq
      exact CompilerProfile.currentSolidityEmittable_excludes_gasOp h
    · intro hEq
      cases hEq
      exact CompilerProfile.currentSolidityEmittable_excludes_pcOp h

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidCoreBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_memoryCopy
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryCopyBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_memoryHash
    {builtin : Evm.Builtin}
    (h : CompilerProfile.MemoryHashBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_buffer
    {builtin : Evm.Builtin}
    (h : CompilerProfile.BufferBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_returnData
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ReturnDataBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_code
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CodeBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_objectData
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ObjectDataBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_contextWord
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ContextWordBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_externalQuery
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ExternalQueryBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_transientStorage
    {builtin : Evm.Builtin}
    (h : CompilerProfile.TransientStorageBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_compilerAnnotation
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CompilerAnnotationBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_compilerArtifact
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CompilerArtifactBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoExternalCallsNoVerbatimBuiltin,
    h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.of_externalCall
    {builtin : Evm.Builtin}
    (h : CompilerProfile.ExternalCallBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  simp [CompilerProfile.CurrentSolidityEmittableBuiltin,
    CompilerProfile.CurrentSolidityEmittableNoVerbatimBuiltin, h]

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    CompilerProfile.currentSolidityEmittable.builtinOK builtin :=
  (CompilerProfile.currentSolidityEmittable_builtinOK_iff builtin).2 h

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.signature
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig :=
  CompilerProfile.currentSolidityEmittable.builtinOK_signature
    (CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK h)

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.claimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin :=
  CompilerProfile.currentSolidityEmittable_builtinClaimEvidence
    (CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK h)

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.nonDeferredClaimEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    BuiltinClaimEvidence NonDeferredClaim builtin :=
  CompilerProfile.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
    (CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK h)

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.coverageEvidence
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableNoVerbatimSemanticCoverage builtin :=
  CompilerProfile.currentSolidityEmittable_builtinCoverageEvidence
    (CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK h)

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.boundary
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    BuiltinCanonicalSolidityEmittableBoundary builtin :=
  CompilerProfile.currentSolidityEmittable_builtinBoundary
    (CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK h)

theorem CompilerProfile.CurrentSolidityEmittableBuiltin.evidenceBundle
    {builtin : Evm.Builtin}
    (h : CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    (∃ sig, builtin.signature? = some sig) ∧
      BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin ∧
      BuiltinClaimEvidence NonDeferredClaim builtin ∧
      BuiltinCoverageEvidence
        CurrentSolidityEmittableNoVerbatimSemanticCoverage builtin ∧
      BuiltinCanonicalSolidityEmittableBoundary builtin :=
  ⟨ CompilerProfile.CurrentSolidityEmittableBuiltin.signature h
  , CompilerProfile.CurrentSolidityEmittableBuiltin.claimEvidence h
  , CompilerProfile.CurrentSolidityEmittableBuiltin.nonDeferredClaimEvidence h
  , CompilerProfile.CurrentSolidityEmittableBuiltin.coverageEvidence h
  , CompilerProfile.CurrentSolidityEmittableBuiltin.boundary h ⟩

namespace SolidityEmission

structure CanonicalAstSurfaceEvidence : Prop where
  dataRefs :
    CompilerProfile.currentSolidityEmittable.allowDataRefs
  functionDefs :
    CompilerProfile.currentSolidityEmittable.allowFunctionDefs
  functionCalls :
    CompilerProfile.currentSolidityEmittable.allowFunctionCalls
  switch :
    CompilerProfile.currentSolidityEmittable.allowSwitch

theorem canonicalAstSurfaceEvidence :
    CanonicalAstSurfaceEvidence where
  dataRefs := CompilerProfile.currentSolidityEmittable_allowDataRefs
  functionDefs := CompilerProfile.currentSolidityEmittable_allowFunctionDefs
  functionCalls := CompilerProfile.currentSolidityEmittable_allowFunctionCalls
  switch := CompilerProfile.currentSolidityEmittable_allowSwitch

structure CanonicalBuiltinFeatureEvidence
    (requires : Evm.Builtin -> Prop) : Prop where
  builtinOK :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      CompilerProfile.currentSolidityEmittable.builtinOK builtin
  signature :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      ∃ sig, builtin.signature? = some sig
  claimEvidence :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim builtin
  nonDeferredClaimEvidence :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      BuiltinClaimEvidence NonDeferredClaim builtin
  coverageEvidence :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      BuiltinCoverageEvidence
        CurrentSolidityEmittableNoVerbatimSemanticCoverage builtin
  boundary :
    ∀ {builtin : Evm.Builtin}, requires builtin ->
      BuiltinCanonicalSolidityEmittableBoundary builtin

def canonicalBuiltinFeatureEvidenceOf
    {requires : Evm.Builtin -> Prop}
    (toCurrent :
      ∀ {builtin : Evm.Builtin}, requires builtin ->
        CompilerProfile.CurrentSolidityEmittableBuiltin builtin) :
    CanonicalBuiltinFeatureEvidence requires where
  builtinOK h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.builtinOK
      (toCurrent h)
  signature h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.signature
      (toCurrent h)
  claimEvidence h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.claimEvidence
      (toCurrent h)
  nonDeferredClaimEvidence h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.nonDeferredClaimEvidence
      (toCurrent h)
  coverageEvidence h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.coverageEvidence
      (toCurrent h)
  boundary h :=
    CompilerProfile.CurrentSolidityEmittableBuiltin.boundary
      (toCurrent h)

inductive ScalarWordBuiltin : Evm.Builtin -> Prop where
  | add : ScalarWordBuiltin Evm.Builtin.add
  | mul : ScalarWordBuiltin Evm.Builtin.mul
  | divOp : ScalarWordBuiltin Evm.Builtin.divOp
  | sdivOp : ScalarWordBuiltin Evm.Builtin.sdivOp
  | modOp : ScalarWordBuiltin Evm.Builtin.modOp
  | smodOp : ScalarWordBuiltin Evm.Builtin.smodOp
  | addmodOp : ScalarWordBuiltin Evm.Builtin.addmodOp
  | mulmodOp : ScalarWordBuiltin Evm.Builtin.mulmodOp
  | expOp : ScalarWordBuiltin Evm.Builtin.expOp
  | sub : ScalarWordBuiltin Evm.Builtin.sub
  | iszero : ScalarWordBuiltin Evm.Builtin.iszero
  | eqOp : ScalarWordBuiltin Evm.Builtin.eqOp
  | ltOp : ScalarWordBuiltin Evm.Builtin.ltOp
  | gtOp : ScalarWordBuiltin Evm.Builtin.gtOp
  | sltOp : ScalarWordBuiltin Evm.Builtin.sltOp
  | sgtOp : ScalarWordBuiltin Evm.Builtin.sgtOp
  | andOp : ScalarWordBuiltin Evm.Builtin.andOp
  | orOp : ScalarWordBuiltin Evm.Builtin.orOp
  | xorOp : ScalarWordBuiltin Evm.Builtin.xorOp
  | notOp : ScalarWordBuiltin Evm.Builtin.notOp
  | shlOp : ScalarWordBuiltin Evm.Builtin.shlOp
  | shrOp : ScalarWordBuiltin Evm.Builtin.shrOp
  | sarOp : ScalarWordBuiltin Evm.Builtin.sarOp
  | signextendOp : ScalarWordBuiltin Evm.Builtin.signextendOp
  | byteOp : ScalarWordBuiltin Evm.Builtin.byteOp
  | clzOp : ScalarWordBuiltin Evm.Builtin.clzOp

theorem ScalarWordBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : ScalarWordBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
      (by constructor)

theorem scalarWordEvidence :
    CanonicalBuiltinFeatureEvidence ScalarWordBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    ScalarWordBuiltin.to_currentSolidityEmittableBuiltin

inductive ControlAndErrorBuiltin : Evm.Builtin -> Prop where
  | stopOp : ControlAndErrorBuiltin Evm.Builtin.stopOp
  | returnOp : ControlAndErrorBuiltin Evm.Builtin.returnOp
  | revertOp : ControlAndErrorBuiltin Evm.Builtin.revertOp
  | invalidOp : ControlAndErrorBuiltin Evm.Builtin.invalidOp
  | popOp : ControlAndErrorBuiltin Evm.Builtin.popOp

theorem ControlAndErrorBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : ControlAndErrorBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
      (by constructor)

theorem controlAndErrorEvidence :
    CanonicalBuiltinFeatureEvidence ControlAndErrorBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    ControlAndErrorBuiltin.to_currentSolidityEmittableBuiltin

inductive AbiDispatchBuiltin : Evm.Builtin -> Prop where
  | calldatasizeOp : AbiDispatchBuiltin Evm.Builtin.calldatasizeOp
  | calldataloadOp : AbiDispatchBuiltin Evm.Builtin.calldataloadOp
  | callvalueOp : AbiDispatchBuiltin Evm.Builtin.callvalueOp
  | shrOp : AbiDispatchBuiltin Evm.Builtin.shrOp
  | eqOp : AbiDispatchBuiltin Evm.Builtin.eqOp
  | ltOp : AbiDispatchBuiltin Evm.Builtin.ltOp
  | gtOp : AbiDispatchBuiltin Evm.Builtin.gtOp
  | iszero : AbiDispatchBuiltin Evm.Builtin.iszero
  | mstore : AbiDispatchBuiltin Evm.Builtin.mstore
  | revertOp : AbiDispatchBuiltin Evm.Builtin.revertOp
  | returnOp : AbiDispatchBuiltin Evm.Builtin.returnOp

theorem AbiDispatchBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : AbiDispatchBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
          (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_buffer
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_contextWord
        (by constructor)

theorem abiDispatchEvidence :
    CanonicalBuiltinFeatureEvidence AbiDispatchBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    AbiDispatchBuiltin.to_currentSolidityEmittableBuiltin

inductive AbiMemoryBuiltin : Evm.Builtin -> Prop where
  | add : AbiMemoryBuiltin Evm.Builtin.add
  | sub : AbiMemoryBuiltin Evm.Builtin.sub
  | mul : AbiMemoryBuiltin Evm.Builtin.mul
  | divOp : AbiMemoryBuiltin Evm.Builtin.divOp
  | modOp : AbiMemoryBuiltin Evm.Builtin.modOp
  | ltOp : AbiMemoryBuiltin Evm.Builtin.ltOp
  | gtOp : AbiMemoryBuiltin Evm.Builtin.gtOp
  | eqOp : AbiMemoryBuiltin Evm.Builtin.eqOp
  | iszero : AbiMemoryBuiltin Evm.Builtin.iszero
  | andOp : AbiMemoryBuiltin Evm.Builtin.andOp
  | orOp : AbiMemoryBuiltin Evm.Builtin.orOp
  | xorOp : AbiMemoryBuiltin Evm.Builtin.xorOp
  | notOp : AbiMemoryBuiltin Evm.Builtin.notOp
  | shlOp : AbiMemoryBuiltin Evm.Builtin.shlOp
  | shrOp : AbiMemoryBuiltin Evm.Builtin.shrOp
  | sarOp : AbiMemoryBuiltin Evm.Builtin.sarOp
  | byteOp : AbiMemoryBuiltin Evm.Builtin.byteOp
  | signextendOp : AbiMemoryBuiltin Evm.Builtin.signextendOp
  | mload : AbiMemoryBuiltin Evm.Builtin.mload
  | mstore : AbiMemoryBuiltin Evm.Builtin.mstore
  | mstore8 : AbiMemoryBuiltin Evm.Builtin.mstore8
  | mcopyOp : AbiMemoryBuiltin Evm.Builtin.mcopyOp
  | calldataloadOp : AbiMemoryBuiltin Evm.Builtin.calldataloadOp
  | calldatasizeOp : AbiMemoryBuiltin Evm.Builtin.calldatasizeOp
  | calldatacopyOp : AbiMemoryBuiltin Evm.Builtin.calldatacopyOp
  | returndataloadOp : AbiMemoryBuiltin Evm.Builtin.returndataloadOp
  | returndatasizeOp : AbiMemoryBuiltin Evm.Builtin.returndatasizeOp
  | returndatacopyOp : AbiMemoryBuiltin Evm.Builtin.returndatacopyOp
  | returnOp : AbiMemoryBuiltin Evm.Builtin.returnOp
  | revertOp : AbiMemoryBuiltin Evm.Builtin.revertOp

theorem AbiMemoryBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : AbiMemoryBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
          (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memoryCopy
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_buffer
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_returnData
        (by constructor)

theorem abiMemoryEvidence :
    CanonicalBuiltinFeatureEvidence AbiMemoryBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    AbiMemoryBuiltin.to_currentSolidityEmittableBuiltin

inductive StorageLayoutBuiltin : Evm.Builtin -> Prop where
  | sload : StorageLayoutBuiltin Evm.Builtin.sload
  | sstore : StorageLayoutBuiltin Evm.Builtin.sstore
  | keccak256Op : StorageLayoutBuiltin Evm.Builtin.keccak256Op
  | mload : StorageLayoutBuiltin Evm.Builtin.mload
  | mstore : StorageLayoutBuiltin Evm.Builtin.mstore
  | add : StorageLayoutBuiltin Evm.Builtin.add
  | sub : StorageLayoutBuiltin Evm.Builtin.sub
  | mul : StorageLayoutBuiltin Evm.Builtin.mul
  | divOp : StorageLayoutBuiltin Evm.Builtin.divOp
  | modOp : StorageLayoutBuiltin Evm.Builtin.modOp
  | andOp : StorageLayoutBuiltin Evm.Builtin.andOp
  | orOp : StorageLayoutBuiltin Evm.Builtin.orOp
  | xorOp : StorageLayoutBuiltin Evm.Builtin.xorOp
  | notOp : StorageLayoutBuiltin Evm.Builtin.notOp
  | shlOp : StorageLayoutBuiltin Evm.Builtin.shlOp
  | shrOp : StorageLayoutBuiltin Evm.Builtin.shrOp
  | sarOp : StorageLayoutBuiltin Evm.Builtin.sarOp
  | byteOp : StorageLayoutBuiltin Evm.Builtin.byteOp
  | signextendOp : StorageLayoutBuiltin Evm.Builtin.signextendOp
  | tloadOp : StorageLayoutBuiltin Evm.Builtin.tloadOp
  | tstoreOp : StorageLayoutBuiltin Evm.Builtin.tstoreOp

theorem StorageLayoutBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : StorageLayoutBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
          (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memoryHash
        (by constructor)
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_transientStorage
          (by constructor)

theorem storageLayoutEvidence :
    CanonicalBuiltinFeatureEvidence StorageLayoutBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    StorageLayoutBuiltin.to_currentSolidityEmittableBuiltin

inductive DeploymentBuiltin : Evm.Builtin -> Prop where
  | datacopyOp : DeploymentBuiltin Evm.Builtin.datacopyOp
  | codecopyOp : DeploymentBuiltin Evm.Builtin.codecopyOp
  | codesizeOp : DeploymentBuiltin Evm.Builtin.codesizeOp
  | setimmutableOp : DeploymentBuiltin Evm.Builtin.setimmutableOp
  | loadimmutableOp : DeploymentBuiltin Evm.Builtin.loadimmutableOp
  | linkersymbolOp : DeploymentBuiltin Evm.Builtin.linkersymbolOp
  | memoryguardOp : DeploymentBuiltin Evm.Builtin.memoryguardOp
  | mload : DeploymentBuiltin Evm.Builtin.mload
  | mstore : DeploymentBuiltin Evm.Builtin.mstore
  | mstore8 : DeploymentBuiltin Evm.Builtin.mstore8
  | returnOp : DeploymentBuiltin Evm.Builtin.returnOp
  | stopOp : DeploymentBuiltin Evm.Builtin.stopOp

theorem DeploymentBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : DeploymentBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
          (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_code
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_objectData
        (by constructor)
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_compilerAnnotation
          (by constructor)
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_compilerArtifact
          (by constructor)

theorem deploymentEvidence :
    CanonicalBuiltinFeatureEvidence DeploymentBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    DeploymentBuiltin.to_currentSolidityEmittableBuiltin

theorem deploymentAllowsDataRefs :
    CompilerProfile.currentSolidityEmittable.allowDataRefs :=
  CompilerProfile.currentSolidityEmittable_allowDataRefs

inductive ExternalEffectBuiltin : Evm.Builtin -> Prop where
  | callOp : ExternalEffectBuiltin Evm.Builtin.callOp
  | callcodeOp : ExternalEffectBuiltin Evm.Builtin.callcodeOp
  | delegatecallOp : ExternalEffectBuiltin Evm.Builtin.delegatecallOp
  | staticcallOp : ExternalEffectBuiltin Evm.Builtin.staticcallOp
  | log0Op : ExternalEffectBuiltin Evm.Builtin.log0Op
  | log1Op : ExternalEffectBuiltin Evm.Builtin.log1Op
  | log2Op : ExternalEffectBuiltin Evm.Builtin.log2Op
  | log3Op : ExternalEffectBuiltin Evm.Builtin.log3Op
  | log4Op : ExternalEffectBuiltin Evm.Builtin.log4Op
  | createOp : ExternalEffectBuiltin Evm.Builtin.createOp
  | create2Op : ExternalEffectBuiltin Evm.Builtin.create2Op
  | selfdestructOp : ExternalEffectBuiltin Evm.Builtin.selfdestructOp
  | returndataloadOp : ExternalEffectBuiltin Evm.Builtin.returndataloadOp
  | returndatasizeOp : ExternalEffectBuiltin Evm.Builtin.returndatasizeOp
  | returndatacopyOp : ExternalEffectBuiltin Evm.Builtin.returndatacopyOp
  | mload : ExternalEffectBuiltin Evm.Builtin.mload
  | mstore : ExternalEffectBuiltin Evm.Builtin.mstore
  | mcopyOp : ExternalEffectBuiltin Evm.Builtin.mcopyOp
  | iszero : ExternalEffectBuiltin Evm.Builtin.iszero
  | revertOp : ExternalEffectBuiltin Evm.Builtin.revertOp

theorem ExternalEffectBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : ExternalEffectBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_currentSolidCore
          (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memory
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_memoryCopy
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_returnData
        (by constructor)
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_externalCall
        (by constructor)

theorem externalEffectEvidence :
    CanonicalBuiltinFeatureEvidence ExternalEffectBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    ExternalEffectBuiltin.to_currentSolidityEmittableBuiltin

inductive EnvironmentQueryBuiltin : Evm.Builtin -> Prop where
  | addressOp : EnvironmentQueryBuiltin Evm.Builtin.addressOp
  | originOp : EnvironmentQueryBuiltin Evm.Builtin.originOp
  | callerOp : EnvironmentQueryBuiltin Evm.Builtin.callerOp
  | callvalueOp : EnvironmentQueryBuiltin Evm.Builtin.callvalueOp
  | gaspriceOp : EnvironmentQueryBuiltin Evm.Builtin.gaspriceOp
  | coinbaseOp : EnvironmentQueryBuiltin Evm.Builtin.coinbaseOp
  | timestampOp : EnvironmentQueryBuiltin Evm.Builtin.timestampOp
  | numberOp : EnvironmentQueryBuiltin Evm.Builtin.numberOp
  | difficultyOp : EnvironmentQueryBuiltin Evm.Builtin.difficultyOp
  | prevrandaoOp : EnvironmentQueryBuiltin Evm.Builtin.prevrandaoOp
  | gaslimitOp : EnvironmentQueryBuiltin Evm.Builtin.gaslimitOp
  | chainidOp : EnvironmentQueryBuiltin Evm.Builtin.chainidOp
  | selfbalanceOp : EnvironmentQueryBuiltin Evm.Builtin.selfbalanceOp
  | basefeeOp : EnvironmentQueryBuiltin Evm.Builtin.basefeeOp
  | msizeOp : EnvironmentQueryBuiltin Evm.Builtin.msizeOp
  | blobbasefeeOp : EnvironmentQueryBuiltin Evm.Builtin.blobbasefeeOp
  | blockhashOp : EnvironmentQueryBuiltin Evm.Builtin.blockhashOp
  | balanceOp : EnvironmentQueryBuiltin Evm.Builtin.balanceOp
  | extcodesizeOp : EnvironmentQueryBuiltin Evm.Builtin.extcodesizeOp
  | extcodehashOp : EnvironmentQueryBuiltin Evm.Builtin.extcodehashOp
  | extcodecopyOp : EnvironmentQueryBuiltin Evm.Builtin.extcodecopyOp
  | blobhashOp : EnvironmentQueryBuiltin Evm.Builtin.blobhashOp

theorem EnvironmentQueryBuiltin.to_currentSolidityEmittableBuiltin
    {builtin : Evm.Builtin} (h : EnvironmentQueryBuiltin builtin) :
    CompilerProfile.CurrentSolidityEmittableBuiltin builtin := by
  cases h <;>
    first
    | exact CompilerProfile.CurrentSolidityEmittableBuiltin.of_contextWord
        (by constructor)
    | exact
        CompilerProfile.CurrentSolidityEmittableBuiltin.of_externalQuery
          (by constructor)

theorem environmentQueryEvidence :
    CanonicalBuiltinFeatureEvidence EnvironmentQueryBuiltin :=
  canonicalBuiltinFeatureEvidenceOf
    EnvironmentQueryBuiltin.to_currentSolidityEmittableBuiltin

inductive LoweringOnlyBuiltin : Evm.Builtin -> Prop where
  | gasOp : LoweringOnlyBuiltin Evm.Builtin.gasOp
  | pcOp : LoweringOnlyBuiltin Evm.Builtin.pcOp

def DeferredToLoweringClaim (claim : Evm.ClaimKind) : Prop :=
  claim = Evm.ClaimKind.deferredToLowering

theorem LoweringOnlyBuiltin.to_loweringEnvironmentBuiltin
    {builtin : Evm.Builtin} (h : LoweringOnlyBuiltin builtin) :
    CompilerProfile.LoweringEnvironmentBuiltin builtin := by
  cases h <;> constructor

theorem LoweringOnlyBuiltin.withLoweringEnvironment_builtinOK
    {builtin : Evm.Builtin} (h : LoweringOnlyBuiltin builtin) :
    CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
      builtin := by
  unfold CompilerProfile.currentSolidityEmittableWithLoweringEnvironment
  exact Or.inr h.to_loweringEnvironmentBuiltin

theorem LoweringOnlyBuiltin.signature
    {builtin : Evm.Builtin} (h : LoweringOnlyBuiltin builtin) :
    ∃ sig, builtin.signature? = some sig :=
  CompilerProfile.currentSolidityEmittableWithLoweringEnvironment
    |>.builtinOK_signature (h.withLoweringEnvironment_builtinOK)

theorem LoweringOnlyBuiltin.deferredClaimEvidence
    {builtin : Evm.Builtin} (h : LoweringOnlyBuiltin builtin) :
    BuiltinClaimEvidence DeferredToLoweringClaim builtin := by
  cases h <;>
    exact ⟨Evm.ClaimKind.deferredToLowering, rfl, rfl⟩

theorem LoweringOnlyBuiltin.currentSolidityEmittable_rejected
    {builtin : Evm.Builtin} (h : LoweringOnlyBuiltin builtin) :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK builtin := by
  cases h
  · exact CompilerProfile.currentSolidityEmittable_excludes_gasOp
  · exact CompilerProfile.currentSolidityEmittable_excludes_pcOp

inductive VerbatimEscapeBuiltin : Evm.Builtin -> Prop where
  | verbatimOp (inputs outputs : Nat) :
      VerbatimEscapeBuiltin (Evm.Builtin.verbatimOp inputs outputs)

theorem VerbatimEscapeBuiltin.to_verbatimBuiltin
    {builtin : Evm.Builtin} (h : VerbatimEscapeBuiltin builtin) :
    CompilerProfile.VerbatimBuiltin builtin := by
  cases h
  exact CompilerProfile.VerbatimBuiltin.verbatimOp _ _

theorem VerbatimEscapeBuiltin.withVerbatim_builtinOK
    {builtin : Evm.Builtin} (h : VerbatimEscapeBuiltin builtin) :
    CompilerProfile.currentSolidityEmittableWithVerbatim.builtinOK
      builtin := by
  unfold CompilerProfile.currentSolidityEmittableWithVerbatim
  exact Or.inr h.to_verbatimBuiltin

theorem VerbatimEscapeBuiltin.currentSolidityEmittable_rejected
    {builtin : Evm.Builtin} (h : VerbatimEscapeBuiltin builtin) :
    ¬ CompilerProfile.currentSolidityEmittable.builtinOK builtin := by
  cases h with
  | verbatimOp inputs outputs =>
      exact
        CompilerProfile.currentSolidityEmittable_excludes_verbatim
          inputs outputs

end SolidityEmission

theorem CompilerEmittableExpr.currentSolidityEmittable_builtinBoundary :
    ∀ {expr : Expr},
      CompilerEmittableExpr CompilerProfile.currentSolidityEmittable expr ->
        ExprCanonicalSolidityEmittableBoundaryEvidence expr :=
  CompilerEmittableExpr.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableExprs.currentSolidityEmittable_builtinBoundary :
    ∀ {exprs : List Expr},
      CompilerEmittableExprs CompilerProfile.currentSolidityEmittable exprs ->
        ExprsCanonicalSolidityEmittableBoundaryEvidence exprs :=
  CompilerEmittableExprs.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableStmt.currentSolidityEmittable_builtinBoundary :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt ->
        StmtCanonicalSolidityEmittableBoundaryEvidence stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableBlock.currentSolidityEmittable_builtinBoundary :
    ∀ {stmts : List Stmt},
      CompilerEmittableBlock CompilerProfile.currentSolidityEmittable stmts ->
        BlockCanonicalSolidityEmittableBoundaryEvidence stmts :=
  CompilerEmittableBlock.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableSwitchCases.currentSolidityEmittable_builtinBoundary :
    ∀ {cases : List (Value × Stmt)},
      CompilerEmittableSwitchCases CompilerProfile.currentSolidityEmittable
        cases ->
        SwitchCasesCanonicalSolidityEmittableBoundaryEvidence cases :=
  CompilerEmittableSwitchCases.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableOptionalStmt.currentSolidityEmittable_builtinBoundary :
    ∀ {stmt? : Option Stmt},
      CompilerEmittableOptionalStmt CompilerProfile.currentSolidityEmittable
        stmt? ->
        OptionalStmtCanonicalSolidityEmittableBoundaryEvidence stmt? :=
  CompilerEmittableOptionalStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinCanonicalSolidityEmittableBoundary)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinBoundary hBuiltin)

theorem CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt ->
        StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence :=
      BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence := BuiltinClaimEvidence NonDeferredClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidityEmittable_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidityEmittableNoVerbatimSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidityEmittable)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidityEmittableNoVerbatimSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidityEmittable_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidityEmittable_evidenceBundle :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidityEmittable stmt ->
        StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt ∧
          StmtBuiltinClaimEvidence NonDeferredClaim stmt ∧
          StmtBuiltinCoverageEvidence
            CurrentSolidityEmittableNoVerbatimSemanticCoverage stmt ∧
          StmtCanonicalSolidityEmittableBoundaryEvidence stmt :=
  fun hEmittable =>
    ⟨ CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence
        hEmittable
    , CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
        hEmittable
    , CompilerEmittableStmt.currentSolidityEmittable_builtinCoverageEvidence
        hEmittable
    , CompilerEmittableStmt.currentSolidityEmittable_builtinBoundary
        hEmittable ⟩

theorem CompilerProfile.currentSolidityEmittableWithVerbatim_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithVerbatim.builtinOK
        builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableWithVerbatimSemanticCoverage builtin := by
  simp [CompilerProfile.currentSolidityEmittableWithVerbatim] at h
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidityEmittableNoVerbatim_builtinCoverageEvidence
          hBuiltin).mono
          (fun hCoverage => hCoverage.to_withVerbatim)
  | inr hVerbatim =>
      exact
        (CompilerProfile.VerbatimBuiltin.coverageEvidence_current
          hVerbatim).mono
          (fun hCoverage => hCoverage.to_solidityWithVerbatim)

theorem CompilerProfile.currentSolidityEmittableWithLoweringEnvironment_builtinCoverageEvidence
    {builtin : Evm.Builtin}
    (h :
      CompilerProfile.currentSolidityEmittableWithLoweringEnvironment.builtinOK
        builtin) :
    BuiltinCoverageEvidence
      CurrentSolidityEmittableWithLoweringEnvironmentSemanticCoverage
      builtin := by
  simp [CompilerProfile.currentSolidityEmittableWithLoweringEnvironment]
    at h
  cases h with
  | inl hBuiltin =>
      exact
        (CompilerProfile.currentSolidityEmittableNoVerbatim_builtinCoverageEvidence
          hBuiltin).mono
          (fun hCoverage => hCoverage.to_withLoweringEnvironment)
  | inr hLowering =>
      exact
        (CompilerProfile.LoweringEnvironmentBuiltin.coverageEvidence_current
          hLowering).mono
          (fun hCoverage =>
            hCoverage.to_solidityWithLoweringEnvironment)

theorem CompilerEmittableStmt.currentSolidCore_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore)
    (builtinEvidence := BuiltinClaimEvidence ExactYulClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinClaimEvidence_exactOrAbstracted :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinClaimEvidence hEmittable
      |>.exactYul_to_exactOrAbstracted

theorem CompilerEmittableStmt.currentSolidCore_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinClaimEvidence hEmittable
      |>.exactYul_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withMemoryBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactYulClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactYul_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryHashBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withMemoryHashBuiltins)
    (builtinEvidence :=
      BuiltinClaimEvidence ExactAbstractedOrSymbolicClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryHashBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactAbstractedOrSymbolic_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withBufferBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withBufferBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactYulClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withBufferBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withBufferBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactYul_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withObjectDataBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withObjectDataBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactYulClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withObjectDataBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactYul_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithContextBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withContextBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withContextBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactYulClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withContextBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithContextBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withContextBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithContextBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactYul_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerAnnotations stmt ->
        StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withCompilerAnnotations)
    (builtinEvidence := BuiltinClaimEvidence ExactOrAbstractedClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerAnnotations stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence
      hEmittable
      |>.exactOrAbstracted_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactOrAbstractedClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactOrAbstracted_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithVerbatimBuiltins_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withVerbatimBuiltins stmt ->
        StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withVerbatimBuiltins)
    (builtinEvidence := BuiltinClaimEvidence ExactOrAbstractedClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithVerbatimBuiltins_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withVerbatimBuiltins stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithVerbatimBuiltins_builtinClaimEvidence
      hEmittable
      |>.exactOrAbstracted_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore)
    (builtinEvidence :=
      BuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withExternalCalls :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithExternalCallsSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withExternalCalls

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withMemoryBuiltins :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithMemorySemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withMemoryBuiltins

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithMemorySemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withMemoryBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithMemorySemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withMemoryHashBuiltins :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithMemoryHashSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withMemoryHashBuiltins

theorem CompilerEmittableStmt.currentSolidCoreWithMemoryHashBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withMemoryHashBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithMemoryHashSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withMemoryHashBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithMemoryHashSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withBufferBuiltins :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithBufferSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withBufferBuiltins

theorem CompilerEmittableStmt.currentSolidCoreWithBufferBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withBufferBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithBufferSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withBufferBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithBufferSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withBufferBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withObjectDataBuiltins :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithObjectDataSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withObjectDataBuiltins

theorem CompilerEmittableStmt.currentSolidCoreWithObjectDataBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withObjectDataBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithObjectDataSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withObjectDataBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithObjectDataSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withContextBuiltins :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithContextSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withContextBuiltins

theorem CompilerEmittableStmt.currentSolidCoreWithContextBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withContextBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithContextSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withContextBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithContextSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withContextBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withCompilerAnnotations :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withCompilerAnnotations

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerAnnotations_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerAnnotations stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withCompilerAnnotations)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withCompilerArtifacts :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithCompilerArtifactsSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withCompilerArtifacts

theorem CompilerEmittableStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithCompilerArtifactsSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithCompilerArtifactsSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence_withVerbatim :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt CompilerProfile.currentSolidCore stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithVerbatimSemanticCoverage stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCore_builtinCoverageEvidence hEmittable
      |>.currentSolidCore_to_withVerbatim

theorem CompilerEmittableStmt.currentSolidCoreWithVerbatimBuiltins_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withVerbatimBuiltins stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithVerbatimSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withVerbatimBuiltins)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithVerbatimSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withVerbatimBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithExternalCalls_builtinClaimEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withExternalCalls stmt ->
        StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withExternalCalls)
    (builtinEvidence := BuiltinClaimEvidence ExactOrAbstractedClaim)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withExternalCalls_builtinClaimEvidence
        hBuiltin)

theorem CompilerEmittableStmt.currentSolidCoreWithExternalCalls_builtinClaimEvidence_nonDeferred :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withExternalCalls stmt ->
        StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  fun hEmittable =>
    CompilerEmittableStmt.currentSolidCoreWithExternalCalls_builtinClaimEvidence
      hEmittable
      |>.exactOrAbstracted_to_nonDeferred

theorem CompilerEmittableStmt.currentSolidCoreWithExternalCalls_builtinCoverageEvidence :
    ∀ {stmt : Stmt},
      CompilerEmittableStmt
          CompilerProfile.currentSolidCore.withExternalCalls stmt ->
        StmtBuiltinCoverageEvidence
          CurrentSolidCoreWithExternalCallsSemanticCoverage stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := CompilerProfile.currentSolidCore.withExternalCalls)
    (builtinEvidence :=
      BuiltinCoverageEvidence
        CurrentSolidCoreWithExternalCallsSemanticCoverage)
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withExternalCalls_builtinCoverageEvidence
        hBuiltin)

mutual
  theorem CompilerEmittableExpr.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {expr : Expr},
        CompilerEmittableExpr source expr ->
          CompilerEmittableExpr target expr
    | _, CompilerEmittableExpr.value hValue =>
        CompilerEmittableExpr.value (hLe.valueOK hValue)
    | _, CompilerEmittableExpr.var name =>
        CompilerEmittableExpr.var name
    | _, CompilerEmittableExpr.keccak hKeccak =>
        CompilerEmittableExpr.keccak (hLe.symbolicKeccak hKeccak)
    | _, CompilerEmittableExpr.dataSize hDataRefs =>
        CompilerEmittableExpr.dataSize (hLe.dataRefs hDataRefs)
    | _, CompilerEmittableExpr.dataOffset hDataRefs =>
        CompilerEmittableExpr.dataOffset (hLe.dataRefs hDataRefs)
    | _, CompilerEmittableExpr.builtin hBuiltin hArgs =>
        CompilerEmittableExpr.builtin
          (hLe.builtinOK hBuiltin)
          (CompilerEmittableExprs.mono hLe hArgs)

  theorem CompilerEmittableExprs.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {exprs : List Expr},
        CompilerEmittableExprs source exprs ->
          CompilerEmittableExprs target exprs
    | _, CompilerEmittableExprs.nil =>
        CompilerEmittableExprs.nil
    | _, CompilerEmittableExprs.cons hExpr hRest =>
        CompilerEmittableExprs.cons
          (CompilerEmittableExpr.mono hLe hExpr)
          (CompilerEmittableExprs.mono hLe hRest)
end

mutual
  theorem CompilerEmittableStmt.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {stmt : Stmt},
        CompilerEmittableStmt source stmt ->
          CompilerEmittableStmt target stmt
    | _, CompilerEmittableStmt.skip =>
        CompilerEmittableStmt.skip
    | _, CompilerEmittableStmt.expr hExpr =>
        CompilerEmittableStmt.expr
          (CompilerEmittableExpr.mono hLe hExpr)
    | _, CompilerEmittableStmt.let1None =>
        CompilerEmittableStmt.let1None
    | _, CompilerEmittableStmt.let1Some hExpr =>
        CompilerEmittableStmt.let1Some
          (CompilerEmittableExpr.mono hLe hExpr)
    | _, CompilerEmittableStmt.letManyNone =>
        CompilerEmittableStmt.letManyNone
    | _, CompilerEmittableStmt.letManySome hExprs =>
        CompilerEmittableStmt.letManySome
          (CompilerEmittableExprs.mono hLe hExprs)
    | _, CompilerEmittableStmt.funDef hAllow hBody =>
        CompilerEmittableStmt.funDef
          (hLe.functionDefs hAllow)
          (CompilerEmittableStmt.mono hLe hBody)
    | _, CompilerEmittableStmt.assign hExpr =>
        CompilerEmittableStmt.assign
          (CompilerEmittableExpr.mono hLe hExpr)
    | _, CompilerEmittableStmt.assignMany hExprs =>
        CompilerEmittableStmt.assignMany
          (CompilerEmittableExprs.mono hLe hExprs)
    | _, CompilerEmittableStmt.letCall hAllow hArgs =>
        CompilerEmittableStmt.letCall
          (hLe.functionCalls hAllow)
          (CompilerEmittableExprs.mono hLe hArgs)
    | _, CompilerEmittableStmt.assignCall hAllow hArgs =>
        CompilerEmittableStmt.assignCall
          (hLe.functionCalls hAllow)
          (CompilerEmittableExprs.mono hLe hArgs)
    | _, CompilerEmittableStmt.seq hFirst hSecond =>
        CompilerEmittableStmt.seq
          (CompilerEmittableStmt.mono hLe hFirst)
          (CompilerEmittableStmt.mono hLe hSecond)
    | _, CompilerEmittableStmt.block hBlock =>
        CompilerEmittableStmt.block
          (CompilerEmittableBlock.mono hLe hBlock)
    | _, CompilerEmittableStmt.ifThen hCond hBody =>
        CompilerEmittableStmt.ifThen
          (CompilerEmittableExpr.mono hLe hCond)
          (CompilerEmittableStmt.mono hLe hBody)
    | _, CompilerEmittableStmt.switch hAllow hDiscr hCases hDefault =>
        CompilerEmittableStmt.switch
          (hLe.switch hAllow)
          (CompilerEmittableExpr.mono hLe hDiscr)
          (CompilerEmittableSwitchCases.mono hLe hCases)
          (CompilerEmittableOptionalStmt.mono hLe hDefault)
    | _, CompilerEmittableStmt.forLoop hPre hCond hPost hBody =>
        CompilerEmittableStmt.forLoop
          (CompilerEmittableStmt.mono hLe hPre)
          (CompilerEmittableExpr.mono hLe hCond)
          (CompilerEmittableStmt.mono hLe hPost)
          (CompilerEmittableStmt.mono hLe hBody)
    | _, CompilerEmittableStmt.break =>
        CompilerEmittableStmt.break
    | _, CompilerEmittableStmt.continue =>
        CompilerEmittableStmt.continue
    | _, CompilerEmittableStmt.leave =>
        CompilerEmittableStmt.leave

  theorem CompilerEmittableBlock.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {stmts : List Stmt},
        CompilerEmittableBlock source stmts ->
          CompilerEmittableBlock target stmts
    | _, CompilerEmittableBlock.nil =>
        CompilerEmittableBlock.nil
    | _, CompilerEmittableBlock.cons hStmt hRest =>
        CompilerEmittableBlock.cons
          (CompilerEmittableStmt.mono hLe hStmt)
          (CompilerEmittableBlock.mono hLe hRest)

  theorem CompilerEmittableSwitchCases.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {cases : List (Value × Stmt)},
        CompilerEmittableSwitchCases source cases ->
          CompilerEmittableSwitchCases target cases
    | _, CompilerEmittableSwitchCases.nil =>
        CompilerEmittableSwitchCases.nil
    | _, CompilerEmittableSwitchCases.cons hLabel hBranch hRest =>
        CompilerEmittableSwitchCases.cons
          (hLe.valueOK hLabel)
          (CompilerEmittableStmt.mono hLe hBranch)
          (CompilerEmittableSwitchCases.mono hLe hRest)

  theorem CompilerEmittableOptionalStmt.mono
      {source target : CompilerProfile}
      (hLe : CompilerProfile.Le source target) :
      ∀ {stmt? : Option Stmt},
        CompilerEmittableOptionalStmt source stmt? ->
          CompilerEmittableOptionalStmt target stmt?
    | _, CompilerEmittableOptionalStmt.none =>
        CompilerEmittableOptionalStmt.none
    | _, CompilerEmittableOptionalStmt.some hStmt =>
        CompilerEmittableOptionalStmt.some
          (CompilerEmittableStmt.mono hLe hStmt)
end

theorem CompilerEmittableStmt.withExternalCalls
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withExternalCalls stmt :=
  CompilerEmittableStmt.mono (CompilerProfile.le_withExternalCalls profile)
    hStmt

theorem CompilerEmittableStmt.withMemoryBuiltins
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withMemoryBuiltins stmt :=
  CompilerEmittableStmt.mono (CompilerProfile.le_withMemoryBuiltins profile)
    hStmt

theorem CompilerEmittableStmt.withMemoryHashBuiltins
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withMemoryHashBuiltins stmt :=
  CompilerEmittableStmt.mono
    (CompilerProfile.le_withMemoryHashBuiltins profile) hStmt

theorem CompilerEmittableStmt.withBufferBuiltins
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withBufferBuiltins stmt :=
  CompilerEmittableStmt.mono (CompilerProfile.le_withBufferBuiltins profile)
    hStmt

theorem CompilerEmittableStmt.withCompilerAnnotations
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withCompilerAnnotations stmt :=
  CompilerEmittableStmt.mono
    (CompilerProfile.le_withCompilerAnnotations profile) hStmt

theorem CompilerEmittableStmt.withVerbatimBuiltins
    {profile : CompilerProfile} {stmt : Stmt}
    (hStmt : CompilerEmittableStmt profile stmt) :
    CompilerEmittableStmt profile.withVerbatimBuiltins stmt :=
  CompilerEmittableStmt.mono
    (CompilerProfile.le_withVerbatimBuiltins profile) hStmt

def switchTarget? (value : Value) : List (Value × Stmt) -> Option Stmt ->
    Option Stmt
  | [], defaultBranch => defaultBranch
  | (label, branch) :: rest, defaultBranch =>
      if label = value then some branch else switchTarget? value rest defaultBranch

def containsSwitchLabel : List (Value × Stmt) -> Value -> Bool
  | [], _ => false
  | (candidate, _) :: rest, value =>
      if candidate = value then true else containsSwitchLabel rest value

def switchCaseLabelsUnique : List (Value × Stmt) -> Bool
  | [] => true
  | (label, _) :: rest =>
      !containsSwitchLabel rest label && switchCaseLabelsUnique rest

def switchHasBranch : List (Value × Stmt) -> Option Stmt -> Bool
  | [], none => false
  | _, _ => true

mutual
  def stmtHasNoFunDefs : Stmt -> Bool
    | Stmt.funDef _ _ _ _ => false
    | Stmt.seq first second => stmtHasNoFunDefs first && stmtHasNoFunDefs second
    | Stmt.block stmts => blockHasNoFunDefs stmts
    | Stmt.ifThen _ body => stmtHasNoFunDefs body
    | Stmt.switch _ cases defaultBranch =>
        switchCasesHaveNoFunDefs cases &&
          match defaultBranch with
          | some branch => stmtHasNoFunDefs branch
          | none => true
    | Stmt.forLoop pre _ post body =>
        stmtHasNoFunDefs pre && stmtHasNoFunDefs post && stmtHasNoFunDefs body
    | _ => true

  def blockHasNoFunDefs : List Stmt -> Bool
    | [] => true
    | stmt :: rest => stmtHasNoFunDefs stmt && blockHasNoFunDefs rest

  def switchCasesHaveNoFunDefs : List (Value × Stmt) -> Bool
    | [] => true
    | (_, branch) :: rest =>
        stmtHasNoFunDefs branch && switchCasesHaveNoFunDefs rest
end

mutual
  def evalStmt : Env -> Stmt -> Option Env
    | env, Stmt.skip => some env
    | env, Stmt.expr expr =>
        match evalExpr env expr with
        | some _ => some env
        | none => none
    | env, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr env expr with
            | some value => declare? env name value
            | none => none
        | none => declare? env name (Value.word 0)
    | env, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprs env exprs with
            | some values => declareMany? env names values
            | none => none
        | none => declareMany? env names (names.map (fun _ => Value.word 0))
    | env, Stmt.funDef _ _ _ _ => some env
    | env, Stmt.assign name expr =>
        match evalExpr env expr with
        | some value => assign? env name value
        | none => none
    | env, Stmt.assignMany names exprs =>
        match evalExprs env exprs with
        | some values => assignMany? env names values
        | none => none
    | _, Stmt.letCall _ _ _ => none
    | _, Stmt.assignCall _ _ _ => none
    | env, Stmt.seq first second =>
        match evalStmt env first with
        | some env' => evalStmt env' second
        | none => none
    | env, Stmt.block stmts =>
        match evalBlock env stmts with
        | some inner => restoreOuter env inner
        | none => none
    | _, Stmt.ifThen _ _ => none
    | _, Stmt.switch _ _ _ => none
    | _, Stmt.forLoop _ _ _ _ => none
    | _, Stmt.break => none
    | _, Stmt.continue => none
    | _, Stmt.leave => none

  def evalBlock : Env -> List Stmt -> Option Env
    | env, [] => some env
    | env, stmt :: rest =>
        match evalStmt env stmt with
        | some env' => evalBlock env' rest
        | none => none
end

inductive Flow where
  | normal
  | broke
  | continued
  | left
  | halted
  deriving DecidableEq, Repr

structure FlowResult where
  flow : Flow
  env : Env
  deriving DecidableEq, Repr

def normalResult (env : Env) : FlowResult :=
  { flow := Flow.normal, env := env }

def withRestoredEnv (outer : Env) (result : FlowResult) : Option FlowResult :=
  match restoreOuter outer result.env with
  | some restored => some { flow := result.flow, env := restored }
  | none => none

def withRestoredFlow (outer : Env) (env : Env) (flow : Flow) :
    Option FlowResult :=
  match restoreOuter outer env with
  | some restored => some { flow := flow, env := restored }
  | none => none

mutual
  def evalControlStmtFuel : Nat -> Env -> Stmt -> Option FlowResult
    | 0, _, _ => none
    | _fuel + 1, env, Stmt.skip => some (normalResult env)
    | _fuel + 1, env, Stmt.expr expr =>
        match evalExpr env expr with
        | some _ => some (normalResult env)
        | none => none
    | _fuel + 1, env, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr env expr with
            | some value =>
                match declare? env name value with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none =>
            match declare? env name (Value.word 0) with
            | some env' => some (normalResult env')
            | none => none
    | _fuel + 1, env, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprs env exprs with
            | some values =>
                match declareMany? env names values with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none =>
            match declareMany? env names (names.map (fun _ => Value.word 0)) with
            | some env' => some (normalResult env')
            | none => none
    | _fuel + 1, env, Stmt.funDef _ _ _ _ =>
        some (normalResult env)
    | _fuel + 1, env, Stmt.assign name expr =>
        match evalExpr env expr with
        | some value =>
            match assign? env name value with
            | some env' => some (normalResult env')
            | none => none
        | none => none
    | _fuel + 1, env, Stmt.assignMany names exprs =>
        match evalExprs env exprs with
        | some values =>
            match assignMany? env names values with
            | some env' => some (normalResult env')
            | none => none
        | none => none
    | _fuel + 1, _, Stmt.letCall _ _ _ => none
    | _fuel + 1, _, Stmt.assignCall _ _ _ => none
    | fuel + 1, env, Stmt.seq first second =>
        match evalControlStmtFuel fuel env first with
        | some { flow := Flow.normal, env := env' } =>
            evalControlStmtFuel fuel env' second
        | some result => some result
        | none => none
    | fuel + 1, env, Stmt.block stmts =>
        match evalControlBlockFuel fuel env stmts with
        | some result => withRestoredEnv env result
        | none => none
    | fuel + 1, env, Stmt.ifThen cond body =>
        match evalExpr env cond with
        | some value =>
            match valueAsBool value with
            | some true => evalControlStmtFuel fuel env body
            | some false => some (normalResult env)
            | none => none
        | none => none
    | fuel + 1, env, Stmt.switch discr cases defaultBranch =>
        match evalExpr env discr with
        | some value =>
            match switchTarget? value cases defaultBranch with
            | some branch => evalControlStmtFuel fuel env branch
            | none => some (normalResult env)
        | none => none
    | fuel + 1, env, Stmt.forLoop pre cond post body =>
        match evalControlStmtFuel fuel env pre with
        | some { flow := Flow.normal, env := loopEnv } =>
            evalControlForFuel fuel env loopEnv cond post body
        | some result => withRestoredEnv env result
        | none => none
    | _fuel + 1, env, Stmt.break =>
        some { flow := Flow.broke, env := env }
    | _fuel + 1, env, Stmt.continue =>
        some { flow := Flow.continued, env := env }
    | _fuel + 1, env, Stmt.leave =>
        some { flow := Flow.left, env := env }

  def evalControlBlockFuel : Nat -> Env -> List Stmt -> Option FlowResult
    | 0, _, _ => none
    | _fuel + 1, env, [] => some (normalResult env)
    | fuel + 1, env, stmt :: rest =>
        match evalControlStmtFuel fuel env stmt with
        | some { flow := Flow.normal, env := env' } =>
            evalControlBlockFuel fuel env' rest
        | some result => some result
        | none => none

  def evalControlForFuel : Nat -> Env -> Env -> Expr -> Stmt -> Stmt ->
      Option FlowResult
    | 0, _, _, _, _, _ => none
    | fuel + 1, outer, loopEnv, cond, post, body =>
        match evalExpr loopEnv cond with
        | some value =>
            match valueAsBool value with
            | some false => withRestoredFlow outer loopEnv Flow.normal
            | some true =>
                match evalControlStmtFuel fuel loopEnv body with
                | some { flow := Flow.normal, env := bodyEnv } =>
                    match evalControlStmtFuel fuel bodyEnv post with
                    | some { flow := Flow.normal, env := postEnv } =>
                        evalControlForFuel fuel outer postEnv cond post body
                    | some { flow := Flow.continued, env := postEnv } =>
                        evalControlForFuel fuel outer postEnv cond post body
                    | some { flow := Flow.broke, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.normal
                    | some { flow := Flow.left, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.left
                    | some { flow := Flow.halted, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.halted
                    | none => none
                | some { flow := Flow.continued, env := bodyEnv } =>
                    match evalControlStmtFuel fuel bodyEnv post with
                    | some { flow := Flow.normal, env := postEnv } =>
                        evalControlForFuel fuel outer postEnv cond post body
                    | some { flow := Flow.continued, env := postEnv } =>
                        evalControlForFuel fuel outer postEnv cond post body
                    | some { flow := Flow.broke, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.normal
                    | some { flow := Flow.left, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.left
                    | some { flow := Flow.halted, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.halted
                    | none => none
                | some { flow := Flow.broke, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.normal
                | some { flow := Flow.left, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.left
                | some { flow := Flow.halted, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.halted
                | none => none
            | none => none
        | none => none
end

def lookupData? : List (DataLabel × SymbolicBytes) -> DataLabel ->
    Option SymbolicBytes
  | [], _ => none
  | (candidate, bytes) :: rest, label =>
      if candidate = label then some bytes else lookupData? rest label

inductive YulObject where
  | mk : DataLabel -> Stmt -> List (DataLabel × SymbolicBytes) ->
      List YulObject -> YulObject
  deriving Repr

def YulObject.label : YulObject -> DataLabel
  | YulObject.mk label _ _ _ => label

def YulObject.code : YulObject -> Stmt
  | YulObject.mk _ code _ _ => code

def YulObject.data? : YulObject -> DataLabel -> Option SymbolicBytes
  | YulObject.mk _ _ dataEntries _, label => lookupData? dataEntries label

def evalObjectExpr (object : YulObject) (env : Env) : Expr -> Option Value
  | Expr.value value => some value
  | Expr.var name => lookup? env name
  | Expr.keccak bytes => some (symbolicKeccak bytes)
  | Expr.dataSize label =>
      match object.data? label with
      | some bytes => some (Value.word (symbolicDataSize bytes))
      | none => none
  | Expr.dataOffset label =>
      match object.data? label with
      | some _ => some (Value.dataOffset label)
      | none => none
  | Expr.builtin _ _ => none

structure ObjectMemory where
  writes : List (Word × SymbolicBytes)
  deriving DecidableEq, Repr

def ObjectMemory.empty : ObjectMemory :=
  { writes := [] }

def ObjectMemory.write (memory : ObjectMemory) (offset : Word)
    (bytes : SymbolicBytes) : ObjectMemory :=
  { writes := (offset, bytes) :: memory.writes }

def copyObjectData? (object : YulObject) (memory : ObjectMemory)
    (offset : Word) (label : DataLabel) : Option ObjectMemory :=
  match object.data? label with
  | some bytes => some (memory.write offset bytes)
  | none => none

def lookupWordMap? : List (Word × Value) -> Word -> Option Value
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if norm candidate = norm key then some value else lookupWordMap? rest key

def writeWordMap (entries : List (Word × Value)) (key : Word)
    (value : Value) : List (Word × Value) :=
  (norm key, value) :: entries

def lookupValueMap? : List (Value × Value) -> Value -> Option Value
  | [], _ => none
  | (candidate, value) :: rest, key =>
      if candidate = key then some value else lookupValueMap? rest key

def writeValueMap (entries : List (Value × Value)) (key value : Value) :
    List (Value × Value) :=
  (key, value) :: entries

theorem lookupValueMap_writeValueMap_same
    (entries : List (Value × Value)) (key value : Value) :
    lookupValueMap? (writeValueMap entries key value) key = some value := by
  simp [lookupValueMap?, writeValueMap]

theorem lookupValueMap_writeValueMap_other
    (entries : List (Value × Value)) {key query value : Value}
    (hKey : key ≠ query) :
    lookupValueMap? (writeValueMap entries key value) query =
      lookupValueMap? entries query := by
  simp [lookupValueMap?, writeValueMap, hKey]

abbrev AccountValueMap := List (Word × List (Value × Value))

def lookupAccountValueEntries? : AccountValueMap -> Word ->
    Option (List (Value × Value))
  | [], _ => none
  | (candidate, entries) :: rest, address =>
      if norm candidate = norm address then
        some entries
      else
        lookupAccountValueEntries? rest address

def lookupAccountValueMap?
    (accounts : AccountValueMap) (address : Word) (key : Value) :
    Option Value :=
  match lookupAccountValueEntries? accounts address with
  | some entries => lookupValueMap? entries key
  | none => none

def writeAccountValueMap
    (accounts : AccountValueMap) (address : Word) (key value : Value) :
    AccountValueMap :=
  let entries :=
    match lookupAccountValueEntries? accounts address with
    | some entries => entries
    | none => []
  (norm address, writeValueMap entries key value) :: accounts

theorem lookupAccountValueEntries_write_other_address
    (accounts : AccountValueMap) {address other : Word}
    {key value : Value}
    (hOther : norm other ≠ norm address) :
    lookupAccountValueEntries?
        (writeAccountValueMap accounts address key value) other =
      lookupAccountValueEntries? accounts other := by
  have hNorm : norm (norm address) = norm address := by
    simp [norm, wordModulus]
  have hNe : norm (norm address) ≠ norm other := by
    rw [hNorm]
    exact Ne.symm hOther
  simp [writeAccountValueMap, lookupAccountValueEntries?, hNe]

theorem lookupAccountValueMap_write_same
    (accounts : AccountValueMap) (address : Word) (key value : Value) :
    lookupAccountValueMap?
        (writeAccountValueMap accounts address key value) address key =
      some value := by
  have hNorm : norm (norm address) = norm address := by
    simp [norm, wordModulus]
  simp [lookupAccountValueMap?, writeAccountValueMap,
    lookupAccountValueEntries?, lookupValueMap_writeValueMap_same, hNorm]

theorem lookupAccountValueMap_write_other_address
    (accounts : AccountValueMap) {address other : Word}
    {key value readKey : Value}
    (hOther : norm other ≠ norm address) :
    lookupAccountValueMap?
        (writeAccountValueMap accounts address key value) other readKey =
      lookupAccountValueMap? accounts other readKey := by
  simp [lookupAccountValueMap?,
    lookupAccountValueEntries_write_other_address accounts hOther]

theorem lookupAccountValueMap_write_same_address_other_key
    (accounts : AccountValueMap) (address : Word) {key query value : Value}
    (hKey : key ≠ query) :
    lookupAccountValueMap?
        (writeAccountValueMap accounts address key value) address query =
      lookupAccountValueMap? accounts address query := by
  have hNorm : norm (norm address) = norm address := by
    simp [norm, wordModulus]
  cases hEntries : lookupAccountValueEntries? accounts address with
  | none =>
      simp [lookupAccountValueMap?, writeAccountValueMap,
        lookupAccountValueEntries?, hEntries, lookupValueMap_writeValueMap_other,
        hKey, hNorm, lookupValueMap?]
  | some entries =>
      simp [lookupAccountValueMap?, writeAccountValueMap,
        lookupAccountValueEntries?, hEntries, lookupValueMap_writeValueMap_other,
        hKey, hNorm]

structure ExternalEvent where
  id : Nat
  op : Evm.Builtin
  args : List Value
  result : Value
  returndata : SymbolicBytes
  deriving DecidableEq, Repr

structure EvmHalt where
  kind : Evm.HaltKind
  returndata : SymbolicBytes
  deriving DecidableEq, Repr

structure EvmState where
  storage : AccountValueMap := []
  transientStorage : AccountValueMap := []
  immutables : List (Value × Value) := []
  linkerSymbols : List (Value × Value) := []
  memoryWords : List (Word × Value) := []
  memoryBytes : ObjectMemory := ObjectMemory.empty
  memoryVersion : Nat := 0
  calldata : SymbolicBytes := SymbolicBytes.empty
  returndata : SymbolicBytes := SymbolicBytes.empty
  returndataVersion : Nat := 0
  code : SymbolicBytes := SymbolicBytes.empty
  address : Word := 0
  origin : Word := 0
  caller : Word := 0
  callvalue : Word := 0
  gasprice : Word := 0
  coinbase : Word := 0
  timestamp : Word := 0
  number : Word := 0
  difficulty : Word := 0
  prevrandao : Word := 0
  gaslimit : Word := 0
  chainid : Word := 0
  selfbalance : Word := 0
  basefee : Word := 0
  gas : Word := 0
  pc : Word := 0
  msize : Word := 0
  blobbasefee : Word := 0
  logs : List (Nat × List Value × SymbolicBytes) := []
  externalActions : List Evm.Builtin := []
  externalEvents : List ExternalEvent := []
  nextExternalId : Nat := 1
  halt? : Option EvmHalt := none
  deriving DecidableEq, Repr

def EvmState.empty : EvmState := {}

def returnWord (value : Word) (state : EvmState) : Option (Value × EvmState) :=
  some (Value.word value, state)

def returnUnit (state : EvmState) : Option (Value × EvmState) :=
  returnWord 0 state

def expandMemory (state : EvmState) (offset size : Word) : EvmState :=
  { state with msize := memorySizeAfter state.msize offset size }

def bumpMemoryVersion (state : EvmState) : EvmState :=
  { state with memoryVersion := state.memoryVersion + 1 }

def bumpMemoryVersionIfAccessed (state : EvmState) (size : Word) : EvmState :=
  if norm size = 0 then state else bumpMemoryVersion state

def recordMemoryWrite (state : EvmState) (offset size : Word) : EvmState :=
  bumpMemoryVersionIfAccessed (expandMemory state offset size) size

theorem recordMemoryWrite_memoryWords
    (state : EvmState) (offset size : Word) :
    (recordMemoryWrite state offset size).memoryWords =
      state.memoryWords := by
  unfold recordMemoryWrite bumpMemoryVersionIfAccessed bumpMemoryVersion
    expandMemory
  by_cases hSize : norm size = 0 <;> simp [hSize]

theorem recordMemoryWrite_memoryVersion_of_zero
    (state : EvmState) (offset size : Word)
    (hSize : norm size = 0) :
    (recordMemoryWrite state offset size).memoryVersion =
      state.memoryVersion := by
  simp [recordMemoryWrite, bumpMemoryVersionIfAccessed, expandMemory,
    hSize]

theorem recordMemoryWrite_memoryVersion_of_nonzero
    (state : EvmState) (offset size : Word)
    (hSize : norm size ≠ 0) :
    (recordMemoryWrite state offset size).memoryVersion =
      state.memoryVersion + 1 := by
  simp [recordMemoryWrite, bumpMemoryVersionIfAccessed, bumpMemoryVersion,
    expandMemory, hSize]

theorem recordMemoryWrite_memoryVersion_32
    (state : EvmState) (offset : Word) :
    (recordMemoryWrite state offset 32).memoryVersion =
      state.memoryVersion + 1 := by
  exact
    recordMemoryWrite_memoryVersion_of_nonzero state offset 32 (by decide)

def recordExternalEvent (builtin : Evm.Builtin) (args : List Value)
    (state : EvmState) : Value × EvmState :=
  let id := state.nextExternalId
  let result := Value.callSuccess id
  let returndata := SymbolicBytes.callReturnData id
  ( result
  , { state with
      returndata := returndata
      returndataVersion := id
      externalActions := builtin :: state.externalActions
      externalEvents :=
        { id := id
          op := builtin
          args := args
          result := result
          returndata := returndata } :: state.externalEvents
      nextExternalId := id + 1 } )

def recordExternalCallEvent (builtin : Evm.Builtin) (args : List Value)
    (argsOffset argsSize retOffset retSize : Word) (state : EvmState) :
    Value × EvmState :=
  let (result, eventState) := recordExternalEvent builtin args state
  let accessedState := expandMemory eventState argsOffset argsSize
  if norm retSize = 0 then
    (result, accessedState)
  else
    ( result
    , recordMemoryWrite
        { accessedState with
          memoryWords := []
          memoryBytes :=
            ObjectMemory.write accessedState.memoryBytes retOffset
              (SymbolicBytes.returndataSnapshot
                eventState.returndataVersion 0 retSize) }
        retOffset retSize )

def recordExternalCreateEvent (builtin : Evm.Builtin) (args : List Value)
    (offset size : Word) (state : EvmState) : Value × EvmState :=
  let (result, eventState) := recordExternalEvent builtin args state
  (result, expandMemory eventState offset size)

def recordExternalUnit (builtin : Evm.Builtin) (args : List Value)
    (state : EvmState) : EvmState :=
  let id := state.nextExternalId
  { state with
    externalActions := builtin :: state.externalActions
    externalEvents :=
      { id := id, op := builtin, args := args, result := Value.word 0,
        returndata := state.returndata } :: state.externalEvents
    nextExternalId := id + 1 }

def recordExternalValueEvent (builtin : Evm.Builtin) (args : List Value)
    (state : EvmState) : Value × EvmState :=
  let id := state.nextExternalId
  let result := Value.callSuccess id
  ( result
  , { state with
      externalActions := builtin :: state.externalActions
      externalEvents :=
        { id := id
          op := builtin
          args := args
          result := result
          returndata := state.returndata } :: state.externalEvents
      nextExternalId := id + 1 } )

def externalValueResults : Nat -> Nat -> List Value
  | _, 0 => []
  | id, count + 1 => Value.callSuccess id :: externalValueResults (id + 1) count

theorem externalValueResults_length (start count : Nat) :
    (externalValueResults start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [externalValueResults, ih]

def externalValueEvents (builtin : Evm.Builtin) (args : List Value)
    (returndata : SymbolicBytes) : Nat -> Nat -> List ExternalEvent
  | _, 0 => []
  | id, count + 1 =>
      let result := Value.callSuccess id
      { id := id
        op := builtin
        args := args
        result := result
        returndata := returndata } ::
        externalValueEvents builtin args returndata (id + 1) count

def recordExternalValueEvents (builtin : Evm.Builtin) (args : List Value)
    (outputCount : Nat) (state : EvmState) : List Value × EvmState :=
  let id := state.nextExternalId
  let values := externalValueResults id outputCount
  let events := externalValueEvents builtin args state.returndata id outputCount
  ( values
  , { state with
      externalActions := builtin :: state.externalActions
      externalEvents := events ++ state.externalEvents
      nextExternalId := id + outputCount } )

def haltWith (kind : Evm.HaltKind) (returndata : SymbolicBytes)
    (state : EvmState) : EvmState :=
  { state with halt? := some { kind := kind, returndata := returndata } }

def evalEvmBuiltin (builtin : Evm.Builtin) (args : List Value)
    (state : EvmState) : Option (Value × EvmState) :=
  match builtin, args with
  | Evm.Builtin.verbatimOp inputs 0, args =>
      if args.length = inputs then
        returnUnit (recordExternalUnit (Evm.Builtin.verbatimOp inputs 0) args state)
      else
        none
  | Evm.Builtin.verbatimOp inputs 1, args =>
      if args.length = inputs then
        some (recordExternalValueEvent (Evm.Builtin.verbatimOp inputs 1)
          args state)
      else
        none
  | Evm.Builtin.verbatimOp _ _, _ => none
  | Evm.Builtin.stopOp, [] =>
      returnUnit (haltWith Evm.HaltKind.stop SymbolicBytes.empty state)
  | Evm.Builtin.add, [Value.word lhs, Value.word rhs] =>
      returnWord (addWord lhs rhs) state
  | Evm.Builtin.add, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.add lhs rhs, state)
  | Evm.Builtin.mul, [Value.word lhs, Value.word rhs] =>
      returnWord (mulWord lhs rhs) state
  | Evm.Builtin.mul, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.mul lhs rhs, state)
  | Evm.Builtin.divOp, [Value.word lhs, Value.word rhs] =>
      returnWord (divWord lhs rhs) state
  | Evm.Builtin.divOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.divOp lhs rhs, state)
  | Evm.Builtin.sdivOp, [Value.word lhs, Value.word rhs] =>
      returnWord (sdivWord lhs rhs) state
  | Evm.Builtin.sdivOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.sdivOp lhs rhs, state)
  | Evm.Builtin.modOp, [Value.word lhs, Value.word rhs] =>
      returnWord (modWord lhs rhs) state
  | Evm.Builtin.modOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.modOp lhs rhs, state)
  | Evm.Builtin.smodOp, [Value.word lhs, Value.word rhs] =>
      returnWord (smodWord lhs rhs) state
  | Evm.Builtin.smodOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.smodOp lhs rhs, state)
  | Evm.Builtin.addmodOp, [Value.word lhs, Value.word rhs, Value.word modulus] =>
      returnWord (addmodWord lhs rhs modulus) state
  | Evm.Builtin.addmodOp, [lhs, rhs, modulus] =>
      some (Value.ternaryBuiltin Evm.Builtin.addmodOp lhs rhs modulus, state)
  | Evm.Builtin.mulmodOp, [Value.word lhs, Value.word rhs, Value.word modulus] =>
      returnWord (mulmodWord lhs rhs modulus) state
  | Evm.Builtin.mulmodOp, [lhs, rhs, modulus] =>
      some (Value.ternaryBuiltin Evm.Builtin.mulmodOp lhs rhs modulus, state)
  | Evm.Builtin.expOp, [Value.word base, Value.word exponent] =>
      returnWord (expWord base exponent) state
  | Evm.Builtin.expOp, [base, exponent] =>
      some (Value.binaryBuiltin Evm.Builtin.expOp base exponent, state)
  | Evm.Builtin.sub, [Value.word lhs, Value.word rhs] =>
      returnWord (subWord lhs rhs) state
  | Evm.Builtin.sub, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.sub lhs rhs, state)
  | Evm.Builtin.iszero, [Value.word value] =>
      returnWord (iszeroWord value) state
  | Evm.Builtin.iszero, [value] =>
      some (Value.unaryBuiltin Evm.Builtin.iszero value, state)
  | Evm.Builtin.eqOp, [lhs, rhs] =>
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord => returnWord (eqWord lhsWord rhsWord) state
      | _, _ =>
          if lhs = rhs then returnWord 1 state
          else some (Value.binaryBuiltin Evm.Builtin.eqOp lhs rhs, state)
  | Evm.Builtin.ltOp, [Value.word lhs, Value.word rhs] =>
      returnWord (ltWord lhs rhs) state
  | Evm.Builtin.ltOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.ltOp lhs rhs, state)
  | Evm.Builtin.gtOp, [Value.word lhs, Value.word rhs] =>
      returnWord (gtWord lhs rhs) state
  | Evm.Builtin.gtOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.gtOp lhs rhs, state)
  | Evm.Builtin.sltOp, [Value.word lhs, Value.word rhs] =>
      returnWord (sltWord lhs rhs) state
  | Evm.Builtin.sltOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.sltOp lhs rhs, state)
  | Evm.Builtin.sgtOp, [Value.word lhs, Value.word rhs] =>
      returnWord (sgtWord lhs rhs) state
  | Evm.Builtin.sgtOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.sgtOp lhs rhs, state)
  | Evm.Builtin.andOp, [Value.word lhs, Value.word rhs] =>
      returnWord (andWord lhs rhs) state
  | Evm.Builtin.andOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.andOp lhs rhs, state)
  | Evm.Builtin.orOp, [Value.word lhs, Value.word rhs] =>
      returnWord (orWord lhs rhs) state
  | Evm.Builtin.orOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.orOp lhs rhs, state)
  | Evm.Builtin.xorOp, [Value.word lhs, Value.word rhs] =>
      returnWord (xorWord lhs rhs) state
  | Evm.Builtin.xorOp, [lhs, rhs] =>
      some (Value.binaryBuiltin Evm.Builtin.xorOp lhs rhs, state)
  | Evm.Builtin.notOp, [Value.word value] =>
      returnWord (notWord value) state
  | Evm.Builtin.notOp, [value] =>
      some (Value.unaryBuiltin Evm.Builtin.notOp value, state)
  | Evm.Builtin.shlOp, [Value.word shift, Value.word value] =>
      returnWord (shlWord shift value) state
  | Evm.Builtin.shlOp, [shift, value] =>
      some (Value.binaryBuiltin Evm.Builtin.shlOp shift value, state)
  | Evm.Builtin.shrOp, [Value.word shift, Value.word value] =>
      returnWord (shrWord shift value) state
  | Evm.Builtin.shrOp, [shift, value] =>
      some (Value.binaryBuiltin Evm.Builtin.shrOp shift value, state)
  | Evm.Builtin.sarOp, [Value.word shift, Value.word value] =>
      returnWord (sarWord shift value) state
  | Evm.Builtin.sarOp, [shift, value] =>
      some (Value.binaryBuiltin Evm.Builtin.sarOp shift value, state)
  | Evm.Builtin.signextendOp, [Value.word ix, Value.word value] =>
      returnWord (signextendWord ix value) state
  | Evm.Builtin.signextendOp, [ix, value] =>
      some (Value.binaryBuiltin Evm.Builtin.signextendOp ix value, state)
  | Evm.Builtin.byteOp, [Value.word ix, Value.word value] =>
      returnWord (byteWord ix value) state
  | Evm.Builtin.byteOp, [ix, value] =>
      some (Value.binaryBuiltin Evm.Builtin.byteOp ix value, state)
  | Evm.Builtin.clzOp, [Value.word value] =>
      returnWord (clzWord value) state
  | Evm.Builtin.clzOp, [value] =>
      some (Value.unaryBuiltin Evm.Builtin.clzOp value, state)
  | Evm.Builtin.popOp, [_] => returnUnit state
  | Evm.Builtin.addressOp, [] => returnWord state.address state
  | Evm.Builtin.originOp, [] => returnWord state.origin state
  | Evm.Builtin.callerOp, [] => returnWord state.caller state
  | Evm.Builtin.callvalueOp, [] => returnWord state.callvalue state
  | Evm.Builtin.gaspriceOp, [] => returnWord state.gasprice state
  | Evm.Builtin.coinbaseOp, [] => returnWord state.coinbase state
  | Evm.Builtin.timestampOp, [] => returnWord state.timestamp state
  | Evm.Builtin.numberOp, [] => returnWord state.number state
  | Evm.Builtin.difficultyOp, [] => returnWord state.difficulty state
  | Evm.Builtin.prevrandaoOp, [] => returnWord state.prevrandao state
  | Evm.Builtin.gaslimitOp, [] => returnWord state.gaslimit state
  | Evm.Builtin.chainidOp, [] => returnWord state.chainid state
  | Evm.Builtin.selfbalanceOp, [] => returnWord state.selfbalance state
  | Evm.Builtin.basefeeOp, [] => returnWord state.basefee state
  | Evm.Builtin.gasOp, [] => returnWord state.gas state
  | Evm.Builtin.pcOp, [] => returnWord state.pc state
  | Evm.Builtin.msizeOp, [] => returnWord state.msize state
  | Evm.Builtin.blobbasefeeOp, [] => returnWord state.blobbasefee state
  | Evm.Builtin.calldataloadOp, [Value.word offset] =>
      some (Value.calldataWord offset, state)
  | Evm.Builtin.calldatasizeOp, [] =>
      returnWord (symbolicDataSize state.calldata) state
  | Evm.Builtin.calldatacopyOp,
      [Value.word dest, Value.word offset, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.calldataSlice offset size) } dest size)
  | Evm.Builtin.returndataloadOp, [Value.word offset] =>
      some (Value.returndataWordAt state.returndataVersion offset, state)
  | Evm.Builtin.returndatasizeOp, [] =>
      returnWord (symbolicDataSize state.returndata) state
  | Evm.Builtin.returndatacopyOp,
      [Value.word dest, Value.word offset, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.returndataSnapshot
                  state.returndataVersion offset size) } dest size)
  | Evm.Builtin.codecopyOp,
      [Value.word dest, Value.word offset, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.codeSlice offset size) } dest size)
  | Evm.Builtin.datacopyOp,
      [Value.word dest, Value.dataOffset label, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.objectData label size) } dest size)
  | Evm.Builtin.datacopyOp,
      [Value.word dest, Value.word offset, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.codeSlice offset size) } dest size)
  | Evm.Builtin.extcodecopyOp,
      [Value.word address, Value.word dest, Value.word offset, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
            memoryWords := []
            memoryBytes :=
              ObjectMemory.write state.memoryBytes dest
                (SymbolicBytes.extcodeSlice address offset size) } dest size)
  | Evm.Builtin.keccak256Op, [Value.word offset, Value.word size] =>
      some
        (symbolicKeccak
          (SymbolicBytes.memorySnapshot state.memoryVersion offset size),
          expandMemory state offset size)
  | Evm.Builtin.mload, [Value.word offset] =>
      match lookupWordMap? state.memoryWords offset with
      | some value => some (value, expandMemory state offset 32)
      | none => some (Value.memoryWordAt state.memoryVersion offset,
          expandMemory state offset 32)
  | Evm.Builtin.mstore, [Value.word offset, value] =>
      returnUnit
        (recordMemoryWrite
          { state with
            memoryWords := [(norm offset, value)] } offset 32)
  | Evm.Builtin.mstore8, [Value.word offset, _value] =>
      returnUnit (recordMemoryWrite { state with memoryWords := [] } offset 1)
  | Evm.Builtin.mcopyOp,
      [Value.word dest, Value.word source, Value.word size] =>
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            (expandMemory
              { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.memorySnapshot state.memoryVersion source size) }
              source size)
            dest size)
  | Evm.Builtin.sload, [key] =>
      match lookupAccountValueMap? state.storage state.address key with
      | some value => some (value, state)
      | none => some (Value.storageWord state.address key, state)
  | Evm.Builtin.sstore, [key, value] =>
      returnUnit
        { state with
          storage := writeAccountValueMap state.storage state.address key value }
  | Evm.Builtin.tloadOp, [key] =>
      match lookupAccountValueMap? state.transientStorage state.address key with
      | some value => some (value, state)
      | none => some (Value.transientWord state.address key, state)
  | Evm.Builtin.tstoreOp, [key, value] =>
      returnUnit
        { state with
          transientStorage :=
            writeAccountValueMap state.transientStorage state.address key value }
  | Evm.Builtin.log0Op, [Value.word offset, Value.word size] =>
      returnUnit
        { expandMemory state offset size with
          logs :=
            (0, [],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
                state.logs }
  | Evm.Builtin.log1Op, [Value.word offset, Value.word size, topic0] =>
      returnUnit
        { expandMemory state offset size with
          logs :=
            (1, [topic0],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
                state.logs }
  | Evm.Builtin.log2Op,
      [Value.word offset, Value.word size, topic0, topic1] =>
      returnUnit
        { expandMemory state offset size with
          logs := (2, [topic0, topic1],
            SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs }
  | Evm.Builtin.log3Op,
      [Value.word offset, Value.word size, topic0, topic1, topic2] =>
      returnUnit
        { expandMemory state offset size with
          logs := (3, [topic0, topic1, topic2],
            SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs }
  | Evm.Builtin.log4Op,
      [Value.word offset, Value.word size, topic0, topic1, topic2, topic3] =>
      returnUnit
        { expandMemory state offset size with
          logs := (4, [topic0, topic1, topic2, topic3],
            SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs }
  | Evm.Builtin.callOp,
      [ gas, address, value, Value.word argsOffset, Value.word argsSize
      , Value.word retOffset, Value.word retSize ] =>
      some
        (recordExternalCallEvent Evm.Builtin.callOp
          [ gas, address, value, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state)
  | Evm.Builtin.callcodeOp,
      [ gas, address, value, Value.word argsOffset, Value.word argsSize
      , Value.word retOffset, Value.word retSize ] =>
      some
        (recordExternalCallEvent Evm.Builtin.callcodeOp
          [ gas, address, value, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state)
  | Evm.Builtin.delegatecallOp,
      [ gas, address, Value.word argsOffset, Value.word argsSize
      , Value.word retOffset, Value.word retSize ] =>
      some
        (recordExternalCallEvent Evm.Builtin.delegatecallOp
          [ gas, address, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state)
  | Evm.Builtin.staticcallOp,
      [ gas, address, Value.word argsOffset, Value.word argsSize
      , Value.word retOffset, Value.word retSize ] =>
      some
        (recordExternalCallEvent Evm.Builtin.staticcallOp
          [ gas, address, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state)
  | Evm.Builtin.callOp,
      [gas, address, value, argsOffset, argsSize, retOffset, retSize] =>
      some
        (recordExternalEvent Evm.Builtin.callOp
          [gas, address, value, argsOffset, argsSize, retOffset, retSize] state)
  | Evm.Builtin.callcodeOp,
      [gas, address, value, argsOffset, argsSize, retOffset, retSize] =>
      some
        (recordExternalEvent Evm.Builtin.callcodeOp
          [gas, address, value, argsOffset, argsSize, retOffset, retSize] state)
  | Evm.Builtin.delegatecallOp,
      [gas, address, argsOffset, argsSize, retOffset, retSize] =>
      some
        (recordExternalEvent Evm.Builtin.delegatecallOp
          [gas, address, argsOffset, argsSize, retOffset, retSize] state)
  | Evm.Builtin.staticcallOp,
      [gas, address, argsOffset, argsSize, retOffset, retSize] =>
      some
        (recordExternalEvent Evm.Builtin.staticcallOp
          [gas, address, argsOffset, argsSize, retOffset, retSize] state)
  | Evm.Builtin.returnOp, [Value.word offset, Value.word size] =>
      returnUnit
        (haltWith Evm.HaltKind.returned
          (SymbolicBytes.memorySnapshot state.memoryVersion offset size)
          (expandMemory state offset size))
  | Evm.Builtin.revertOp, [Value.word offset, Value.word size] =>
      returnUnit
        (haltWith Evm.HaltKind.reverted
          (SymbolicBytes.memorySnapshot state.memoryVersion offset size)
          (expandMemory state offset size))
  | Evm.Builtin.invalidOp, [] =>
      returnUnit (haltWith Evm.HaltKind.invalid SymbolicBytes.empty state)
  | Evm.Builtin.createOp, [value, Value.word offset, Value.word size] =>
      some
        (recordExternalCreateEvent Evm.Builtin.createOp
          [value, Value.word offset, Value.word size] offset size state)
  | Evm.Builtin.create2Op, [value, Value.word offset, Value.word size, salt] =>
      some
        (recordExternalCreateEvent Evm.Builtin.create2Op
          [value, Value.word offset, Value.word size, salt] offset size state)
  | Evm.Builtin.createOp, [value, offset, size] =>
      some
        (recordExternalEvent Evm.Builtin.createOp [value, offset, size] state)
  | Evm.Builtin.create2Op, [value, offset, size, salt] =>
      some
        (recordExternalEvent Evm.Builtin.create2Op
          [value, offset, size, salt] state)
  | Evm.Builtin.selfdestructOp, [target] =>
      returnUnit
        (haltWith Evm.HaltKind.stop SymbolicBytes.empty
          (recordExternalUnit Evm.Builtin.selfdestructOp [target] state))
  | Evm.Builtin.balanceOp, [address] =>
      some (Value.unaryBuiltin Evm.Builtin.balanceOp address, state)
  | Evm.Builtin.extcodesizeOp, [address] =>
      some (Value.unaryBuiltin Evm.Builtin.extcodesizeOp address, state)
  | Evm.Builtin.extcodehashOp, [Value.word address] =>
      some (symbolicKeccak (SymbolicBytes.extcodeSlice address 0 0), state)
  | Evm.Builtin.extcodehashOp, [address] =>
      some (Value.unaryBuiltin Evm.Builtin.extcodehashOp address, state)
  | Evm.Builtin.codesizeOp, [] => returnWord (symbolicDataSize state.code) state
  | Evm.Builtin.blockhashOp, [Value.word number] =>
      some (symbolicKeccak (SymbolicBytes.literal s!"blockhash:{number}"), state)
  | Evm.Builtin.blockhashOp, [number] =>
      some (Value.unaryBuiltin Evm.Builtin.blockhashOp number, state)
  | Evm.Builtin.blobhashOp, [Value.word index] =>
      some (symbolicKeccak (SymbolicBytes.literal s!"blobhash:{index}"), state)
  | Evm.Builtin.blobhashOp, [index] =>
      some (Value.unaryBuiltin Evm.Builtin.blobhashOp index, state)
  | Evm.Builtin.setimmutableOp, [_offset, key, value] =>
      returnUnit { state with immutables := writeValueMap state.immutables key value }
  | Evm.Builtin.loadimmutableOp, [key] =>
      match lookupValueMap? state.immutables key with
      | some value => some (value, state)
      | none => some (Value.unaryBuiltin Evm.Builtin.loadimmutableOp key, state)
  | Evm.Builtin.linkersymbolOp, [key] =>
      match lookupValueMap? state.linkerSymbols key with
      | some value => some (value, state)
      | none => some (Value.unaryBuiltin Evm.Builtin.linkersymbolOp key, state)
  | Evm.Builtin.memoryguardOp, [Value.word size] => returnWord size state
  | Evm.Builtin.memoryguardOp, [size] =>
      some (Value.unaryBuiltin Evm.Builtin.memoryguardOp size, state)
  | Evm.Builtin.opaque _, _ => none
  | _, _ => none

theorem evalEvmBuiltin_opaque_none
    (id : Nat) (args : List Value) (state : EvmState) :
    evalEvmBuiltin (Evm.Builtin.opaque id) args state = none := by
  rfl

theorem evalEvmBuiltin_add_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.add [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (addWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.add lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_mul_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.mul [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (mulWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.mul lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_sub_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.sub [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (subWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.sub lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_div_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.divOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (divWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.divOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_sdiv_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.sdivOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (sdivWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.sdivOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_mod_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.modOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (modWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.modOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_smod_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.smodOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (smodWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.smodOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_exp_values
    (base exponent : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.expOp [base, exponent] state =
      match base, exponent with
      | Value.word baseWord, Value.word exponentWord =>
          some (Value.word (expWord baseWord exponentWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.expOp base exponent, state) := by
  cases base <;> cases exponent <;> rfl

theorem evalEvmBuiltin_eq_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.eqOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (eqWord lhsWord rhsWord), state)
      | _, _ =>
          if lhs = rhs then
            some (Value.word 1, state)
          else
            some (Value.binaryBuiltin Evm.Builtin.eqOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_lt_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.ltOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (ltWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.ltOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_gt_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.gtOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (gtWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.gtOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_slt_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.sltOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (sltWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.sltOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_sgt_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.sgtOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (sgtWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.sgtOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_and_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.andOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (andWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.andOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_or_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.orOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (orWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.orOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_xor_values
    (lhs rhs : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.xorOp [lhs, rhs] state =
      match lhs, rhs with
      | Value.word lhsWord, Value.word rhsWord =>
          some (Value.word (xorWord lhsWord rhsWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.xorOp lhs rhs, state) := by
  cases lhs <;> cases rhs <;> rfl

theorem evalEvmBuiltin_shl_values
    (shift value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.shlOp [shift, value] state =
      match shift, value with
      | Value.word shiftWord, Value.word valueWord =>
          some (Value.word (shlWord shiftWord valueWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.shlOp shift value, state) := by
  cases shift <;> cases value <;> rfl

theorem evalEvmBuiltin_shr_values
    (shift value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.shrOp [shift, value] state =
      match shift, value with
      | Value.word shiftWord, Value.word valueWord =>
          some (Value.word (shrWord shiftWord valueWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.shrOp shift value, state) := by
  cases shift <;> cases value <;> rfl

theorem evalEvmBuiltin_sar_values
    (shift value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.sarOp [shift, value] state =
      match shift, value with
      | Value.word shiftWord, Value.word valueWord =>
          some (Value.word (sarWord shiftWord valueWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.sarOp shift value, state) := by
  cases shift <;> cases value <;> rfl

theorem evalEvmBuiltin_signextend_values
    (ix value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.signextendOp [ix, value] state =
      match ix, value with
      | Value.word ixWord, Value.word valueWord =>
          some (Value.word (signextendWord ixWord valueWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.signextendOp ix value, state) := by
  cases ix <;> cases value <;> rfl

theorem evalEvmBuiltin_byte_values
    (ix value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.byteOp [ix, value] state =
      match ix, value with
      | Value.word ixWord, Value.word valueWord =>
          some (Value.word (byteWord ixWord valueWord), state)
      | _, _ =>
          some (Value.binaryBuiltin Evm.Builtin.byteOp ix value, state) := by
  cases ix <;> cases value <;> rfl

theorem evalEvmBuiltin_iszero_values
    (value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.iszero [value] state =
      match value with
      | Value.word word => some (Value.word (iszeroWord word), state)
      | _ => some (Value.unaryBuiltin Evm.Builtin.iszero value, state) := by
  cases value <;> rfl

theorem evalEvmBuiltin_not_values
    (value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.notOp [value] state =
      match value with
      | Value.word word => some (Value.word (notWord word), state)
      | _ => some (Value.unaryBuiltin Evm.Builtin.notOp value, state) := by
  cases value <;> rfl

theorem evalEvmBuiltin_clz_values
    (value : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.clzOp [value] state =
      match value with
      | Value.word word => some (Value.word (clzWord word), state)
      | _ => some (Value.unaryBuiltin Evm.Builtin.clzOp value, state) := by
  cases value <;> rfl

theorem evalEvmBuiltin_addmod_values
    (lhs rhs modulus : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.addmodOp [lhs, rhs, modulus] state =
      match lhs, rhs, modulus with
      | Value.word lhsWord, Value.word rhsWord, Value.word modulusWord =>
          some (Value.word (addmodWord lhsWord rhsWord modulusWord), state)
      | _, _, _ =>
          some
            (Value.ternaryBuiltin Evm.Builtin.addmodOp lhs rhs modulus,
              state) := by
  cases lhs <;> cases rhs <;> cases modulus <;> rfl

theorem evalEvmBuiltin_mulmod_values
    (lhs rhs modulus : Value) (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.mulmodOp [lhs, rhs, modulus] state =
      match lhs, rhs, modulus with
      | Value.word lhsWord, Value.word rhsWord, Value.word modulusWord =>
          some (Value.word (mulmodWord lhsWord rhsWord modulusWord), state)
      | _, _, _ =>
          some
            (Value.ternaryBuiltin Evm.Builtin.mulmodOp lhs rhs modulus,
              state) := by
  cases lhs <;> cases rhs <;> cases modulus <;> rfl

def evalEvmBuiltinValues (builtin : Evm.Builtin) (args : List Value)
    (state : EvmState) : Option (List Value × EvmState) :=
  match builtin with
  | Evm.Builtin.verbatimOp inputs outputs =>
      if args.length = inputs then
        match outputs with
        | 0 =>
            match evalEvmBuiltin builtin args state with
            | some (_, state') => some ([], state')
            | none => none
        | 1 =>
            match evalEvmBuiltin builtin args state with
            | some (value, state') => some ([value], state')
            | none => none
        | _ + 2 => some (recordExternalValueEvents builtin args outputs state)
      else
        none
  | _ =>
      match builtin.signature? with
      | some sig =>
          match sig.resultCount with
          | 0 =>
              match evalEvmBuiltin builtin args state with
              | some (_, state') => some ([], state')
              | none => none
          | 1 =>
              match evalEvmBuiltin builtin args state with
              | some (value, state') => some ([value], state')
              | none => none
          | _ + 2 => none
      | none => none

theorem evalEvmBuiltinValues_opaque_none
    (id : Nat) (args : List Value) (state : EvmState) :
    evalEvmBuiltinValues (Evm.Builtin.opaque id) args state = none := by
  simp [evalEvmBuiltinValues, Evm.Builtin.signature?]

theorem evalEvmBuiltinValues_zero_match_length
    {builtin : Evm.Builtin} {args : List Value}
    {state state' : EvmState} {values : List Value}
    (hEval :
      (match evalEvmBuiltin builtin args state with
      | some (_, nextState) => some ([], nextState)
      | none => none) = some (values, state')) :
    values.length = 0 := by
  cases hBuiltin : evalEvmBuiltin builtin args state with
  | none =>
      simp [hBuiltin] at hEval
  | some pair =>
      cases pair with
      | mk _ nextState =>
          simp [hBuiltin] at hEval
          cases hEval.1
          rfl

theorem evalEvmBuiltinValues_one_match_length
    {builtin : Evm.Builtin} {args : List Value}
    {state state' : EvmState} {values : List Value}
    (hEval :
      (match evalEvmBuiltin builtin args state with
      | some (value, nextState) => some ([value], nextState)
      | none => none) = some (values, state')) :
    values.length = 1 := by
  cases hBuiltin : evalEvmBuiltin builtin args state with
  | none =>
      simp [hBuiltin] at hEval
  | some pair =>
      cases pair with
      | mk value nextState =>
          simp [hBuiltin] at hEval
          cases hEval.1
          rfl

theorem evalEvmBuiltinValues_length_of_signature
    {builtin : Evm.Builtin} {args : List Value}
    {state state' : EvmState} {values : List Value}
    {sig : Evm.BuiltinSignature}
    (hSig : builtin.signature? = some sig)
    (hEval : evalEvmBuiltinValues builtin args state = some (values, state')) :
    values.length = sig.resultCount := by
  cases builtin <;>
    simp [evalEvmBuiltinValues, Evm.Builtin.signature?] at hSig hEval ⊢
  case verbatimOp inputs outputs =>
    subst sig
    rcases hEval with ⟨_, hEval⟩
    cases outputs with
    | zero =>
        exact evalEvmBuiltinValues_zero_match_length hEval
    | succ outputs =>
        cases outputs with
        | zero =>
            exact evalEvmBuiltinValues_one_match_length hEval
        | succ outputs =>
            cases hEval
            simp [externalValueResults_length]
  all_goals
    subst sig
    first
    | exact evalEvmBuiltinValues_zero_match_length hEval
    | exact evalEvmBuiltinValues_one_match_length hEval

theorem evalEvmBuiltin_datacopy_objectData
    (state : EvmState) (dest : Word) (label : DataLabel) (size : Word) :
    evalEvmBuiltin Evm.Builtin.datacopyOp
        [Value.word dest, Value.dataOffset label, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.objectData label size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_calldatacopy_words
    (state : EvmState) (dest offset size : Word) :
    evalEvmBuiltin Evm.Builtin.calldatacopyOp
        [Value.word dest, Value.word offset, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.calldataSlice offset size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_returndatacopy_words
    (state : EvmState) (dest offset size : Word) :
    evalEvmBuiltin Evm.Builtin.returndatacopyOp
        [Value.word dest, Value.word offset, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.returndataSnapshot
                    state.returndataVersion offset size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_codecopy_words
    (state : EvmState) (dest offset size : Word) :
    evalEvmBuiltin Evm.Builtin.codecopyOp
        [Value.word dest, Value.word offset, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.codeSlice offset size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_datacopy_words
    (state : EvmState) (dest offset size : Word) :
    evalEvmBuiltin Evm.Builtin.datacopyOp
        [Value.word dest, Value.word offset, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.codeSlice offset size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_extcodecopy_words
    (state : EvmState) (address dest offset size : Word) :
    evalEvmBuiltin Evm.Builtin.extcodecopyOp
        [ Value.word address, Value.word dest, Value.word offset
        , Value.word size ] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            { state with
              memoryWords := []
              memoryBytes :=
                ObjectMemory.write state.memoryBytes dest
                  (SymbolicBytes.extcodeSlice address offset size) }
            dest size) := by
  rfl

theorem evalEvmBuiltin_sload_present
    (state : EvmState) (key value : Value)
    (hLookup :
      lookupAccountValueMap? state.storage state.address key = some value) :
    evalEvmBuiltin Evm.Builtin.sload [key] state =
      some (value, state) := by
  change
    (match lookupAccountValueMap? state.storage state.address key with
    | some value => some (value, state)
    | none => some (Value.storageWord state.address key, state)) =
      some (value, state)
  rw [hLookup]

theorem evalEvmBuiltin_sload_missing
    (state : EvmState) (key : Value)
    (hLookup :
      lookupAccountValueMap? state.storage state.address key = none) :
    evalEvmBuiltin Evm.Builtin.sload [key] state =
      some (Value.storageWord state.address key, state) := by
  change
    (match lookupAccountValueMap? state.storage state.address key with
    | some value => some (value, state)
    | none => some (Value.storageWord state.address key, state)) =
      some (Value.storageWord state.address key, state)
  rw [hLookup]

theorem evalEvmBuiltin_tload_present
    (state : EvmState) (key value : Value)
    (hLookup :
      lookupAccountValueMap? state.transientStorage state.address key =
        some value) :
    evalEvmBuiltin Evm.Builtin.tloadOp [key] state =
      some (value, state) := by
  change
    (match lookupAccountValueMap? state.transientStorage state.address key with
    | some value => some (value, state)
    | none => some (Value.transientWord state.address key, state)) =
      some (value, state)
  rw [hLookup]

theorem evalEvmBuiltin_tload_missing
    (state : EvmState) (key : Value)
    (hLookup :
      lookupAccountValueMap? state.transientStorage state.address key = none) :
    evalEvmBuiltin Evm.Builtin.tloadOp [key] state =
      some (Value.transientWord state.address key, state) := by
  change
    (match lookupAccountValueMap? state.transientStorage state.address key with
    | some value => some (value, state)
    | none => some (Value.transientWord state.address key, state)) =
      some (Value.transientWord state.address key, state)
  rw [hLookup]

theorem evalEvmBuiltin_sstore_values
    (state : EvmState) (key value : Value) :
    evalEvmBuiltin Evm.Builtin.sstore [key, value] state =
      returnUnit
        { state with
          storage := writeAccountValueMap state.storage state.address key value } := by
  rfl

theorem evalEvmBuiltin_tstore_values
    (state : EvmState) (key value : Value) :
    evalEvmBuiltin Evm.Builtin.tstoreOp [key, value] state =
      returnUnit
        { state with
          transientStorage :=
            writeAccountValueMap state.transientStorage state.address key value } := by
  rfl

theorem evalEvmBuiltin_memoryguard_word
    (state : EvmState) (size : Word) :
    evalEvmBuiltin Evm.Builtin.memoryguardOp [Value.word size] state =
      returnWord size state := by
  rfl

theorem evalEvmBuiltin_calldatasize
    (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.calldatasizeOp [] state =
      returnWord (symbolicDataSize state.calldata) state := by
  rfl

theorem evalEvmBuiltin_calldataload_word
    (state : EvmState) (offset : Word) :
    evalEvmBuiltin Evm.Builtin.calldataloadOp [Value.word offset] state =
      some (Value.calldataWord offset, state) := by
  rfl

theorem evalEvmBuiltin_returndataload_word
    (state : EvmState) (offset : Word) :
    evalEvmBuiltin Evm.Builtin.returndataloadOp [Value.word offset] state =
      some (Value.returndataWordAt state.returndataVersion offset, state) := by
  rfl

theorem evalEvmBuiltin_returndatasize
    (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.returndatasizeOp [] state =
      returnWord (symbolicDataSize state.returndata) state := by
  rfl

theorem evalEvmBuiltin_codesize
    (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.codesizeOp [] state =
      returnWord (symbolicDataSize state.code) state := by
  rfl

theorem evalEvmBuiltin_balance_value
    (state : EvmState) (address : Value) :
    evalEvmBuiltin Evm.Builtin.balanceOp [address] state =
      some (Value.unaryBuiltin Evm.Builtin.balanceOp address, state) := by
  rfl

theorem evalEvmBuiltin_extcodesize_value
    (state : EvmState) (address : Value) :
    evalEvmBuiltin Evm.Builtin.extcodesizeOp [address] state =
      some (Value.unaryBuiltin Evm.Builtin.extcodesizeOp address, state) := by
  rfl

theorem evalEvmBuiltin_extcodehash_word
    (state : EvmState) (address : Word) :
    evalEvmBuiltin Evm.Builtin.extcodehashOp [Value.word address] state =
      some (symbolicKeccak (SymbolicBytes.extcodeSlice address 0 0), state) := by
  rfl

theorem evalEvmBuiltin_blockhash_word
    (state : EvmState) (number : Word) :
    evalEvmBuiltin Evm.Builtin.blockhashOp [Value.word number] state =
      some (symbolicKeccak (SymbolicBytes.literal s!"blockhash:{number}"), state) := by
  rfl

theorem evalEvmBuiltin_blobhash_word
    (state : EvmState) (index : Word) :
    evalEvmBuiltin Evm.Builtin.blobhashOp [Value.word index] state =
      some (symbolicKeccak (SymbolicBytes.literal s!"blobhash:{index}"), state) := by
  rfl

theorem evalEvmBuiltin_mload_present
    (state : EvmState) (offset : Word) (value : Value)
    (hLookup : lookupWordMap? state.memoryWords offset = some value) :
    evalEvmBuiltin Evm.Builtin.mload [Value.word offset] state =
      some (value, expandMemory state offset 32) := by
  change
    (match lookupWordMap? state.memoryWords offset with
    | some value => some (value, expandMemory state offset 32)
    | none => some (Value.memoryWordAt state.memoryVersion offset,
        expandMemory state offset 32)) =
      some (value, expandMemory state offset 32)
  rw [hLookup]

theorem evalEvmBuiltin_mload_missing
    (state : EvmState) (offset : Word)
    (hLookup : lookupWordMap? state.memoryWords offset = none) :
    evalEvmBuiltin Evm.Builtin.mload [Value.word offset] state =
      some (Value.memoryWordAt state.memoryVersion offset,
        expandMemory state offset 32) := by
  change
    (match lookupWordMap? state.memoryWords offset with
    | some value => some (value, expandMemory state offset 32)
    | none => some (Value.memoryWordAt state.memoryVersion offset,
        expandMemory state offset 32)) =
      some (Value.memoryWordAt state.memoryVersion offset,
        expandMemory state offset 32)
  rw [hLookup]

theorem evalEvmBuiltin_mstore_value
    (state : EvmState) (offset : Word) (value : Value) :
    evalEvmBuiltin Evm.Builtin.mstore [Value.word offset, value] state =
      returnUnit
        (recordMemoryWrite
          { state with memoryWords := [(norm offset, value)] } offset 32) := by
  rfl

theorem evalEvmBuiltin_mstore8_value
    (state : EvmState) (offset : Word) (value : Value) :
    evalEvmBuiltin Evm.Builtin.mstore8 [Value.word offset, value] state =
      returnUnit
        (recordMemoryWrite { state with memoryWords := [] } offset 1) := by
  rfl

theorem evalEvmBuiltin_keccak256_words
    (state : EvmState) (offset size : Word) :
    evalEvmBuiltin Evm.Builtin.keccak256Op
        [Value.word offset, Value.word size] state =
      some
        ( symbolicKeccak
            (SymbolicBytes.memorySnapshot state.memoryVersion offset size)
        , expandMemory state offset size ) := by
  rfl

theorem evalEvmBuiltin_return_words
    (state : EvmState) (offset size : Word) :
    evalEvmBuiltin Evm.Builtin.returnOp [Value.word offset, Value.word size] state =
      returnUnit
        (haltWith Evm.HaltKind.returned
          (SymbolicBytes.memorySnapshot state.memoryVersion offset size)
          (expandMemory state offset size)) := by
  rfl

theorem evalEvmBuiltin_revert_words
    (state : EvmState) (offset size : Word) :
    evalEvmBuiltin Evm.Builtin.revertOp [Value.word offset, Value.word size] state =
      returnUnit
        (haltWith Evm.HaltKind.reverted
          (SymbolicBytes.memorySnapshot state.memoryVersion offset size)
          (expandMemory state offset size)) := by
  rfl

theorem evalEvmBuiltin_mcopy_words
    (state : EvmState) (dest source size : Word) :
    evalEvmBuiltin Evm.Builtin.mcopyOp
        [Value.word dest, Value.word source, Value.word size] state =
      if norm size = 0 then
        returnUnit state
      else
        returnUnit
          (recordMemoryWrite
            (expandMemory
              { state with
                memoryWords := []
                memoryBytes :=
                  ObjectMemory.write state.memoryBytes dest
                    (SymbolicBytes.memorySnapshot state.memoryVersion source size) }
              source size)
            dest size) := by
  rfl

theorem evalEvmBuiltin_loadimmutable_present
    (state : EvmState) (key value : Value)
    (hLookup : lookupValueMap? state.immutables key = some value) :
    evalEvmBuiltin Evm.Builtin.loadimmutableOp [key] state =
      some (value, state) := by
  change
    (match lookupValueMap? state.immutables key with
    | some value => some (value, state)
    | none => some (Value.unaryBuiltin Evm.Builtin.loadimmutableOp key, state)) =
      some (value, state)
  rw [hLookup]

theorem evalEvmBuiltin_loadimmutable_missing
    (state : EvmState) (key : Value)
    (hLookup : lookupValueMap? state.immutables key = none) :
    evalEvmBuiltin Evm.Builtin.loadimmutableOp [key] state =
      some (Value.unaryBuiltin Evm.Builtin.loadimmutableOp key, state) := by
  change
    (match lookupValueMap? state.immutables key with
    | some value => some (value, state)
    | none => some (Value.unaryBuiltin Evm.Builtin.loadimmutableOp key, state)) =
      some (Value.unaryBuiltin Evm.Builtin.loadimmutableOp key, state)
  rw [hLookup]

theorem evalEvmBuiltin_linkersymbol_present
    (state : EvmState) (key value : Value)
    (hLookup : lookupValueMap? state.linkerSymbols key = some value) :
    evalEvmBuiltin Evm.Builtin.linkersymbolOp [key] state =
      some (value, state) := by
  change
    (match lookupValueMap? state.linkerSymbols key with
    | some value => some (value, state)
    | none => some (Value.unaryBuiltin Evm.Builtin.linkersymbolOp key, state)) =
      some (value, state)
  rw [hLookup]

theorem evalEvmBuiltin_linkersymbol_missing
    (state : EvmState) (key : Value)
    (hLookup : lookupValueMap? state.linkerSymbols key = none) :
    evalEvmBuiltin Evm.Builtin.linkersymbolOp [key] state =
      some (Value.unaryBuiltin Evm.Builtin.linkersymbolOp key, state) := by
  change
    (match lookupValueMap? state.linkerSymbols key with
    | some value => some (value, state)
    | none => some (Value.unaryBuiltin Evm.Builtin.linkersymbolOp key, state)) =
      some (Value.unaryBuiltin Evm.Builtin.linkersymbolOp key, state)
  rw [hLookup]

theorem evalEvmBuiltin_setimmutable_values
    (state : EvmState) (offset key value : Value) :
    evalEvmBuiltin Evm.Builtin.setimmutableOp [offset, key, value] state =
      returnUnit
        { state with immutables := writeValueMap state.immutables key value } := by
  rfl

theorem evalEvmBuiltin_stop
    (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.stopOp [] state =
      returnUnit (haltWith Evm.HaltKind.stop SymbolicBytes.empty state) := by
  rfl

theorem evalEvmBuiltin_pop_value
    (state : EvmState) (value : Value) :
    evalEvmBuiltin Evm.Builtin.popOp [value] state =
      returnUnit state := by
  rfl

theorem evalEvmBuiltin_invalid
    (state : EvmState) :
    evalEvmBuiltin Evm.Builtin.invalidOp [] state =
      returnUnit (haltWith Evm.HaltKind.invalid SymbolicBytes.empty state) := by
  rfl

theorem evalEvmBuiltin_selfdestruct_value
    (state : EvmState) (target : Value) :
    evalEvmBuiltin Evm.Builtin.selfdestructOp [target] state =
      returnUnit
        (haltWith Evm.HaltKind.stop SymbolicBytes.empty
          (recordExternalUnit Evm.Builtin.selfdestructOp [target] state)) := by
  rfl

theorem evalEvmBuiltin_call_values
    (state : EvmState) (gas address value : Value)
    (argsOffset argsSize retOffset retSize : Word) :
    evalEvmBuiltin Evm.Builtin.callOp
        [ gas, address, value, Value.word argsOffset, Value.word argsSize
        , Value.word retOffset, Value.word retSize ] state =
      some
        (recordExternalCallEvent Evm.Builtin.callOp
          [ gas, address, value, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state) := by
  rfl

theorem evalEvmBuiltin_callcode_values
    (state : EvmState) (gas address value : Value)
    (argsOffset argsSize retOffset retSize : Word) :
    evalEvmBuiltin Evm.Builtin.callcodeOp
        [ gas, address, value, Value.word argsOffset, Value.word argsSize
        , Value.word retOffset, Value.word retSize ] state =
      some
        (recordExternalCallEvent Evm.Builtin.callcodeOp
          [ gas, address, value, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state) := by
  rfl

theorem evalEvmBuiltin_delegatecall_values
    (state : EvmState) (gas address : Value)
    (argsOffset argsSize retOffset retSize : Word) :
    evalEvmBuiltin Evm.Builtin.delegatecallOp
        [ gas, address, Value.word argsOffset, Value.word argsSize
        , Value.word retOffset, Value.word retSize ] state =
      some
        (recordExternalCallEvent Evm.Builtin.delegatecallOp
          [ gas, address, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state) := by
  rfl

theorem evalEvmBuiltin_staticcall_values
    (state : EvmState) (gas address : Value)
    (argsOffset argsSize retOffset retSize : Word) :
    evalEvmBuiltin Evm.Builtin.staticcallOp
        [ gas, address, Value.word argsOffset, Value.word argsSize
        , Value.word retOffset, Value.word retSize ] state =
      some
        (recordExternalCallEvent Evm.Builtin.staticcallOp
          [ gas, address, Value.word argsOffset, Value.word argsSize
          , Value.word retOffset, Value.word retSize ]
          argsOffset argsSize retOffset retSize state) := by
  rfl

theorem evalEvmBuiltin_create_values
    (state : EvmState) (value : Value) (offset size : Word) :
    evalEvmBuiltin Evm.Builtin.createOp
        [value, Value.word offset, Value.word size] state =
      some
        (recordExternalCreateEvent Evm.Builtin.createOp
          [value, Value.word offset, Value.word size] offset size state) := by
  rfl

theorem evalEvmBuiltin_create2_values
    (state : EvmState) (value : Value) (offset size : Word) (salt : Value) :
    evalEvmBuiltin Evm.Builtin.create2Op
        [value, Value.word offset, Value.word size, salt] state =
      some
        (recordExternalCreateEvent Evm.Builtin.create2Op
          [value, Value.word offset, Value.word size, salt] offset size
          state) := by
  rfl

theorem evalEvmBuiltin_verbatim_zero_args
    (state : EvmState) (inputs : Nat) (args : List Value)
    (hArgs : args.length = inputs) :
    evalEvmBuiltin (Evm.Builtin.verbatimOp inputs 0) args state =
      returnUnit
        (recordExternalUnit (Evm.Builtin.verbatimOp inputs 0) args state) := by
  subst inputs
  change
    (if args.length = args.length then
      returnUnit
        (recordExternalUnit (Evm.Builtin.verbatimOp args.length 0) args
          state)
    else none) =
      returnUnit
        (recordExternalUnit (Evm.Builtin.verbatimOp args.length 0) args
          state)
  simp

theorem evalEvmBuiltin_verbatim_one_args
    (state : EvmState) (inputs : Nat) (args : List Value)
    (hArgs : args.length = inputs) :
    evalEvmBuiltin (Evm.Builtin.verbatimOp inputs 1) args state =
      some
        (recordExternalValueEvent (Evm.Builtin.verbatimOp inputs 1) args
          state) := by
  subst inputs
  change
    (if args.length = args.length then
      some
        (recordExternalValueEvent (Evm.Builtin.verbatimOp args.length 1)
          args state)
    else none) =
      some
        (recordExternalValueEvent (Evm.Builtin.verbatimOp args.length 1)
          args state)
  simp

theorem evalEvmBuiltin_log0_words
    (state : EvmState) (offset size : Word) :
    evalEvmBuiltin Evm.Builtin.log0Op
        [Value.word offset, Value.word size] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (0, [],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs } := by
  rfl

theorem evalEvmBuiltin_log1_words
    (state : EvmState) (offset size : Word) (topic0 : Value) :
    evalEvmBuiltin Evm.Builtin.log1Op
        [Value.word offset, Value.word size, topic0] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (1, [topic0],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs } := by
  rfl

theorem evalEvmBuiltin_log2_words
    (state : EvmState) (offset size : Word) (topic0 topic1 : Value) :
    evalEvmBuiltin Evm.Builtin.log2Op
        [Value.word offset, Value.word size, topic0, topic1] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (2, [topic0, topic1],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs } := by
  rfl

theorem evalEvmBuiltin_log3_words
    (state : EvmState) (offset size : Word)
    (topic0 topic1 topic2 : Value) :
    evalEvmBuiltin Evm.Builtin.log3Op
        [Value.word offset, Value.word size, topic0, topic1, topic2] state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (3, [topic0, topic1, topic2],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs } := by
  rfl

theorem evalEvmBuiltin_log4_words
    (state : EvmState) (offset size : Word)
    (topic0 topic1 topic2 topic3 : Value) :
    evalEvmBuiltin Evm.Builtin.log4Op
        [Value.word offset, Value.word size, topic0, topic1, topic2, topic3]
        state =
      returnUnit
        { expandMemory state offset size with
          logs :=
            (4, [topic0, topic1, topic2, topic3],
              SymbolicBytes.memorySnapshot state.memoryVersion offset size) ::
              state.logs } := by
  rfl

structure FunctionDef where
  params : List Name
  returns : List Name
  body : Stmt
  deriving Repr

abbrev FunctionEnv := List (Name × FunctionDef)

def lookupFunction? : FunctionEnv -> Name -> Option FunctionDef
  | [], _ => none
  | (candidate, fn) :: rest, name =>
      if candidate = name then some fn else lookupFunction? rest name

def declareFunction (funcs : FunctionEnv) (name : Name)
    (fn : FunctionDef) : FunctionEnv :=
  match lookupFunction? funcs name with
  | some _ => funcs
  | none => (name, fn) :: funcs

def collectStmtFunctionDefs : Stmt -> FunctionEnv -> FunctionEnv
  | Stmt.funDef name params returns body, funcs =>
      declareFunction funcs name { params := params, returns := returns, body := body }
  | Stmt.seq first second, funcs =>
      collectStmtFunctionDefs second (collectStmtFunctionDefs first funcs)
  | _, funcs => funcs

def collectBlockFunctionDefs : List Stmt -> FunctionEnv -> FunctionEnv
  | [], funcs => funcs
  | stmt :: rest, funcs =>
      collectBlockFunctionDefs rest (collectStmtFunctionDefs stmt funcs)

def valuesForNames? (env : Env) : List Name -> Option (List Value)
  | [] => some []
  | name :: rest =>
      match lookup? env name, valuesForNames? env rest with
      | some value, some values => some (value :: values)
      | _, _ => none

def initFunctionEnv (params : List Name) (args : List Value)
    (returns : List Name) : Option Env :=
  match declareMany? [] params args with
  | some paramEnv =>
      declareMany? paramEnv returns (returns.map (fun _ => Value.word 0))
  | none => none

mutual
  def evalProgramStmtFuel : Nat -> FunctionEnv -> Env -> Stmt ->
      Option FlowResult
    | 0, _, _, _ => none
    | _fuel + 1, _, env, Stmt.skip => some (normalResult env)
    | _fuel + 1, _, env, Stmt.expr expr =>
        match evalExpr env expr with
        | some _ => some (normalResult env)
        | none => none
    | _fuel + 1, _, env, Stmt.let1 name init =>
        match init with
        | some expr =>
            match evalExpr env expr with
            | some value =>
                match declare? env name value with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none =>
            match declare? env name (Value.word 0) with
            | some env' => some (normalResult env')
            | none => none
    | _fuel + 1, _, env, Stmt.letMany names init =>
        match init with
        | some exprs =>
            match evalExprs env exprs with
            | some values =>
                match declareMany? env names values with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none =>
            match declareMany? env names (names.map (fun _ => Value.word 0)) with
            | some env' => some (normalResult env')
            | none => none
    | _fuel + 1, _, env, Stmt.funDef _ _ _ _ =>
        some (normalResult env)
    | _fuel + 1, _, env, Stmt.assign name expr =>
        match evalExpr env expr with
        | some value =>
            match assign? env name value with
            | some env' => some (normalResult env')
            | none => none
        | none => none
    | _fuel + 1, _, env, Stmt.assignMany names exprs =>
        match evalExprs env exprs with
        | some values =>
            match assignMany? env names values with
            | some env' => some (normalResult env')
            | none => none
        | none => none
    | fuel + 1, funcs, env, Stmt.letCall names fnName args =>
        match evalExprs env args with
        | some argValues =>
            match evalFunctionFuel fuel funcs fnName argValues with
            | some returnValues =>
                match declareMany? env names returnValues with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none => none
    | fuel + 1, funcs, env, Stmt.assignCall names fnName args =>
        match evalExprs env args with
        | some argValues =>
            match evalFunctionFuel fuel funcs fnName argValues with
            | some returnValues =>
                match assignMany? env names returnValues with
                | some env' => some (normalResult env')
                | none => none
            | none => none
        | none => none
    | fuel + 1, funcs, env, Stmt.seq first second =>
        let funcs := collectStmtFunctionDefs (Stmt.seq first second) funcs
        match evalProgramStmtFuel fuel funcs env first with
        | some { flow := Flow.normal, env := env' } =>
            evalProgramStmtFuel fuel funcs env' second
        | some result => some result
        | none => none
    | fuel + 1, funcs, env, Stmt.block stmts =>
        let funcs := collectBlockFunctionDefs stmts funcs
        match evalProgramBlockFuel fuel funcs env stmts with
        | some result => withRestoredEnv env result
        | none => none
    | fuel + 1, funcs, env, Stmt.ifThen cond body =>
        match evalExpr env cond with
        | some value =>
            match valueAsBool value with
            | some true => evalProgramStmtFuel fuel funcs env body
            | some false => some (normalResult env)
            | none => none
        | none => none
    | fuel + 1, funcs, env, Stmt.switch discr cases defaultBranch =>
        match evalExpr env discr with
        | some value =>
            match switchTarget? value cases defaultBranch with
            | some branch => evalProgramStmtFuel fuel funcs env branch
            | none => some (normalResult env)
        | none => none
    | fuel + 1, funcs, env, Stmt.forLoop pre cond post body =>
        match evalProgramStmtFuel fuel funcs env pre with
        | some { flow := Flow.normal, env := loopEnv } =>
            evalProgramForFuel fuel funcs env loopEnv cond post body
        | some result => withRestoredEnv env result
        | none => none
    | _fuel + 1, _, env, Stmt.break =>
        some { flow := Flow.broke, env := env }
    | _fuel + 1, _, env, Stmt.continue =>
        some { flow := Flow.continued, env := env }
    | _fuel + 1, _, env, Stmt.leave =>
        some { flow := Flow.left, env := env }

  def evalProgramBlockFuel : Nat -> FunctionEnv -> Env -> List Stmt ->
      Option FlowResult
    | 0, _, _, _ => none
    | _fuel + 1, _, env, [] => some (normalResult env)
    | fuel + 1, funcs, env, stmt :: rest =>
        match evalProgramStmtFuel fuel funcs env stmt with
        | some { flow := Flow.normal, env := env' } =>
            evalProgramBlockFuel fuel funcs env' rest
        | some result => some result
        | none => none

  def evalProgramForFuel : Nat -> FunctionEnv -> Env -> Env -> Expr -> Stmt ->
      Stmt -> Option FlowResult
    | 0, _, _, _, _, _, _ => none
    | fuel + 1, funcs, outer, loopEnv, cond, post, body =>
        match evalExpr loopEnv cond with
        | some value =>
            match valueAsBool value with
            | some false => withRestoredFlow outer loopEnv Flow.normal
            | some true =>
                match evalProgramStmtFuel fuel funcs loopEnv body with
                | some { flow := Flow.normal, env := bodyEnv } =>
                    match evalProgramStmtFuel fuel funcs bodyEnv post with
                    | some { flow := Flow.normal, env := postEnv } =>
                        evalProgramForFuel fuel funcs outer postEnv cond post body
                    | some { flow := Flow.continued, env := postEnv } =>
                        evalProgramForFuel fuel funcs outer postEnv cond post body
                    | some { flow := Flow.broke, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.normal
                    | some { flow := Flow.left, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.left
                    | some { flow := Flow.halted, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.halted
                    | none => none
                | some { flow := Flow.continued, env := bodyEnv } =>
                    match evalProgramStmtFuel fuel funcs bodyEnv post with
                    | some { flow := Flow.normal, env := postEnv } =>
                        evalProgramForFuel fuel funcs outer postEnv cond post body
                    | some { flow := Flow.continued, env := postEnv } =>
                        evalProgramForFuel fuel funcs outer postEnv cond post body
                    | some { flow := Flow.broke, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.normal
                    | some { flow := Flow.left, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.left
                    | some { flow := Flow.halted, env := postEnv } =>
                        withRestoredFlow outer postEnv Flow.halted
                    | none => none
                | some { flow := Flow.broke, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.normal
                | some { flow := Flow.left, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.left
                | some { flow := Flow.halted, env := bodyEnv } =>
                    withRestoredFlow outer bodyEnv Flow.halted
                | none => none
            | none => none
        | none => none

  def evalFunctionFuel : Nat -> FunctionEnv -> Name -> List Value ->
      Option (List Value)
    | 0, _, _, _ => none
    | fuel + 1, funcs, fnName, args =>
        match lookupFunction? funcs fnName with
        | some fn =>
            match initFunctionEnv fn.params args fn.returns with
            | some callEnv =>
                let funcs := collectStmtFunctionDefs fn.body funcs
                match evalProgramStmtFuel fuel funcs callEnv fn.body with
                | some { flow := Flow.normal, env := env' } =>
                    valuesForNames? env' fn.returns
                | some { flow := Flow.left, env := env' } =>
                    valuesForNames? env' fn.returns
                | some _ => none
                | none => none
            | none => none
        | none => none
end

def containsName : List Name -> Name -> Bool
  | [], _ => false
  | candidate :: rest, name =>
      if candidate = name then true else containsName rest name

def namesUnique : List Name -> Bool
  | [] => true
  | name :: rest => !containsName rest name && namesUnique rest

def addScopedName? (scope : List Name) (name : Name) : Option (List Name) :=
  if containsName scope name then none else some (name :: scope)

def addScopedNames? : List Name -> List Name -> Option (List Name)
  | scope, [] => some scope
  | scope, name :: rest =>
      match addScopedName? scope name with
      | some scope' => addScopedNames? scope' rest
      | none => none

def namesInScope : List Name -> List Name -> Bool
  | _, [] => true
  | scope, name :: rest =>
      containsName scope name && namesInScope scope rest

structure FunctionSig where
  paramCount : Nat
  returnCount : Nat
  deriving DecidableEq, Repr

abbrev FunctionScope := List (Name × FunctionSig)

def lookupFunctionSig? : FunctionScope -> Name -> Option FunctionSig
  | [], _ => none
  | (candidate, sig) :: rest, name =>
      if candidate = name then some sig else lookupFunctionSig? rest name

def addFunctionSig? (scope : FunctionScope) (name : Name)
    (sig : FunctionSig) : Option FunctionScope :=
  match lookupFunctionSig? scope name with
  | some _ => none
  | none => some ((name, sig) :: scope)

def containsFunctionName : FunctionScope -> Name -> Bool
  | [], _ => false
  | (candidate, _) :: rest, name =>
      if candidate = name then true else containsFunctionName rest name

structure StaticContext where
  vars : List Name
  funcs : FunctionScope
  deriving DecidableEq, Repr

def StaticContext.empty : StaticContext :=
  { vars := [], funcs := [] }

def addVarName? (ctx : StaticContext) (name : Name) :
    Option StaticContext :=
  if containsFunctionName ctx.funcs name then
    none
  else
    match addScopedName? ctx.vars name with
    | some vars' => some { ctx with vars := vars' }
    | none => none

def addVarNames? : StaticContext -> List Name -> Option StaticContext
  | ctx, [] => some ctx
  | ctx, name :: rest =>
      match addVarName? ctx name with
      | some ctx' => addVarNames? ctx' rest
      | none => none

def addFunctionSigNoShadow? (ctx : StaticContext) (name : Name)
    (sig : FunctionSig) : Option StaticContext :=
  if containsName ctx.vars name then
    none
  else
    match addFunctionSig? ctx.funcs name sig with
    | some funcs' => some { ctx with funcs := funcs' }
    | none => none

def addFunctionLocalName? (visible : StaticContext)
    (locals : List Name) (name : Name) : Option (List Name) :=
  if containsName visible.vars name || containsFunctionName visible.funcs name ||
      containsName locals name then
    none
  else
    some (name :: locals)

def addFunctionLocalNames? (visible : StaticContext) :
    List Name -> List Name -> Option (List Name)
  | locals, [] => some locals
  | locals, name :: rest =>
      match addFunctionLocalName? visible locals name with
      | some locals' => addFunctionLocalNames? visible locals' rest
      | none => none

def initFunctionStaticVars? (visible : StaticContext)
    (params returns : List Name) : Option (List Name) :=
  match addFunctionLocalNames? visible [] params with
  | some paramVars => addFunctionLocalNames? visible paramVars returns
  | none => none

mutual
  def predeclareStmtFunctionSigs? : StaticContext -> Stmt ->
      Option StaticContext
    | ctx, Stmt.funDef name params returns _ =>
        addFunctionSigNoShadow? ctx name
          { paramCount := params.length, returnCount := returns.length }
    | ctx, Stmt.seq first second =>
        match predeclareStmtFunctionSigs? ctx first with
        | some ctx' => predeclareStmtFunctionSigs? ctx' second
        | none => none
    | ctx, _ => some ctx

  def predeclareBlockFunctionSigs? : StaticContext -> List Stmt ->
      Option StaticContext
    | ctx, [] => some ctx
    | ctx, stmt :: rest =>
        match predeclareStmtFunctionSigs? ctx stmt with
        | some ctx' => predeclareBlockFunctionSigs? ctx' rest
        | none => none
end

mutual
  def checkExpr (ctx : StaticContext) : Expr -> Bool
    | Expr.value _ => true
    | Expr.var name => containsName ctx.vars name
    | Expr.keccak _ => true
    | Expr.dataSize _ => true
    | Expr.dataOffset _ => true
    | Expr.builtin builtin args =>
        match builtin.signature? with
        | some sig =>
            decide (sig.paramCount = args.length) &&
              decide (sig.resultCount = 1) &&
              checkExprs ctx args
        | none => false

  def checkStmtExpr (ctx : StaticContext) : Expr -> Bool
    | Expr.builtin builtin args =>
        match builtin.signature? with
        | some sig =>
          decide (sig.paramCount = args.length) &&
              decide (sig.resultCount = 0) &&
              checkExprs ctx args
        | none => false
    | _ => false

  def checkExprs (ctx : StaticContext) : List Expr -> Bool
    | [] => true
    | expr :: rest => checkExpr ctx expr && checkExprs ctx rest
end

def checkExprsAsYulValues (ctx : StaticContext) (exprs : List Expr)
    (resultCount : Nat) : Bool :=
  match exprs with
  | [Expr.builtin builtin args] =>
      match builtin.signature? with
      | some sig =>
          decide (sig.paramCount = args.length) &&
            decide (sig.resultCount = resultCount) &&
            checkExprs ctx args
      | none => false
  | _ => checkExprs ctx exprs && decide (resultCount = exprs.length)

mutual
  def checkStmtFuel : Nat -> StaticContext -> Bool -> Bool -> Stmt ->
      Option StaticContext
    | 0, _, _, _, _ => none
    | _fuel + 1, ctx, _, _, Stmt.skip => some ctx
    | _fuel + 1, ctx, _, _, Stmt.expr expr =>
        if checkStmtExpr ctx expr then some ctx else none
    | _fuel + 1, ctx, _, _, Stmt.let1 name init =>
        match init with
        | some expr =>
            if checkExpr ctx expr then
              match addVarName? ctx name with
              | some ctx' => some ctx'
              | none => none
            else none
        | none =>
            match addVarName? ctx name with
            | some ctx' => some ctx'
            | none => none
    | _fuel + 1, ctx, _, _, Stmt.letMany names init =>
        match init with
        | some exprs =>
            if checkExprsAsYulValues ctx exprs names.length then
              match addVarNames? ctx names with
              | some ctx' => some ctx'
              | none => none
            else none
        | none =>
            match addVarNames? ctx names with
            | some ctx' => some ctx'
            | none => none
    | fuel + 1, ctx, _, _, Stmt.funDef name params returns body =>
        let sig := { paramCount := params.length, returnCount := returns.length }
        let checkBodyWith (ctx' : StaticContext) :=
          match initFunctionStaticVars? ctx' params returns with
          | some fnVars =>
              match checkStmtFuel fuel { vars := fnVars, funcs := ctx'.funcs }
                  false true body with
              | some _ => some ctx'
              | none => none
          | none => none
        match lookupFunctionSig? ctx.funcs name with
        | some existing =>
            if existing = sig then checkBodyWith ctx else none
        | none =>
            match addFunctionSigNoShadow? ctx name sig with
            | some ctx' => checkBodyWith ctx'
            | none => none
    | _fuel + 1, ctx, _, _, Stmt.assign name expr =>
        if containsName ctx.vars name && checkExpr ctx expr then some ctx else none
    | _fuel + 1, ctx, _, _, Stmt.assignMany names exprs =>
        if namesUnique names && namesInScope ctx.vars names &&
            checkExprsAsYulValues ctx exprs names.length then
          some ctx
        else none
    | _fuel + 1, ctx, _, _, Stmt.letCall names fnName args =>
        match lookupFunctionSig? ctx.funcs fnName with
        | some sig =>
            if checkExprs ctx args && decide (sig.paramCount = args.length) &&
                decide (sig.returnCount = names.length) then
              match addVarNames? ctx names with
              | some ctx' => some ctx'
              | none => none
            else none
        | none => none
    | _fuel + 1, ctx, _, _, Stmt.assignCall names fnName args =>
        match lookupFunctionSig? ctx.funcs fnName with
        | some sig =>
            if namesUnique names && namesInScope ctx.vars names && checkExprs ctx args &&
                decide (sig.paramCount = args.length) &&
                decide (sig.returnCount = names.length) then
              some ctx
            else none
        | none => none
    | fuel + 1, ctx, inLoop, inFunction, Stmt.seq first second =>
        match predeclareStmtFunctionSigs? ctx (Stmt.seq first second) with
        | some seqCtx =>
            match checkStmtFuel fuel seqCtx inLoop inFunction first with
            | some ctx' => checkStmtFuel fuel ctx' inLoop inFunction second
            | none => none
        | none => none
    | fuel + 1, ctx, inLoop, inFunction, Stmt.block stmts =>
        match predeclareBlockFunctionSigs? ctx stmts with
        | some blockCtx =>
            match checkBlockFuel fuel blockCtx inLoop inFunction stmts with
            | some _ => some ctx
            | none => none
        | none => none
    | fuel + 1, ctx, inLoop, inFunction, Stmt.ifThen cond body =>
        if checkExpr ctx cond then
          match checkStmtFuel fuel ctx inLoop inFunction body with
          | some _ => some ctx
          | none => none
        else none
    | fuel + 1, ctx, inLoop, inFunction, Stmt.switch discr cases defaultBranch =>
        if checkExpr ctx discr && switchHasBranch cases defaultBranch &&
            switchCaseLabelsUnique cases then
          match checkSwitchCasesFuel fuel ctx inLoop inFunction cases with
          | some _ =>
              match defaultBranch with
              | some branch =>
                  match checkStmtFuel fuel ctx inLoop inFunction branch with
                  | some _ => some ctx
                  | none => none
              | none => some ctx
          | none => none
        else none
    | fuel + 1, ctx, _, inFunction, Stmt.forLoop pre cond post body =>
        if stmtHasNoFunDefs pre then
          match checkStmtFuel fuel ctx false inFunction pre with
          | some loopCtx =>
              if checkExpr loopCtx cond then
                match checkStmtFuel fuel loopCtx true inFunction body,
                    checkStmtFuel fuel loopCtx false inFunction post with
                | some _, some _ => some ctx
                | _, _ => none
              else none
          | none => none
        else none
    | _fuel + 1, ctx, inLoop, _, Stmt.break =>
        if inLoop then some ctx else none
    | _fuel + 1, ctx, inLoop, _, Stmt.continue =>
        if inLoop then some ctx else none
    | _fuel + 1, ctx, _, inFunction, Stmt.leave =>
        if inFunction then some ctx else none

  def checkBlockFuel : Nat -> StaticContext -> Bool -> Bool -> List Stmt ->
      Option StaticContext
    | 0, _, _, _, _ => none
    | _fuel + 1, ctx, _, _, [] => some ctx
    | fuel + 1, ctx, inLoop, inFunction, stmt :: rest =>
        match checkStmtFuel fuel ctx inLoop inFunction stmt with
        | some ctx' => checkBlockFuel fuel ctx' inLoop inFunction rest
        | none => none

  def checkSwitchCasesFuel : Nat -> StaticContext -> Bool -> Bool ->
      List (Value × Stmt) -> Option Unit
    | 0, _, _, _, _ => none
    | _fuel + 1, _, _, _, [] => some ()
    | fuel + 1, ctx, inLoop, inFunction, (_, branch) :: rest =>
        match checkStmtFuel fuel ctx inLoop inFunction branch,
            checkSwitchCasesFuel fuel ctx inLoop inFunction rest with
        | some _, some _ => some ()
        | _, _ => none
end

theorem evalExpr_keccak (env : Env) (bytes : SymbolicBytes) :
    evalExpr env (Expr.keccak bytes) = some (symbolicKeccak bytes) := by
  rfl

theorem evalControlStmtFuel_zero (env : Env) (stmt : Stmt) :
    evalControlStmtFuel 0 env stmt = none := by
  rfl

theorem evalControlBlockFuel_zero (env : Env) (stmts : List Stmt) :
    evalControlBlockFuel 0 env stmts = none := by
  rfl

theorem evalControlForFuel_zero
    (outer loopEnv : Env) (cond : Expr) (post body : Stmt) :
    evalControlForFuel 0 outer loopEnv cond post body = none := by
  rfl

theorem evalProgramStmtFuel_zero
    (funcs : FunctionEnv) (env : Env) (stmt : Stmt) :
    evalProgramStmtFuel 0 funcs env stmt = none := by
  rfl

theorem evalProgramBlockFuel_zero
    (funcs : FunctionEnv) (env : Env) (stmts : List Stmt) :
    evalProgramBlockFuel 0 funcs env stmts = none := by
  rfl

theorem evalProgramForFuel_zero
    (funcs : FunctionEnv) (outer loopEnv : Env) (cond : Expr)
    (post body : Stmt) :
    evalProgramForFuel 0 funcs outer loopEnv cond post body = none := by
  rfl

theorem evalFunctionFuel_zero
    (funcs : FunctionEnv) (name : Name) (args : List Value) :
    evalFunctionFuel 0 funcs name args = none := by
  rfl

theorem evalExprs_cons_success {env : Env} {expr : Expr} {rest : List Expr}
    {value : Value} {values : List Value}
    (hRest : evalExprs env rest = some values)
    (hExpr : evalExpr env expr = some value) :
    evalExprs env (expr :: rest) = some (value :: values) := by
  simp [evalExprs, hRest, hExpr]

theorem evalExprs_cons_rest_failure {env : Env} {expr : Expr}
    {rest : List Expr}
    (hRest : evalExprs env rest = none) :
    evalExprs env (expr :: rest) = none := by
  simp [evalExprs, hRest]

theorem evalExprs_cons_head_failure_after_rest {env : Env} {expr : Expr}
    {rest : List Expr} {values : List Value}
    (hRest : evalExprs env rest = some values)
    (hExpr : evalExpr env expr = none) :
    evalExprs env (expr :: rest) = none := by
  simp [evalExprs, hRest, hExpr]

theorem evalProgramStmt_expr_failure {fuel : Nat} {funcs : FunctionEnv}
    {env : Env} {expr : Expr}
    (hExpr : evalExpr env expr = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.expr expr) = none := by
  simp [evalProgramStmtFuel, hExpr]

theorem evalProgramStmt_let1_init_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {name : Name} {expr : Expr}
    (hExpr : evalExpr env expr = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.let1 name (some expr)) =
      none := by
  simp [evalProgramStmtFuel, hExpr]

theorem evalProgramStmt_letMany_init_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {names : List Name}
    {exprs : List Expr}
    (hExprs : evalExprs env exprs = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.letMany names (some exprs)) =
      none := by
  simp [evalProgramStmtFuel, hExprs]

theorem evalProgramStmt_assign_rhs_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {name : Name} {expr : Expr}
    (hExpr : evalExpr env expr = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.assign name expr) = none := by
  simp [evalProgramStmtFuel, hExpr]

theorem evalProgramStmt_assignMany_rhs_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {names : List Name}
    {exprs : List Expr}
    (hExprs : evalExprs env exprs = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.assignMany names exprs) =
      none := by
  simp [evalProgramStmtFuel, hExprs]

theorem evalProgramStmt_letCall_args_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {names : List Name}
    {fnName : Name} {args : List Expr}
    (hArgs : evalExprs env args = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.letCall names fnName args) =
      none := by
  simp [evalProgramStmtFuel, hArgs]

theorem evalProgramStmt_assignCall_args_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {names : List Name}
    {fnName : Name} {args : List Expr}
    (hArgs : evalExprs env args = none) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.assignCall names fnName args) =
      none := by
  simp [evalProgramStmtFuel, hArgs]

theorem evalProgramStmt_switch_discriminant_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {discr : Expr}
    {cases : List (Value × Stmt)} {defaultBranch : Option Stmt}
    (hDiscr : evalExpr env discr = none) :
    evalProgramStmtFuel fuel.succ funcs env
      (Stmt.switch discr cases defaultBranch) = none := by
  simp [evalProgramStmtFuel, hDiscr]

theorem evalProgramStmt_for_pre_failure {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {pre post body : Stmt} {cond : Expr}
    (hPre : evalProgramStmtFuel fuel funcs env pre = none) :
    evalProgramStmtFuel fuel.succ funcs env
      (Stmt.forLoop pre cond post body) = none := by
  simp [evalProgramStmtFuel, hPre]

theorem evalProgramStmt_seq_short_circuits_non_normal {fuel : Nat}
    {funcs : FunctionEnv} {env : Env} {first second : Stmt}
    {result : FlowResult}
    (hFirst : evalProgramStmtFuel fuel
      (collectStmtFunctionDefs (Stmt.seq first second) funcs)
      env first = some result)
    (hFlow : result.flow ≠ Flow.normal) :
    evalProgramStmtFuel fuel.succ funcs env (Stmt.seq first second) =
      some result := by
  cases result with
  | mk flow resultEnv =>
      cases flow <;> simp [evalProgramStmtFuel, hFirst] at hFlow ⊢

theorem evalLetDefault_declares_fresh (name : Name) (env : Env)
    (h : lookup? env name = none) :
    evalStmt env (Stmt.let1 name none) =
      some ((name, Value.word 0) :: env) := by
  simp [evalStmt, declare?, h]

theorem evalExprs_two_vars (left right : Value) :
    evalExprs [(0, left), (1, right)] [Expr.var 1, Expr.var 0] =
      some [right, left] := by
  simp [evalExprs, evalExpr, lookup?]

theorem declareMany_arity_mismatch (env : Env) (name : Name) :
    declareMany? env [name] [] = none := by
  rfl

theorem declareMany_two_fresh (name0 name1 : Name) (value0 value1 : Value)
    (env : Env) (h0 : lookup? env name0 = none)
    (h1 : lookup? env name1 = none) (hDistinct : name0 ≠ name1) :
    declareMany? env [name0, name1] [value0, value1] =
      some ([(name1, value1), (name0, value0)] ++ env) := by
  simp [declareMany?, declare?, lookup?, h0, h1, hDistinct]

theorem assignMany_arity_mismatch (env : Env) (name : Name) :
    assignMany? env [name] [] = none := by
  rfl

theorem evalLetManyDefault_declares_pair :
    evalStmt [] (Stmt.letMany [0, 1] none) =
      some [(1, Value.word 0), (0, Value.word 0)] := by
  simp [evalStmt, declareMany?, declare?, lookup?]

theorem evalAssignMany_evaluates_rhs_before_assignment
    (left right : Value) :
    evalStmt [(0, left), (1, right)]
        (Stmt.assignMany [0, 1] [Expr.var 1, Expr.var 0]) =
      some [(0, right), (1, left)] := by
  simp [evalStmt, evalExprs, evalExpr, assignMany?, assign?, lookup?]

theorem evalControlIf_false_skips (fuel : Nat) (env : Env) (body : Stmt) :
    evalControlStmtFuel fuel.succ env
        (Stmt.ifThen (Expr.value (Value.word 0)) body) =
      some { flow := Flow.normal, env := env } := by
  simp [evalControlStmtFuel, evalExpr, valueAsBool, normalResult, norm,
    wordModulus]

theorem evalControlSwitch_first_match (fuel : Nat) :
    evalControlStmtFuel fuel.succ.succ []
        (Stmt.switch (Expr.value (Value.word 7))
          [(Value.word 7, Stmt.leave)] none) =
      some { flow := Flow.left, env := [] } := by
  simp [evalControlStmtFuel, evalExpr, switchTarget?]

theorem evalControlBlock_break_drops_local :
    evalControlStmtFuel 5 [(0, Value.word 9)]
        (Stmt.block [Stmt.let1 1 none, Stmt.break]) =
      some { flow := Flow.broke, env := [(0, Value.word 9)] } := by
  simp [evalControlStmtFuel, evalControlBlockFuel, declare?, lookup?,
    restoreOuter, normalResult, withRestoredEnv]

theorem evalControlFor_continue_runs_post :
    evalControlStmtFuel 8 [(0, Value.word 1)]
        (Stmt.forLoop Stmt.skip (Expr.var 0)
          (Stmt.assign 0 (Expr.value (Value.word 0))) Stmt.continue) =
      some { flow := Flow.normal, env := [(0, Value.word 0)] } := by
  simp [evalControlStmtFuel, evalControlForFuel, evalExpr, valueAsBool,
    assign?, lookup?, restoreOuter, normalResult, withRestoredFlow, norm,
    wordModulus]

theorem evalControlFor_break_exits :
    evalControlStmtFuel 8 [(0, Value.word 1)]
        (Stmt.forLoop Stmt.skip (Expr.var 0)
          (Stmt.assign 0 (Expr.value (Value.word 0))) Stmt.break) =
      some { flow := Flow.normal, env := [(0, Value.word 1)] } := by
  simp [evalControlStmtFuel, evalControlForFuel, evalExpr, valueAsBool,
    lookup?, restoreOuter, normalResult, withRestoredFlow, norm, wordModulus]

def pairReturnFunction : FunctionDef :=
  { params := [0, 1]
    returns := [2, 3]
    body :=
      Stmt.block
        [ Stmt.assign 2 (Expr.var 0)
        , Stmt.assign 3 (Expr.var 1) ] }

theorem valuesForNames_pair (left right : Value) :
    valuesForNames? [(2, left), (3, right)] [2, 3] =
      some [left, right] := by
  simp [valuesForNames?, lookup?]

theorem evalFunction_pair_returns :
    evalFunctionFuel 8 [(10, pairReturnFunction)] 10
        [Value.word 4, Value.word 9] =
      some [Value.word 4, Value.word 9] := by
  simp [evalFunctionFuel, lookupFunction?, pairReturnFunction, initFunctionEnv,
    declareMany?, declare?, lookup?, evalProgramStmtFuel, evalProgramBlockFuel,
    evalExpr, assign?, restoreOuter, valuesForNames?, normalResult,
    withRestoredEnv]

theorem evalFunction_pair_wrong_arity :
    evalFunctionFuel 8 [(10, pairReturnFunction)] 10 [Value.word 4] = none := by
  simp [evalFunctionFuel, lookupFunction?, pairReturnFunction, initFunctionEnv,
    declareMany?, declare?, lookup?]

theorem evalProgramAssignCall_pair :
    evalProgramStmtFuel 10 [(10, pairReturnFunction)]
        [(4, Value.word 0), (5, Value.word 0)]
        (Stmt.assignCall [4, 5] 10
          [Expr.value (Value.word 7), Expr.value (Value.word 8)]) =
      some { flow := Flow.normal, env := [(4, Value.word 7), (5, Value.word 8)] } := by
  simp [evalProgramStmtFuel, evalFunctionFuel, lookupFunction?,
    pairReturnFunction, initFunctionEnv, declareMany?, declare?, lookup?,
    evalExprs, evalExpr, evalProgramBlockFuel, assign?, assignMany?,
    restoreOuter, valuesForNames?, normalResult, withRestoredEnv]

def forwardReturnFunctionBody : Stmt :=
  Stmt.assign 0 (Expr.value (Value.word 7))

theorem evalProgramForwardFunctionCall_seq :
    evalProgramStmtFuel 10 [] [(1, Value.word 0)]
        (Stmt.seq
          (Stmt.assignCall [1] 20 [])
          (Stmt.funDef 20 [] [0] forwardReturnFunctionBody)) =
      some { flow := Flow.normal, env := [(1, Value.word 7)] } := by
  rfl

def sampleObject : YulObject :=
  YulObject.mk 0 Stmt.skip [(1, SymbolicBytes.literal "runtime")] []

theorem evalObjectDataSize_literal :
    evalObjectExpr sampleObject [] (Expr.dataSize 1) =
      some (Value.word 32) := by
  simp [evalObjectExpr, sampleObject, YulObject.data?, lookupData?,
    symbolicDataSize]

theorem evalObjectDataOffset_symbolic :
    evalObjectExpr sampleObject [] (Expr.dataOffset 1) =
      some (Value.dataOffset 1) := by
  simp [evalObjectExpr, sampleObject, YulObject.data?, lookupData?]

theorem copyObjectData_symbolic :
    copyObjectData? sampleObject ObjectMemory.empty 64 1 =
      some { writes := [(64, SymbolicBytes.literal "runtime")] } := by
  simp [copyObjectData?, sampleObject, YulObject.data?, lookupData?,
    ObjectMemory.empty, ObjectMemory.write]

theorem evalEvmBuiltin_add_words :
    evalEvmBuiltin Evm.Builtin.add [Value.word 2, Value.word 3]
        EvmState.empty =
      some (Value.word (addWord 2 3), EvmState.empty) := by
  rfl

theorem evalEvmBuiltin_add_symbolic_term :
    evalEvmBuiltin Evm.Builtin.add
        [Value.calldataWord 0, Value.word 1] EvmState.empty =
      some
        (Value.binaryBuiltin Evm.Builtin.add
          (Value.calldataWord 0) (Value.word 1),
          EvmState.empty) := by
  rfl

theorem evalEvmBuiltin_eq_symbolic_term :
    evalEvmBuiltin Evm.Builtin.eqOp
        [Value.calldataWord 0, Value.word 0] EvmState.empty =
      some
        (Value.binaryBuiltin Evm.Builtin.eqOp
          (Value.calldataWord 0) (Value.word 0),
          EvmState.empty) := by
  rfl

theorem evalEvmBuiltin_eq_identical_symbolic :
    evalEvmBuiltin Evm.Builtin.eqOp
        [Value.calldataWord 0, Value.calldataWord 0] EvmState.empty =
      some (Value.word 1, EvmState.empty) := by
  rfl

theorem evalEvmBuiltin_signed_div_mod_words :
    evalEvmBuiltin Evm.Builtin.sdivOp [Value.word 7, Value.word 2]
        EvmState.empty =
      some (Value.word (sdivWord 7 2), EvmState.empty) ∧
    evalEvmBuiltin Evm.Builtin.smodOp [Value.word 7, Value.word 2]
        EvmState.empty =
      some (Value.word (smodWord 7 2), EvmState.empty) := by
  constructor <;> rfl

theorem evalEvmBuiltin_signextend_clz_words :
    evalEvmBuiltin Evm.Builtin.signextendOp [Value.word 0, Value.word 128]
        EvmState.empty =
      some (Value.word (signextendWord 0 128), EvmState.empty) ∧
    evalEvmBuiltin Evm.Builtin.clzOp [Value.word 0] EvmState.empty =
      some (Value.word (clzWord 0), EvmState.empty) := by
  constructor <;> rfl

theorem evalEvmBuiltin_keccak_symbolic :
    evalEvmBuiltin Evm.Builtin.keccak256Op [Value.word 0, Value.word 64]
        EvmState.empty =
      some (Value.symbolicHash (SymbolicBytes.memorySnapshot 0 0 64),
        { EvmState.empty with msize := 64 }) := by
  rfl

theorem evalEvmBuiltin_keccak_uses_memory_version :
    evalEvmBuiltin Evm.Builtin.keccak256Op [Value.word 1, Value.word 2]
        { EvmState.empty with memoryVersion := 5 } =
      some (Value.symbolicHash (SymbolicBytes.memorySnapshot 5 1 2),
        { EvmState.empty with memoryVersion := 5, msize := 32 }) := by
  rfl

theorem evalEvmBuiltin_sload_symbolic_roundtrip :
    evalEvmBuiltin Evm.Builtin.sload [Value.word 5]
        { EvmState.empty with
          storage := [(0, [(Value.word 5, Value.dataOffset 1)])] } =
      some (Value.dataOffset 1,
        { EvmState.empty with
          storage := [(0, [(Value.word 5, Value.dataOffset 1)])] }) := by
  rfl

theorem evalEvmBuiltin_sload_unknown_symbolic_key :
    evalEvmBuiltin Evm.Builtin.sload
        [Value.symbolicHash (SymbolicBytes.literal "slot")] EvmState.empty =
      some
        ( Value.storageWord 0 (Value.symbolicHash (SymbolicBytes.literal "slot"))
        , EvmState.empty ) := by
  rfl

theorem evalEvmBuiltin_sload_symbolic_key_roundtrip :
    evalEvmBuiltin Evm.Builtin.sload
        [Value.symbolicHash (SymbolicBytes.literal "slot")]
        { EvmState.empty with
          storage :=
            [ (0,
                [ (Value.symbolicHash (SymbolicBytes.literal "slot"),
                    Value.word 7) ]) ] } =
      some
        ( Value.word 7
        , { EvmState.empty with
            storage :=
              [ (0,
                  [ (Value.symbolicHash (SymbolicBytes.literal "slot"),
                      Value.word 7) ]) ] } ) := by
  rfl

theorem evalEvmBuiltin_tload_symbolic_roundtrip :
    evalEvmBuiltin Evm.Builtin.tloadOp [Value.word 5]
        { EvmState.empty with
          transientStorage := [(0, [(Value.word 5, Value.dataOffset 1)])] } =
      some
        ( Value.dataOffset 1
        , { EvmState.empty with
            transientStorage := [(0, [(Value.word 5, Value.dataOffset 1)])] } ) := by
  rfl

theorem evalEvmBuiltin_mload_unknown_uses_memory_version :
    evalEvmBuiltin Evm.Builtin.mload [Value.word 0]
        { EvmState.empty with memoryVersion := 4 } =
      some
        ( Value.memoryWordAt 4 0
        , { EvmState.empty with memoryVersion := 4, msize := 32 } ) := by
  rfl

theorem evalEvmBuiltin_mload_known_preserves_memory_version :
    evalEvmBuiltin Evm.Builtin.mload [Value.word 0]
        { EvmState.empty with
          memoryVersion := 4
          memoryWords := [(0, Value.word 7)] } =
      some
        ( Value.word 7
        , { EvmState.empty with
            memoryVersion := 4
            memoryWords := [(0, Value.word 7)]
            msize := 32 } ) := by
  rfl

theorem evalEvmBuiltin_mstore_bumps_memory_version :
    evalEvmBuiltin Evm.Builtin.mstore
        [Value.word 0, Value.dataOffset 1]
        { EvmState.empty with memoryVersion := 2 } =
      some (Value.word 0,
        { EvmState.empty with
          memoryVersion := 3
          msize := 32
          memoryWords := [(0, Value.dataOffset 1)] }) := by
  rfl

theorem evalEvmBuiltin_mstore8_invalidates_exact_words :
    evalEvmBuiltin Evm.Builtin.mstore8 [Value.word 31, Value.word 263]
        { EvmState.empty with memoryWords := [(0, Value.word 1)] } =
      some
        ( Value.word 0
        , { EvmState.empty with memoryVersion := 1, msize := 32 } ) := by
  rfl

theorem evalEvmBuiltin_returndataload_uses_version :
    evalEvmBuiltin Evm.Builtin.returndataloadOp [Value.word 0]
        { EvmState.empty with returndataVersion := 4 } =
      some (Value.returndataWordAt 4 0,
        { EvmState.empty with returndataVersion := 4 }) := by
  rfl

theorem evalEvmBuiltin_calldatacopy_symbolic :
    evalEvmBuiltin Evm.Builtin.calldatacopyOp
        [Value.word 32, Value.word 0, Value.word 4] EvmState.empty =
      some (Value.word 0,
        { EvmState.empty with
          memoryVersion := 1
          msize := 64
          memoryBytes := ObjectMemory.write ObjectMemory.empty 32
            (SymbolicBytes.calldataSlice 0 4) }) := by
  rfl

theorem evalEvmBuiltin_zero_length_calldatacopy_symbolic_noop :
    evalEvmBuiltin Evm.Builtin.calldatacopyOp
        [Value.word 100, Value.word 0, Value.word 0]
        { EvmState.empty with memoryWords := [(0, Value.word 7)] } =
      some
        ( Value.word 0
        , { EvmState.empty with memoryWords := [(0, Value.word 7)] } ) := by
  rfl

theorem evalEvmBuiltin_datacopy_object_symbolic :
    evalEvmBuiltin Evm.Builtin.datacopyOp
        [Value.word 64, Value.dataOffset 1, Value.word 8] EvmState.empty =
      some
        ( Value.word 0
        , { EvmState.empty with
            memoryVersion := 1
            msize := 96
            memoryBytes := ObjectMemory.write ObjectMemory.empty 64
              (SymbolicBytes.objectData 1 8) } ) := by
  rfl

theorem evalEvmBuiltin_external_call_records_action_and_memory :
    evalEvmBuiltin Evm.Builtin.callOp
        [Value.word 0, Value.word 1, Value.word 2, Value.word 3,
          Value.word 4, Value.word 5, Value.word 6] EvmState.empty =
      some (Value.callSuccess 1,
        { EvmState.empty with
          memoryBytes :=
            ObjectMemory.write ObjectMemory.empty 5
              (SymbolicBytes.returndataSnapshot 1 0 6)
          memoryVersion := 1
          returndata := SymbolicBytes.callReturnData 1
          returndataVersion := 1
          msize := 32
          externalActions := [Evm.Builtin.callOp]
          externalEvents :=
            [ { id := 1
                op := Evm.Builtin.callOp
                args :=
                  [Value.word 0, Value.word 1, Value.word 2, Value.word 3,
                    Value.word 4, Value.word 5, Value.word 6]
                result := Value.callSuccess 1
                returndata := SymbolicBytes.callReturnData 1 } ]
          nextExternalId := 2 }) := by
  rfl

theorem evalEvmBuiltin_stop_halts :
    evalEvmBuiltin Evm.Builtin.stopOp [] EvmState.empty =
      some
        ( Value.word 0
        , { EvmState.empty with
            halt? := some
              { kind := Evm.HaltKind.stop
                returndata := SymbolicBytes.empty } } ) := by
  rfl

theorem evalEvmBuiltin_return_halts_with_snapshot :
    evalEvmBuiltin Evm.Builtin.returnOp [Value.word 1, Value.word 2]
        { EvmState.empty with memoryVersion := 3 } =
      some
        ( Value.word 0
        , { EvmState.empty with
            memoryVersion := 3
            msize := 32
            halt? := some
              { kind := Evm.HaltKind.returned
                returndata := SymbolicBytes.memorySnapshot 3 1 2 } } ) := by
  rfl

theorem evalEvmBuiltin_immutable_linker_memoryguard_verbatim :
    evalEvmBuiltin Evm.Builtin.loadimmutableOp [Value.word 1]
        { EvmState.empty with immutables := [(Value.word 1, Value.word 9)] } =
      some
        ( Value.word 9
        , { EvmState.empty with immutables := [(Value.word 1, Value.word 9)] } ) ∧
    evalEvmBuiltin Evm.Builtin.linkersymbolOp [Value.word 1]
        { EvmState.empty with linkerSymbols := [(Value.word 1, Value.word 10)] } =
      some
        ( Value.word 10
        , { EvmState.empty with linkerSymbols := [(Value.word 1, Value.word 10)] } ) ∧
    evalEvmBuiltin Evm.Builtin.memoryguardOp [Value.word 64] EvmState.empty =
      some (Value.word 64, EvmState.empty) ∧
    evalEvmBuiltin (Evm.Builtin.verbatimOp 2 1)
        [Value.word 4, Value.word 5] EvmState.empty =
      some
        ( Value.callSuccess 1
        , { EvmState.empty with
            externalActions := [Evm.Builtin.verbatimOp 2 1]
            externalEvents :=
              [ { id := 1
                  op := Evm.Builtin.verbatimOp 2 1
                  args := [Value.word 4, Value.word 5]
                  result := Value.callSuccess 1
                  returndata := SymbolicBytes.empty } ]
            nextExternalId := 2 } ) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

theorem evalEvmBuiltinValues_verbatim_multi_output :
    evalEvmBuiltinValues (Evm.Builtin.verbatimOp 1 2)
        [Value.word 7] EvmState.empty =
      some
        ( [Value.callSuccess 1, Value.callSuccess 2]
        , { EvmState.empty with
            externalActions := [Evm.Builtin.verbatimOp 1 2]
            externalEvents :=
              [ { id := 1
                  op := Evm.Builtin.verbatimOp 1 2
                  args := [Value.word 7]
                  result := Value.callSuccess 1
                  returndata := SymbolicBytes.empty },
                { id := 2
                  op := Evm.Builtin.verbatimOp 1 2
                  args := [Value.word 7]
                  result := Value.callSuccess 2
                  returndata := SymbolicBytes.empty } ]
            nextExternalId := 3 } ) := by
  rfl

theorem checkBreakOutsideLoop_rejected :
    checkStmtFuel 5 StaticContext.empty false false Stmt.break = none := by
  rfl

theorem checkBlockLocalDoesNotEscape :
    checkStmtFuel 8 StaticContext.empty false false
      (Stmt.seq (Stmt.block [Stmt.let1 0 none])
        (Stmt.assign 0 (Expr.value (Value.word 1)))) = none := by
  rfl

theorem checkLoopBreak_allowed :
    checkStmtFuel 8 StaticContext.empty false false
      (Stmt.forLoop Stmt.skip (Expr.value (Value.word 0)) Stmt.skip Stmt.break) =
    some StaticContext.empty := by
  rfl

theorem checkLoopBreakInPost_rejected :
    checkStmtFuel 8 StaticContext.empty false false
      (Stmt.forLoop Stmt.skip (Expr.value (Value.word 0)) Stmt.break Stmt.skip) =
    none := by
  rfl

theorem checkNestedLoopBreakInPost_allowed :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.forLoop Stmt.skip (Expr.value (Value.word 0))
        (Stmt.forLoop Stmt.skip (Expr.value (Value.word 0)) Stmt.skip Stmt.break)
        Stmt.skip) =
    some StaticContext.empty := by
  rfl

theorem checkFunctionInForInit_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.forLoop (Stmt.funDef 20 [] [] Stmt.skip)
        (Expr.value (Value.word 0)) Stmt.skip Stmt.skip) =
    none := by
  rfl

theorem checkEmptySwitch_rejected :
    checkStmtFuel 6 StaticContext.empty false false
      (Stmt.switch (Expr.value (Value.word 0)) [] none) = none := by
  rfl

theorem checkDefaultOnlySwitch_allowed :
    checkStmtFuel 6 StaticContext.empty false false
      (Stmt.switch (Expr.value (Value.word 0)) [] (some Stmt.skip)) =
    some StaticContext.empty := by
  rfl

theorem checkDuplicateSwitchLabels_rejected :
    checkStmtFuel 8 StaticContext.empty false false
      (Stmt.switch (Expr.value (Value.word 0))
        [(Value.word 1, Stmt.skip), (Value.word 1, Stmt.skip)] none) =
    none := by
  rfl

theorem checkDuplicateLetMany_rejected :
    checkStmtFuel 8 StaticContext.empty false false
      (Stmt.letMany [0, 0] none) = none := by
  rfl

theorem checkNestedFunctionSelfCall_allowed :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.funDef 20 [0] [1] (Stmt.assignCall [1] 20 [Expr.var 0])) =
    some { vars := [], funcs := [(20, { paramCount := 1, returnCount := 1 })] } := by
  rfl

theorem checkForwardFunctionCall_allowed :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.letCall [1] 20 []
        , Stmt.funDef 20 [] [0] forwardReturnFunctionBody ]) =
    some StaticContext.empty := by
  rfl

theorem checkVariableShadowsFunction_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.funDef 20 [] [] Stmt.skip
        , Stmt.let1 20 none ]) =
    none := by
  rfl

theorem checkFunctionShadowsVariable_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.let1 20 none
        , Stmt.funDef 20 [] [] Stmt.skip ]) =
    none := by
  rfl

theorem checkFunctionParamShadowsFunction_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.funDef 20 [] [] Stmt.skip
        , Stmt.funDef 21 [20] [] Stmt.skip ]) =
    none := by
  rfl

theorem checkFunctionParamShadowsVariable_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.let1 20 none
        , Stmt.funDef 21 [20] [] Stmt.skip ]) =
    none := by
  rfl

theorem checkFunctionReturnShadowsVariable_rejected :
    checkStmtFuel 12 StaticContext.empty false false
      (Stmt.block
        [ Stmt.let1 20 none
        , Stmt.funDef 21 [] [20] Stmt.skip ]) =
    none := by
  rfl

theorem checkStmtFuel_break_iff (fuel : Nat) (ctx : StaticContext)
    (inLoop inFunction : Bool) :
    checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.break =
      if inLoop then some ctx else none := by
  cases inLoop <;> rfl

theorem checkStmtFuel_continue_iff (fuel : Nat) (ctx : StaticContext)
    (inLoop inFunction : Bool) :
    checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.continue =
      if inLoop then some ctx else none := by
  cases inLoop <;> rfl

theorem checkStmtFuel_leave_iff (fuel : Nat) (ctx : StaticContext)
    (inLoop inFunction : Bool) :
    checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.leave =
      if inFunction then some ctx else none := by
  cases inFunction <;> rfl

theorem checkBreak_accepted_implies_inLoop {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.break = some ctx') :
    inLoop = true ∧ ctx' = ctx := by
  cases inLoop <;> simp [checkStmtFuel] at h
  exact ⟨rfl, h.symm⟩

theorem checkContinue_accepted_implies_inLoop {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.continue =
      some ctx') :
    inLoop = true ∧ ctx' = ctx := by
  cases inLoop <;> simp [checkStmtFuel] at h
  exact ⟨rfl, h.symm⟩

theorem checkLeave_accepted_implies_inFunction {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.leave = some ctx') :
    inFunction = true ∧ ctx' = ctx := by
  cases inFunction <;> simp [checkStmtFuel] at h
  exact ⟨rfl, h.symm⟩

theorem checkExpr_var_iff_contains (ctx : StaticContext) (name : Name) :
    checkExpr ctx (Expr.var name) = containsName ctx.vars name := by
  rfl

theorem checkStmtFuel_skip_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction Stmt.skip =
      some ctx') :
    ctx' = ctx := by
  simp [checkStmtFuel] at h
  exact h.symm

theorem checkStmtFuel_expr_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {expr : Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction (Stmt.expr expr) =
      some ctx') :
    checkStmtExpr ctx expr = true ∧ ctx' = ctx := by
  cases hExpr : checkStmtExpr ctx expr
  · simp [checkStmtFuel, hExpr] at h
  · simp [checkStmtFuel, hExpr] at h
    exact ⟨rfl, h.symm⟩

theorem checkStmtFuel_let1_init_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.let1 name (some expr)) = some ctx') :
    checkExpr ctx expr = true ∧
      ∃ declCtx,
        addVarName? ctx name = some declCtx ∧ ctx' = declCtx := by
  simp [checkStmtFuel] at h
  rcases h with ⟨hExpr, hAddCtx⟩
  cases hAdd : addVarName? ctx name with
  | none =>
      rw [hAdd] at hAddCtx
      cases hAddCtx
  | some declCtx =>
      rw [hAdd] at hAddCtx
      simp at hAddCtx
      exact ⟨hExpr, declCtx, rfl, hAddCtx.symm⟩

theorem checkStmtFuel_let1_default_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.let1 name none) = some ctx') :
    ∃ declCtx,
      addVarName? ctx name = some declCtx ∧ ctx' = declCtx := by
  cases hAdd : addVarName? ctx name with
  | none =>
      simp [checkStmtFuel, hAdd] at h
  | some declCtx =>
      simp [checkStmtFuel, hAdd] at h
      exact ⟨declCtx, rfl, h.symm⟩

theorem checkStmtFuel_letMany_init_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.letMany names (some exprs)) = some ctx') :
    checkExprsAsYulValues ctx exprs names.length = true ∧
      ∃ declCtx,
        addVarNames? ctx names = some declCtx ∧ ctx' = declCtx := by
  simp [checkStmtFuel] at h
  rcases h with ⟨hExprs, hAddCtx⟩
  cases hAdd : addVarNames? ctx names with
  | none =>
      rw [hAdd] at hAddCtx
      cases hAddCtx
  | some declCtx =>
      rw [hAdd] at hAddCtx
      simp at hAddCtx
      exact ⟨hExprs, declCtx, rfl, hAddCtx.symm⟩

theorem checkStmtFuel_letMany_default_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.letMany names none) = some ctx') :
    ∃ declCtx,
      addVarNames? ctx names = some declCtx ∧ ctx' = declCtx := by
  cases hAdd : addVarNames? ctx names with
  | none =>
      simp [checkStmtFuel, hAdd] at h
  | some declCtx =>
      simp [checkStmtFuel, hAdd] at h
      exact ⟨declCtx, rfl, h.symm⟩

theorem checkStmtFuel_assign_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.assign name expr) = some ctx') :
    containsName ctx.vars name = true ∧
      checkExpr ctx expr = true ∧ ctx' = ctx := by
  simp [checkStmtFuel] at h
  exact ⟨h.1.1, h.1.2, h.2.symm⟩

theorem checkStmtFuel_assignMany_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.assignMany names exprs) = some ctx') :
    namesUnique names = true ∧
      namesInScope ctx.vars names = true ∧
      checkExprsAsYulValues ctx exprs names.length = true ∧
      ctx' = ctx := by
  simp [checkStmtFuel] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2.symm⟩

theorem checkStmtFuel_funDef_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {params returns : List Name} {body : Stmt}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.funDef name params returns body) = some ctx') :
    ∃ fnCtx fnVars bodyCtx,
      ((lookupFunctionSig? ctx.funcs name =
          some ({ paramCount := params.length, returnCount := returns.length } : FunctionSig) ∧
          fnCtx = ctx) ∨
        addFunctionSigNoShadow? ctx name
          ({ paramCount := params.length, returnCount := returns.length } : FunctionSig) =
          some fnCtx) ∧
      initFunctionStaticVars? fnCtx params returns = some fnVars ∧
      checkStmtFuel fuel { vars := fnVars, funcs := fnCtx.funcs } false true body =
        some bodyCtx ∧
      ctx' = fnCtx := by
  let sig : FunctionSig :=
    { paramCount := params.length, returnCount := returns.length }
  cases hLookup : lookupFunctionSig? ctx.funcs name with
  | none =>
      cases hAdd : addFunctionSigNoShadow? ctx name sig with
      | none =>
          simp [checkStmtFuel, sig, hLookup, hAdd] at h
      | some fnCtx =>
          cases hVars : initFunctionStaticVars? fnCtx params returns with
          | none =>
              simp [checkStmtFuel, sig, hLookup, hAdd, hVars] at h
          | some fnVars =>
              cases hBody :
                  checkStmtFuel fuel { vars := fnVars, funcs := fnCtx.funcs }
                    false true body with
              | none =>
                  simp [checkStmtFuel, sig, hLookup, hAdd, hVars, hBody] at h
              | some bodyCtx =>
                  simp [checkStmtFuel, sig, hLookup, hAdd, hVars, hBody] at h
                  exact
                    ⟨ fnCtx, fnVars, bodyCtx, Or.inr rfl, hVars, hBody,
                      h.symm ⟩
  | some existing =>
      by_cases hEq : existing = sig
      · subst existing
        cases hVars : initFunctionStaticVars? ctx params returns with
        | none =>
            simp [checkStmtFuel, sig, hLookup, hVars] at h
        | some fnVars =>
            cases hBody :
                checkStmtFuel fuel { vars := fnVars, funcs := ctx.funcs }
                  false true body with
            | none =>
                simp [checkStmtFuel, sig, hLookup, hVars, hBody] at h
            | some bodyCtx =>
                simp [checkStmtFuel, sig, hLookup, hVars, hBody] at h
                exact
                  ⟨ ctx, fnVars, bodyCtx,
                    Or.inl ⟨rfl, rfl⟩,
                    hVars, hBody, h.symm ⟩
      · exfalso
        simp [checkStmtFuel, sig, hLookup, hEq] at h

theorem checkStmtFuel_letCall_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.letCall names fnName args) = some ctx') :
    ∃ sig declCtx,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      addVarNames? ctx names = some declCtx ∧
      ctx' = declCtx := by
  cases hSig : lookupFunctionSig? ctx.funcs fnName with
  | none =>
      simp [checkStmtFuel, hSig] at h
  | some sig =>
      cases hAdd : addVarNames? ctx names with
      | none =>
          simp [checkStmtFuel, hSig] at h
          rcases h with ⟨_, hMatch⟩
          rw [hAdd] at hMatch
          cases hMatch
      | some declCtx =>
          simp [checkStmtFuel, hSig] at h
          rcases h with ⟨hChecks, hMatch⟩
          rw [hAdd] at hMatch
          simp at hMatch
          exact
            ⟨sig, declCtx, rfl, hChecks.1.1, hChecks.1.2, hChecks.2,
              rfl, hMatch.symm⟩

theorem checkStmtFuel_assignCall_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.assignCall names fnName args) = some ctx') :
    ∃ sig,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      namesUnique names = true ∧
      namesInScope ctx.vars names = true ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      ctx' = ctx := by
  cases hSig : lookupFunctionSig? ctx.funcs fnName with
  | none =>
      simp [checkStmtFuel, hSig] at h
  | some sig =>
      simp [checkStmtFuel, hSig] at h
      exact
        ⟨sig, rfl, h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2,
          h.1.1.2, h.1.2, h.2.symm⟩

theorem checkStmtFuel_seq_accepted_implies {fuel : Nat}
    {ctx ctx'' : StaticContext} {inLoop inFunction : Bool}
    {first second : Stmt}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.seq first second) = some ctx'') :
    ∃ seqCtx ctx',
      predeclareStmtFunctionSigs? ctx (Stmt.seq first second) = some seqCtx ∧
      checkStmtFuel fuel seqCtx inLoop inFunction first = some ctx' ∧
      checkStmtFuel fuel ctx' inLoop inFunction second = some ctx'' := by
  cases hPre : predeclareStmtFunctionSigs? ctx (Stmt.seq first second) with
  | none =>
      simp [checkStmtFuel, hPre] at h
  | some seqCtx =>
      cases hFirst : checkStmtFuel fuel seqCtx inLoop inFunction first with
      | none =>
          simp [checkStmtFuel, hPre, hFirst] at h
      | some ctx' =>
          exact
            ⟨seqCtx, ctx', rfl, hFirst,
              by simpa [checkStmtFuel, hPre, hFirst] using h⟩

theorem checkBlockFuel_cons_accepted_implies {fuel : Nat}
    {ctx ctx'' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt} {rest : List Stmt}
    (h : checkBlockFuel fuel.succ ctx inLoop inFunction (stmt :: rest) =
      some ctx'') :
    ∃ ctx',
      checkStmtFuel fuel ctx inLoop inFunction stmt = some ctx' ∧
      checkBlockFuel fuel ctx' inLoop inFunction rest = some ctx'' := by
  cases hStmt : checkStmtFuel fuel ctx inLoop inFunction stmt with
  | none =>
      simp [checkBlockFuel, hStmt] at h
  | some ctx' =>
      exact ⟨ctx', rfl, by simpa [checkBlockFuel, hStmt] using h⟩

theorem checkBlockFuel_empty_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (h : checkBlockFuel fuel.succ ctx inLoop inFunction [] = some ctx') :
    ctx' = ctx := by
  simp [checkBlockFuel] at h
  exact h.symm

theorem checkStmtFuel_block_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmts : List Stmt}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.block stmts) = some ctx') :
    ctx' = ctx ∧
      ∃ blockCtx innerCtx,
        predeclareBlockFunctionSigs? ctx stmts = some blockCtx ∧
        checkBlockFuel fuel blockCtx inLoop inFunction stmts = some innerCtx := by
  cases hPre : predeclareBlockFunctionSigs? ctx stmts with
  | none =>
      simp [checkStmtFuel, hPre] at h
  | some blockCtx =>
      cases hBlock : checkBlockFuel fuel blockCtx inLoop inFunction stmts with
      | none =>
          simp [checkStmtFuel, hPre, hBlock] at h
      | some innerCtx =>
          simp [checkStmtFuel, hPre, hBlock] at h
          exact ⟨h.symm, blockCtx, innerCtx, rfl, hBlock⟩

theorem checkStmtFuel_if_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {cond : Expr} {body : Stmt}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.ifThen cond body) = some ctx') :
    checkExpr ctx cond = true ∧ ctx' = ctx ∧
      ∃ bodyCtx,
        checkStmtFuel fuel ctx inLoop inFunction body = some bodyCtx := by
  simp [checkStmtFuel] at h
  rcases h with ⟨hCond, hBodyCtx⟩
  cases hBody : checkStmtFuel fuel ctx inLoop inFunction body with
  | none =>
      simp [hBody] at hBodyCtx
  | some bodyCtx =>
      simp [hBody] at hBodyCtx
      exact ⟨hCond, hBodyCtx.symm, bodyCtx, rfl⟩

theorem checkStmtFuel_switch_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {discr : Expr} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.switch discr cases defaultBranch) = some ctx') :
    checkExpr ctx discr = true ∧
      switchHasBranch cases defaultBranch = true ∧
      switchCaseLabelsUnique cases = true ∧
      ctx' = ctx ∧
      checkSwitchCasesFuel fuel ctx inLoop inFunction cases = some () ∧
      match defaultBranch with
      | some branch =>
          ∃ branchCtx,
            checkStmtFuel fuel ctx inLoop inFunction branch = some branchCtx
      | none => True := by
  cases hExpr : checkExpr ctx discr <;> simp [checkStmtFuel, hExpr] at h
  cases hHas : switchHasBranch cases defaultBranch <;> simp [hHas] at h
  cases hUnique : switchCaseLabelsUnique cases <;> simp [hUnique] at h
  cases hCases : checkSwitchCasesFuel fuel ctx inLoop inFunction cases with
  | none =>
      simp [hCases] at h
  | some casesOk =>
      cases casesOk
      cases defaultBranch with
      | none =>
          simp [hCases] at h
          exact ⟨rfl, rfl, rfl, h.symm, rfl, True.intro⟩
      | some branch =>
          cases hBranch : checkStmtFuel fuel ctx inLoop inFunction branch with
          | none =>
              simp [hCases, hBranch] at h
          | some branchCtx =>
              simp [hCases, hBranch] at h
              exact
                ⟨rfl, rfl, rfl, h.symm, rfl, branchCtx, hBranch⟩

theorem checkSwitchCasesFuel_empty_accepted
    (fuel : Nat) (ctx : StaticContext) (inLoop inFunction : Bool) :
    checkSwitchCasesFuel fuel.succ ctx inLoop inFunction [] = some () := by
  rfl

theorem checkSwitchCasesFuel_cons_accepted_implies {fuel : Nat}
    {ctx : StaticContext} {inLoop inFunction : Bool}
    {label : Value} {branch : Stmt} {rest : List (Value × Stmt)}
    (h : checkSwitchCasesFuel fuel.succ ctx inLoop inFunction
      ((label, branch) :: rest) = some ()) :
    ∃ branchCtx,
      checkStmtFuel fuel ctx inLoop inFunction branch = some branchCtx ∧
      checkSwitchCasesFuel fuel ctx inLoop inFunction rest = some () := by
  cases hBranch : checkStmtFuel fuel ctx inLoop inFunction branch with
  | none =>
      simp [checkSwitchCasesFuel, hBranch] at h
  | some branchCtx =>
      cases hRest :
          checkSwitchCasesFuel fuel ctx inLoop inFunction rest with
      | none =>
          simp [checkSwitchCasesFuel, hBranch, hRest] at h
      | some restOk =>
          cases restOk
          exact
            ⟨branchCtx, rfl,
              by simp [checkSwitchCasesFuel, hBranch, hRest] at h ⊢⟩

theorem checkStmtFuel_for_accepted_implies {fuel : Nat}
    {ctx ctx' : StaticContext} {inFunction : Bool}
    {pre post body : Stmt} {cond : Expr}
    (h : checkStmtFuel fuel.succ ctx false inFunction
      (Stmt.forLoop pre cond post body) = some ctx') :
    ctx' = ctx ∧ stmtHasNoFunDefs pre = true ∧
      ∃ loopCtx bodyCtx postCtx,
        checkStmtFuel fuel ctx false inFunction pre = some loopCtx ∧
        checkExpr loopCtx cond = true ∧
        checkStmtFuel fuel loopCtx true inFunction body = some bodyCtx ∧
        checkStmtFuel fuel loopCtx false inFunction post = some postCtx := by
  by_cases hNoFun : stmtHasNoFunDefs pre = true
  · cases hPre : checkStmtFuel fuel ctx false inFunction pre with
    | none =>
        simp [checkStmtFuel, hNoFun, hPre] at h
    | some loopCtx =>
        by_cases hCond : checkExpr loopCtx cond = true
        · cases hBody : checkStmtFuel fuel loopCtx true inFunction body with
          | none =>
              simp [checkStmtFuel, hNoFun, hPre, hCond, hBody] at h
          | some bodyCtx =>
              generalize hPost :
                checkStmtFuel fuel loopCtx false inFunction post = postResult at h
              cases postResult with
              | none =>
                  simp [checkStmtFuel, hNoFun, hPre, hCond, hBody, hPost] at h
              | some postCtx =>
                  simp [checkStmtFuel, hNoFun, hPre, hCond, hBody, hPost] at h
                  exact
                    ⟨ h.symm, hNoFun, loopCtx, bodyCtx, postCtx, rfl, hCond,
                      hBody, hPost ⟩
        · simp [checkStmtFuel, hNoFun, hPre, hCond] at h
  · simp [checkStmtFuel, hNoFun] at h

theorem checkStmtFuel_for_accepted_implies_any_loop {fuel : Nat}
    {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {pre post body : Stmt} {cond : Expr}
    (h : checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.forLoop pre cond post body) = some ctx') :
    ctx' = ctx ∧ stmtHasNoFunDefs pre = true ∧
      ∃ loopCtx bodyCtx postCtx,
        checkStmtFuel fuel ctx false inFunction pre = some loopCtx ∧
        checkExpr loopCtx cond = true ∧
        checkStmtFuel fuel loopCtx true inFunction body = some bodyCtx ∧
        checkStmtFuel fuel loopCtx false inFunction post = some postCtx := by
  by_cases hNoFun : stmtHasNoFunDefs pre = true
  · cases hPre : checkStmtFuel fuel ctx false inFunction pre with
    | none =>
        simp [checkStmtFuel, hNoFun, hPre] at h
    | some loopCtx =>
        by_cases hCond : checkExpr loopCtx cond = true
        · cases hBody : checkStmtFuel fuel loopCtx true inFunction body with
          | none =>
              simp [checkStmtFuel, hNoFun, hPre, hCond, hBody] at h
          | some bodyCtx =>
              generalize hPost :
                checkStmtFuel fuel loopCtx false inFunction post = postResult at h
              cases postResult with
              | none =>
                  simp [checkStmtFuel, hNoFun, hPre, hCond, hBody, hPost] at h
              | some postCtx =>
                  simp [checkStmtFuel, hNoFun, hPre, hCond, hBody, hPost] at h
                  exact
                    ⟨ h.symm, hNoFun, loopCtx, bodyCtx, postCtx, rfl, hCond,
                      hBody, hPost ⟩
        · simp [checkStmtFuel, hNoFun, hPre, hCond] at h
  · simp [checkStmtFuel, hNoFun] at h

theorem checkExpr_builtin_true_has_signature {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkExpr ctx (Expr.builtin builtin args) = true) :
    ∃ sig,
      builtin.signature? = some sig ∧
      sig.paramCount = args.length ∧
      sig.resultCount = 1 ∧
      checkExprs ctx args = true := by
  unfold checkExpr at h
  cases hs : builtin.signature? with
  | none =>
      simp [hs] at h
  | some sig =>
      have h' :
          (sig.paramCount = args.length ∧ sig.resultCount = 1) ∧
          checkExprs ctx args = true := by
        simpa [hs, Bool.and_eq_true] using h
      exact ⟨sig, rfl, h'.1.1, h'.1.2, h'.2⟩

theorem checkExpr_builtin_true_has_claim {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkExpr ctx (Expr.builtin builtin args) = true) :
    ∃ claim, builtin.claim? = some claim := by
  rcases checkExpr_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.claim?_of_signature? hSig

theorem checkExpr_builtin_true_has_semanticCoverage {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkExpr ctx (Expr.builtin builtin args) = true) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  rcases checkExpr_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.semanticCoverage?_of_signature? hSig

theorem checkStmtExpr_builtin_true_has_signature {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkStmtExpr ctx (Expr.builtin builtin args) = true) :
    ∃ sig,
      builtin.signature? = some sig ∧
      sig.paramCount = args.length ∧
      sig.resultCount = 0 ∧
      checkExprs ctx args = true := by
  unfold checkStmtExpr at h
  cases hs : builtin.signature? with
  | none =>
      simp [hs] at h
  | some sig =>
      have h' :
          (sig.paramCount = args.length ∧ sig.resultCount = 0) ∧
          checkExprs ctx args = true := by
        simpa [hs, Bool.and_eq_true] using h
      exact ⟨sig, rfl, h'.1.1, h'.1.2, h'.2⟩

theorem checkStmtExpr_builtin_true_has_claim {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkStmtExpr ctx (Expr.builtin builtin args) = true) :
    ∃ claim, builtin.claim? = some claim := by
  rcases checkStmtExpr_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.claim?_of_signature? hSig

theorem checkStmtExpr_builtin_true_has_semanticCoverage {ctx : StaticContext}
    {builtin : Evm.Builtin} {args : List Expr}
    (h : checkStmtExpr ctx (Expr.builtin builtin args) = true) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  rcases checkStmtExpr_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.semanticCoverage?_of_signature? hSig

theorem checkExprsAsYulValues_single_builtin_true_has_signature
    {ctx : StaticContext} {builtin : Evm.Builtin} {args : List Expr}
    {resultCount : Nat}
    (h : checkExprsAsYulValues ctx [Expr.builtin builtin args] resultCount =
      true) :
    ∃ sig,
      builtin.signature? = some sig ∧
      sig.paramCount = args.length ∧
      sig.resultCount = resultCount ∧
      checkExprs ctx args = true := by
  unfold checkExprsAsYulValues at h
  cases hs : builtin.signature? with
  | none =>
      simp [hs] at h
  | some sig =>
      have h' :
          (sig.paramCount = args.length ∧ sig.resultCount = resultCount) ∧
          checkExprs ctx args = true := by
        simpa [hs, Bool.and_eq_true] using h
      exact ⟨sig, rfl, h'.1.1, h'.1.2, h'.2⟩

theorem checkExprsAsYulValues_single_builtin_true_has_claim
    {ctx : StaticContext} {builtin : Evm.Builtin} {args : List Expr}
    {resultCount : Nat}
    (h : checkExprsAsYulValues ctx [Expr.builtin builtin args] resultCount =
      true) :
    ∃ claim, builtin.claim? = some claim := by
  rcases checkExprsAsYulValues_single_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.claim?_of_signature? hSig

theorem checkExprsAsYulValues_single_builtin_true_has_semanticCoverage
    {ctx : StaticContext} {builtin : Evm.Builtin} {args : List Expr}
    {resultCount : Nat}
    (h : checkExprsAsYulValues ctx [Expr.builtin builtin args] resultCount =
      true) :
    ∃ coverage, builtin.semanticCoverage? = some coverage := by
  rcases checkExprsAsYulValues_single_builtin_true_has_signature h with
    ⟨sig, hSig, _, _, _⟩
  exact Evm.Builtin.semanticCoverage?_of_signature? hSig

theorem checkBuiltinValueArity_allowed :
    checkExpr StaticContext.empty
      (Expr.builtin Evm.Builtin.add
        [Expr.value (Value.word 1), Expr.value (Value.word 2)]) = true := by
  rfl

theorem checkBuiltinWrongArity_rejected :
    checkExpr StaticContext.empty
      (Expr.builtin Evm.Builtin.add [Expr.value (Value.word 1)]) = false := by
  rfl

theorem checkStatementOnlyBuiltinAsValue_rejected :
    checkExpr StaticContext.empty
      (Expr.builtin Evm.Builtin.mstore
        [Expr.value (Value.word 0), Expr.value (Value.word 7)]) = false := by
  rfl

theorem checkStatementOnlyBuiltinStatement_allowed :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr
        (Expr.builtin Evm.Builtin.mstore
          [Expr.value (Value.word 0), Expr.value (Value.word 7)])) =
      some StaticContext.empty := by
  rfl

theorem checkValueBuiltinAsStatement_rejected :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr
        (Expr.builtin Evm.Builtin.add
          [Expr.value (Value.word 1), Expr.value (Value.word 2)])) = none := by
  rfl

theorem checkLiteralAsStatement_rejected :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr (Expr.value (Value.word 1))) = none := by
  rfl

theorem checkReturnBuiltin_statement_only :
    checkExpr StaticContext.empty
      (Expr.builtin Evm.Builtin.returnOp
        [Expr.value (Value.word 0), Expr.value (Value.word 0)]) = false ∧
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr
        (Expr.builtin Evm.Builtin.returnOp
          [Expr.value (Value.word 0), Expr.value (Value.word 0)])) =
      some StaticContext.empty := by
  constructor <;> rfl

theorem checkVerbatimMultiOutput_rejected :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr
        (Expr.builtin (Evm.Builtin.verbatimOp 1 2)
          [Expr.value (Value.word 7)])) = none := by
  rfl

theorem checkVerbatimMultiOutputLetMany_allowed :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.letMany [0, 1]
        (some
          [Expr.builtin (Evm.Builtin.verbatimOp 1 2)
            [Expr.value (Value.word 7)]])) =
      some { vars := [1, 0], funcs := [] } := by
  rfl

theorem checkVerbatimMultiOutputAssignMany_allowed :
    checkStmtFuel 4 { vars := [0, 1], funcs := [] } false false
      (Stmt.assignMany [0, 1]
        [Expr.builtin (Evm.Builtin.verbatimOp 1 2)
          [Expr.value (Value.word 7)]]) =
      some { vars := [0, 1], funcs := [] } := by
  rfl

theorem checkDuplicateAssignMany_rejected :
    checkStmtFuel 4 { vars := [0], funcs := [] } false false
      (Stmt.assignMany [0, 0]
        [Expr.value (Value.word 1), Expr.value (Value.word 2)]) = none := by
  rfl

theorem checkOpaqueBuiltin_rejected :
    checkStmtFuel 4 StaticContext.empty false false
      (Stmt.expr (Expr.builtin (Evm.Builtin.opaque 0) [])) = none := by
  rfl

theorem checkExpr_opaque_builtin_false
    (ctx : StaticContext) (id : Nat) (args : List Expr) :
    checkExpr ctx (Expr.builtin (Evm.Builtin.opaque id) args) = false := by
  simp [checkExpr, Evm.Builtin.signature?]

theorem checkStmtFuel_opaque_builtin_expr_rejected
    (fuel : Nat) (ctx : StaticContext) (inLoop inFunction : Bool)
    (id : Nat) (args : List Expr) :
    checkStmtFuel fuel.succ ctx inLoop inFunction
      (Stmt.expr (Expr.builtin (Evm.Builtin.opaque id) args)) = none := by
  simp [checkStmtFuel, checkStmtExpr, Evm.Builtin.signature?]

theorem evalBlock_drops_local (outerValue localValue : Value) :
    evalStmt [(0, outerValue)]
        (Stmt.block [Stmt.let1 1 (some (Expr.value localValue))]) =
      some [(0, outerValue)] := by
  simp [evalStmt, evalBlock, evalExpr, declare?, lookup?, restoreOuter]

theorem evalBlock_assignment_persists (oldOuter newOuter localValue : Value) :
    evalStmt [(0, oldOuter)]
        (Stmt.block
          [ Stmt.let1 1 (some (Expr.value localValue))
          , Stmt.assign 0 (Expr.value newOuter) ]) =
      some [(0, newOuter)] := by
  simp [evalStmt, evalBlock, evalExpr, declare?, assign?, lookup?, restoreOuter]

structure CompilerAcceptedStmt (profile : CompilerProfile)
    (fuel : Nat) (ctx : StaticContext) (inLoop inFunction : Bool)
    (stmt : Stmt) (ctx' : StaticContext) : Prop where
  emittable : CompilerEmittableStmt profile stmt
  checked : checkStmtFuel fuel ctx inLoop inFunction stmt = some ctx'

theorem CompilerAcceptedStmt.noOpaqueEvidence
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    StmtNoOpaqueEvidence stmt :=
  CompilerEmittableStmt.noOpaqueEvidence hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidityEmittable_builtinBoundary
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel ctx
        inLoop inFunction stmt ctx') :
    StmtCanonicalSolidityEmittableBoundaryEvidence stmt :=
  CompilerEmittableStmt.currentSolidityEmittable_builtinBoundary
    hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidityEmittable_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel ctx
        inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence
    hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel ctx
        inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  CompilerEmittableStmt.currentSolidityEmittable_builtinClaimEvidence_nonDeferred
    hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidityEmittable_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel ctx
        inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidityEmittableNoVerbatimSemanticCoverage stmt :=
  CompilerEmittableStmt.currentSolidityEmittable_builtinCoverageEvidence
    hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidityEmittable_evidenceBundle
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel ctx
        inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt ∧
      StmtBuiltinClaimEvidence NonDeferredClaim stmt ∧
      StmtBuiltinCoverageEvidence
        CurrentSolidityEmittableNoVerbatimSemanticCoverage stmt ∧
      StmtCanonicalSolidityEmittableBoundaryEvidence stmt :=
  CompilerEmittableStmt.currentSolidityEmittable_evidenceBundle
    hAccepted.emittable

theorem CompilerAcceptedStmt.currentSolidCore_skip_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction Stmt.skip ctx') :
    ctx' = ctx :=
  checkStmtFuel_skip_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_skip_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction Stmt.skip ctx') :
    ctx' = ctx :=
  checkStmtFuel_skip_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_expr_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.expr expr) ctx') :
    checkStmtExpr ctx expr = true ∧ ctx' = ctx :=
  checkStmtFuel_expr_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_expr_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.expr expr) ctx') :
    checkStmtExpr ctx expr = true ∧ ctx' = ctx :=
  checkStmtFuel_expr_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_let1Some_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.let1 name (some expr)) ctx') :
    checkExpr ctx expr = true ∧
      ∃ declCtx, addVarName? ctx name = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_let1_init_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_let1Some_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.let1 name (some expr)) ctx') :
    checkExpr ctx expr = true ∧
      ∃ declCtx, addVarName? ctx name = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_let1_init_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_let1None_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.let1 name none) ctx') :
    ∃ declCtx, addVarName? ctx name = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_let1_default_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_let1None_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.let1 name none) ctx') :
    ∃ declCtx, addVarName? ctx name = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_let1_default_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_letManySome_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.letMany names (some exprs)) ctx') :
    checkExprsAsYulValues ctx exprs names.length = true ∧
      ∃ declCtx, addVarNames? ctx names = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_letMany_init_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_letManySome_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.letMany names (some exprs)) ctx') :
    checkExprsAsYulValues ctx exprs names.length = true ∧
      ∃ declCtx, addVarNames? ctx names = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_letMany_init_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_letManyNone_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.letMany names none) ctx') :
    ∃ declCtx, addVarNames? ctx names = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_letMany_default_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_letManyNone_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.letMany names none) ctx') :
    ∃ declCtx, addVarNames? ctx names = some declCtx ∧ ctx' = declCtx :=
  checkStmtFuel_letMany_default_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_assign_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.assign name expr) ctx') :
    containsName ctx.vars name = true ∧ checkExpr ctx expr = true ∧
      ctx' = ctx :=
  checkStmtFuel_assign_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_assign_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {expr : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.assign name expr) ctx') :
    containsName ctx.vars name = true ∧ checkExpr ctx expr = true ∧
      ctx' = ctx :=
  checkStmtFuel_assign_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_assignMany_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.assignMany names exprs) ctx') :
    namesUnique names = true ∧ namesInScope ctx.vars names = true ∧
      checkExprsAsYulValues ctx exprs names.length = true ∧ ctx' = ctx :=
  checkStmtFuel_assignMany_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_assignMany_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {exprs : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.assignMany names exprs) ctx') :
    namesUnique names = true ∧ namesInScope ctx.vars names = true ∧
      checkExprsAsYulValues ctx exprs names.length = true ∧ ctx' = ctx :=
  checkStmtFuel_assignMany_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_seq_static_obligations
    {fuel : Nat} {ctx ctx'' : StaticContext} {inLoop inFunction : Bool}
    {first second : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.seq first second) ctx'') :
    ∃ seqCtx ctx',
      predeclareStmtFunctionSigs? ctx (Stmt.seq first second) = some seqCtx ∧
      checkStmtFuel fuel seqCtx inLoop inFunction first = some ctx' ∧
      checkStmtFuel fuel ctx' inLoop inFunction second = some ctx'' :=
  checkStmtFuel_seq_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_seq_static_obligations
    {fuel : Nat} {ctx ctx'' : StaticContext} {inLoop inFunction : Bool}
    {first second : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.seq first second) ctx'') :
    ∃ seqCtx ctx',
      predeclareStmtFunctionSigs? ctx (Stmt.seq first second) = some seqCtx ∧
      checkStmtFuel fuel seqCtx inLoop inFunction first = some ctx' ∧
      checkStmtFuel fuel ctx' inLoop inFunction second = some ctx'' :=
  checkStmtFuel_seq_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_block_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmts : List Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.block stmts) ctx') :
    ctx' = ctx ∧
      ∃ blockCtx innerCtx,
        predeclareBlockFunctionSigs? ctx stmts = some blockCtx ∧
        checkBlockFuel fuel blockCtx inLoop inFunction stmts = some innerCtx :=
  checkStmtFuel_block_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_block_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmts : List Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.block stmts) ctx') :
    ctx' = ctx ∧
      ∃ blockCtx innerCtx,
        predeclareBlockFunctionSigs? ctx stmts = some blockCtx ∧
        checkBlockFuel fuel blockCtx inLoop inFunction stmts = some innerCtx :=
  checkStmtFuel_block_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_ifThen_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {cond : Expr} {body : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.ifThen cond body) ctx') :
    checkExpr ctx cond = true ∧ ctx' = ctx ∧
      ∃ bodyCtx, checkStmtFuel fuel ctx inLoop inFunction body = some bodyCtx :=
  checkStmtFuel_if_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_ifThen_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {cond : Expr} {body : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.ifThen cond body) ctx') :
    checkExpr ctx cond = true ∧ ctx' = ctx ∧
      ∃ bodyCtx, checkStmtFuel fuel ctx inLoop inFunction body = some bodyCtx :=
  checkStmtFuel_if_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_funDef_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {params returns : List Name} {body : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.funDef name params returns body) ctx') :
    ∃ fnCtx fnVars bodyCtx,
      ((lookupFunctionSig? ctx.funcs name =
          some
            ({ paramCount := params.length, returnCount := returns.length } :
              FunctionSig) ∧
          fnCtx = ctx) ∨
        addFunctionSigNoShadow? ctx name
          ({ paramCount := params.length, returnCount := returns.length } :
              FunctionSig) =
          some fnCtx) ∧
      initFunctionStaticVars? fnCtx params returns = some fnVars ∧
      checkStmtFuel fuel { vars := fnVars, funcs := fnCtx.funcs } false true
        body = some bodyCtx ∧
      ctx' = fnCtx :=
  checkStmtFuel_funDef_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_funDef_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {name : Name} {params returns : List Name} {body : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.funDef name params returns body) ctx') :
    ∃ fnCtx fnVars bodyCtx,
      ((lookupFunctionSig? ctx.funcs name =
          some
            ({ paramCount := params.length, returnCount := returns.length } :
              FunctionSig) ∧
          fnCtx = ctx) ∨
        addFunctionSigNoShadow? ctx name
          ({ paramCount := params.length, returnCount := returns.length } :
              FunctionSig) =
          some fnCtx) ∧
      initFunctionStaticVars? fnCtx params returns = some fnVars ∧
      checkStmtFuel fuel { vars := fnVars, funcs := fnCtx.funcs } false true
        body = some bodyCtx ∧
      ctx' = fnCtx :=
  checkStmtFuel_funDef_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_letCall_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.letCall names fnName args) ctx') :
    ∃ sig declCtx,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      addVarNames? ctx names = some declCtx ∧
      ctx' = declCtx :=
  checkStmtFuel_letCall_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_letCall_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.letCall names fnName args) ctx') :
    ∃ sig declCtx,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      addVarNames? ctx names = some declCtx ∧
      ctx' = declCtx :=
  checkStmtFuel_letCall_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_assignCall_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.assignCall names fnName args) ctx') :
    ∃ sig,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      namesUnique names = true ∧
      namesInScope ctx.vars names = true ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      ctx' = ctx :=
  checkStmtFuel_assignCall_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_assignCall_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {names : List Name} {fnName : Name} {args : List Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.assignCall names fnName args) ctx') :
    ∃ sig,
      lookupFunctionSig? ctx.funcs fnName = some sig ∧
      namesUnique names = true ∧
      namesInScope ctx.vars names = true ∧
      checkExprs ctx args = true ∧
      sig.paramCount = args.length ∧
      sig.returnCount = names.length ∧
      ctx' = ctx :=
  checkStmtFuel_assignCall_accepted_implies hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_switch_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {discr : Expr} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.switch discr cases defaultBranch) ctx') :
    checkExpr ctx discr = true ∧
      switchHasBranch cases defaultBranch = true ∧
      switchCaseLabelsUnique cases = true ∧
      ctx' = ctx ∧
      checkSwitchCasesFuel fuel ctx inLoop inFunction cases = some () ∧
      (defaultBranch = none ∨
        ∃ branch branchCtx,
          defaultBranch = some branch ∧
            checkStmtFuel fuel ctx inLoop inFunction branch =
              some branchCtx) := by
  rcases checkStmtFuel_switch_accepted_implies hAccepted.checked with
    ⟨hDiscr, hHasBranch, hUnique, hCtx, hCases, hDefault⟩
  refine
    ⟨hDiscr, hHasBranch, hUnique, hCtx, hCases, ?_⟩
  cases defaultBranch with
  | none =>
      exact Or.inl rfl
  | some branch =>
      rcases hDefault with ⟨branchCtx, hBranch⟩
      exact Or.inr ⟨branch, branchCtx, rfl, hBranch⟩

theorem CompilerAcceptedStmt.currentSolidityEmittable_switch_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {discr : Expr} {cases : List (Value × Stmt)}
    {defaultBranch : Option Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.switch discr cases defaultBranch) ctx') :
    checkExpr ctx discr = true ∧
      switchHasBranch cases defaultBranch = true ∧
      switchCaseLabelsUnique cases = true ∧
      ctx' = ctx ∧
      checkSwitchCasesFuel fuel ctx inLoop inFunction cases = some () ∧
      (defaultBranch = none ∨
        ∃ branch branchCtx,
          defaultBranch = some branch ∧
            checkStmtFuel fuel ctx inLoop inFunction branch =
              some branchCtx) := by
  rcases checkStmtFuel_switch_accepted_implies hAccepted.checked with
    ⟨hDiscr, hHasBranch, hUnique, hCtx, hCases, hDefault⟩
  refine
    ⟨hDiscr, hHasBranch, hUnique, hCtx, hCases, ?_⟩
  cases defaultBranch with
  | none =>
      exact Or.inl rfl
  | some branch =>
      rcases hDefault with ⟨branchCtx, hBranch⟩
      exact Or.inr ⟨branch, branchCtx, rfl, hBranch⟩

theorem CompilerAcceptedStmt.currentSolidCore_forLoop_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {pre post body : Stmt} {cond : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction (Stmt.forLoop pre cond post body) ctx') :
    ctx' = ctx ∧
      stmtHasNoFunDefs pre = true ∧
      ∃ loopCtx bodyCtx postCtx,
        checkStmtFuel fuel ctx false inFunction pre = some loopCtx ∧
          checkExpr loopCtx cond = true ∧
          checkStmtFuel fuel loopCtx true inFunction body = some bodyCtx ∧
          checkStmtFuel fuel loopCtx false inFunction post = some postCtx :=
  checkStmtFuel_for_accepted_implies_any_loop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_forLoop_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {pre post body : Stmt} {cond : Expr}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction (Stmt.forLoop pre cond post body) ctx') :
    ctx' = ctx ∧
      stmtHasNoFunDefs pre = true ∧
      ∃ loopCtx bodyCtx postCtx,
        checkStmtFuel fuel ctx false inFunction pre = some loopCtx ∧
          checkExpr loopCtx cond = true ∧
          checkStmtFuel fuel loopCtx true inFunction body = some bodyCtx ∧
          checkStmtFuel fuel loopCtx false inFunction post = some postCtx :=
  checkStmtFuel_for_accepted_implies_any_loop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_break_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction Stmt.break ctx') :
    inLoop = true ∧ ctx' = ctx :=
  checkBreak_accepted_implies_inLoop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_continue_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction Stmt.continue ctx') :
    inLoop = true ∧ ctx' = ctx :=
  checkContinue_accepted_implies_inLoop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_break_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction Stmt.break ctx') :
    inLoop = true ∧ ctx' = ctx :=
  checkBreak_accepted_implies_inLoop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_continue_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction Stmt.continue ctx') :
    inLoop = true ∧ ctx' = ctx :=
  checkContinue_accepted_implies_inLoop hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidCore_leave_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore fuel.succ ctx
        inLoop inFunction Stmt.leave ctx') :
    inFunction = true ∧ ctx' = ctx :=
  checkLeave_accepted_implies_inFunction hAccepted.checked

theorem CompilerAcceptedStmt.currentSolidityEmittable_leave_static_obligations
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidityEmittable fuel.succ
        ctx inLoop inFunction Stmt.leave ctx') :
    inFunction = true ∧ ctx' = ctx :=
  checkLeave_accepted_implies_inFunction hAccepted.checked

theorem CompilerAcceptedStmt.mono_profile
    {source target : CompilerProfile}
    (hLe : CompilerProfile.Le source target)
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt source fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt target fuel ctx inLoop inFunction stmt ctx' where
  emittable := CompilerEmittableStmt.mono hLe hAccepted.emittable
  checked := hAccepted.checked

theorem CompilerAcceptedStmt.withExternalCalls
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt profile.withExternalCalls fuel ctx inLoop inFunction
      stmt ctx' :=
  hAccepted.mono_profile (CompilerProfile.le_withExternalCalls profile)

theorem CompilerAcceptedStmt.withMemoryBuiltins
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt profile.withMemoryBuiltins fuel ctx inLoop inFunction
      stmt ctx' :=
  hAccepted.mono_profile (CompilerProfile.le_withMemoryBuiltins profile)

theorem CompilerAcceptedStmt.withMemoryHashBuiltins
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt profile.withMemoryHashBuiltins fuel ctx
      inLoop inFunction stmt ctx' :=
  hAccepted.mono_profile
    (CompilerProfile.le_withMemoryHashBuiltins profile)

theorem CompilerAcceptedStmt.withBufferBuiltins
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt profile.withBufferBuiltins fuel ctx inLoop inFunction
      stmt ctx' :=
  hAccepted.mono_profile (CompilerProfile.le_withBufferBuiltins profile)

theorem CompilerAcceptedStmt.withCompilerAnnotations
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    CompilerAcceptedStmt profile.withCompilerAnnotations fuel ctx
      inLoop inFunction stmt ctx' :=
  hAccepted.mono_profile
    (CompilerProfile.le_withCompilerAnnotations profile)

theorem CompilerAcceptedStmt.builtinEvidence
    {profile : CompilerProfile}
    {builtinEvidence : Evm.Builtin -> Prop}
    (hProfileBuiltin :
      ∀ {builtin : Evm.Builtin}, profile.builtinOK builtin ->
        builtinEvidence builtin)
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinEvidence builtinEvidence stmt :=
  CompilerEmittableStmt.builtinEvidence
    (profile := profile) (builtinEvidence := builtinEvidence)
    hProfileBuiltin hAccepted.emittable

theorem CompilerAcceptedStmt.builtinSemanticEvidence
    {profile : CompilerProfile}
    {fuel : Nat} {ctx ctx' : StaticContext} {inLoop inFunction : Bool}
    {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt profile fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinSemanticEvidence stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.builtinOK_semanticEvidence profile hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinClaimEvidence_exactOrAbstracted
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  hAccepted.currentSolidCore_builtinClaimEvidence
    |>.exactYul_to_exactOrAbstracted

theorem CompilerAcceptedStmt.currentSolidCore_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCore_builtinClaimEvidence
    |>.exactYul_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithMemoryBuiltins_builtinClaimEvidence
    |>.exactYul_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryHashBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactAbstractedOrSymbolicClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinClaimEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryHashBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithMemoryHashBuiltins_builtinClaimEvidence
    |>.exactAbstractedOrSymbolic_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withBufferBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withBufferBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withBufferBuiltins
      fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithBufferBuiltins_builtinClaimEvidence
    |>.exactYul_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withObjectDataBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withObjectDataBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithObjectDataBuiltins_builtinClaimEvidence
    |>.exactYul_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithContextBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withContextBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactYulClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withContextBuiltins_builtinClaimEvidence_exactYul
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithContextBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withContextBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithContextBuiltins_builtinClaimEvidence
    |>.exactYul_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerAnnotations
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinClaimEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerAnnotations
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithCompilerAnnotations_builtinClaimEvidence
    |>.exactOrAbstracted_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinClaimEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithCompilerArtifactBuiltins_builtinClaimEvidence
    |>.exactOrAbstracted_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence CurrentSolidCoreSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_builtinCoverageEvidence hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withExternalCalls
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithExternalCallsSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withExternalCalls

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withMemoryBuiltins
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemorySemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withMemoryBuiltins

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemorySemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withMemoryHashBuiltins
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemoryHashSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withMemoryHashBuiltins

theorem CompilerAcceptedStmt.currentSolidCoreWithMemoryHashBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withMemoryHashBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithMemoryHashSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withMemoryHashBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withBufferBuiltins
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithBufferSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withBufferBuiltins

theorem CompilerAcceptedStmt.currentSolidCoreWithBufferBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withBufferBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithBufferSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withBufferBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withObjectDataBuiltins
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithObjectDataSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withObjectDataBuiltins

theorem CompilerAcceptedStmt.currentSolidCoreWithObjectDataBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withObjectDataBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithObjectDataSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withObjectDataBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withContextBuiltins
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithContextSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withContextBuiltins

theorem CompilerAcceptedStmt.currentSolidCoreWithContextBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withContextBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithContextSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withContextBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withCompilerAnnotations
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withCompilerAnnotations

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerAnnotations_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerAnnotations
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerAnnotationsSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerAnnotations_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCore_builtinCoverageEvidence_withCompilerArtifacts
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt CompilerProfile.currentSolidCore
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage stmt :=
  hAccepted.currentSolidCore_builtinCoverageEvidence
    |>.currentSolidCore_to_withCompilerArtifacts

theorem CompilerAcceptedStmt.currentSolidCoreWithCompilerArtifactBuiltins_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withCompilerArtifactBuiltins
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithCompilerArtifactsSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withCompilerArtifactBuiltins_builtinCoverageEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithExternalCalls_builtinClaimEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withExternalCalls
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence ExactOrAbstractedClaim stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withExternalCalls_builtinClaimEvidence
        hBuiltin)

theorem CompilerAcceptedStmt.currentSolidCoreWithExternalCalls_builtinClaimEvidence_nonDeferred
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withExternalCalls
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinClaimEvidence NonDeferredClaim stmt :=
  hAccepted.currentSolidCoreWithExternalCalls_builtinClaimEvidence
    |>.exactOrAbstracted_to_nonDeferred

theorem CompilerAcceptedStmt.currentSolidCoreWithExternalCalls_builtinCoverageEvidence
    {fuel : Nat} {ctx ctx' : StaticContext}
    {inLoop inFunction : Bool} {stmt : Stmt}
    (hAccepted :
      CompilerAcceptedStmt
        CompilerProfile.currentSolidCore.withExternalCalls
        fuel ctx inLoop inFunction stmt ctx') :
    StmtBuiltinCoverageEvidence
      CurrentSolidCoreWithExternalCallsSemanticCoverage stmt :=
  hAccepted.builtinEvidence
    (fun hBuiltin =>
      CompilerProfile.currentSolidCore_withExternalCalls_builtinCoverageEvidence
        hBuiltin)

end FullYul
end SolidCoreYulCore

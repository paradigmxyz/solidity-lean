import SharedSemantics.Word
import SolidCore.Spine.L04_StackCfg.Interface
import SolidCore.Spine.Passes.P05_StackCfgToBytecode.Interface
import SolidCore.Spine.Passes.P06_BytecodeToEvm.Interface

namespace SolidCore
namespace Spine
namespace YulEvm

abbrev Word := SharedSemantics.Word
abbrev Name := Nat
abbrev Env := List (Name × Word)
abbrev Layout := List Name
abbrev Stack := List Word

namespace Env

def lookup? : Env -> Name -> Option Word
  | [], _ => none
  | (candidate, value) :: rest, name =>
      if candidate = name then
        some (SharedSemantics.norm value)
      else
        lookup? rest name

end Env

namespace Layout

def indexOfAux? : Layout -> Name -> Nat -> Option Nat
  | [], _, _ => none
  | candidate :: rest, name, depth =>
      if candidate = name then
        some depth
      else
        indexOfAux? rest name (depth + 1)

def indexOf? (layout : Layout) (name : Name) : Option Nat :=
  indexOfAux? layout name 0

theorem indexOfAux?_eq_indexOf?_map :
    ∀ (layout : Layout) (name : Name) (start : Nat),
      indexOfAux? layout name start =
        (indexOf? layout name).map (fun depth => start + depth)
  | [], _name, _start => rfl
  | candidate :: rest, name, start => by
      by_cases hCandidate : candidate = name
      · subst candidate
        simp [indexOf?, indexOfAux?]
      · simp [indexOf?, indexOfAux?, hCandidate,
          indexOfAux?_eq_indexOf?_map rest name (start + 1),
          indexOfAux?_eq_indexOf?_map rest name 1]
        cases indexOfAux? rest name 0 <;>
          simp [Function.comp_apply, Nat.add_comm, Nat.add_left_comm]

theorem indexOf?_cons_ne
    {head query : Name} {layout : Layout} {depth : Nat}
    (hNe : head ≠ query)
    (hIndex : indexOf? (head :: layout) query = some depth) :
    ∃ oldDepth,
      indexOf? layout query = some oldDepth ∧ depth = oldDepth + 1 := by
  simp [indexOf?, indexOfAux?, hNe] at hIndex
  rw [indexOfAux?_eq_indexOf?_map] at hIndex
  cases hOld : indexOf? layout query with
  | none =>
      simp [hOld] at hIndex
  | some oldDepth =>
      simp [hOld] at hIndex
      cases hIndex
      exact ⟨oldDepth, by simp, by omega⟩

theorem indexOfAux?_lt_start_add_length :
    ∀ {layout : Layout} {name : Name} {start depth : Nat},
      indexOfAux? layout name start = some depth ->
      depth < start + layout.length
  | [], _name, _start, _depth, hIndex => by
      simp [indexOfAux?] at hIndex
  | candidate :: rest, name, start, depth, hIndex => by
      by_cases hCandidate : candidate = name
      · simp [indexOfAux?, hCandidate] at hIndex
        cases hIndex
        simp
      · simp [indexOfAux?, hCandidate] at hIndex
        have hTail :=
          indexOfAux?_lt_start_add_length
            (layout := rest) (name := name) (start := start + 1)
            (depth := depth) hIndex
        simp at hTail ⊢
        omega

theorem indexOf?_lt_length
    {layout : Layout} {name : Name} {depth : Nat}
    (hIndex : indexOf? layout name = some depth) :
    depth < layout.length := by
  have h :=
    indexOfAux?_lt_start_add_length
      (layout := layout) (name := name) (start := 0)
      (depth := depth) hIndex
  simpa [indexOf?] using h

end Layout

def stackAt : Stack -> Nat -> Option Word
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, depth + 1 => stackAt rest depth

theorem stackAt_cons_succ (value : Word) (stack : Stack) (depth : Nat) :
    stackAt (value :: stack) (depth + 1) = stackAt stack depth := by
  rfl

theorem stackAt_eq_getElem? (stack : Stack) (depth : Nat) :
    stackAt stack depth = stack[depth]? := by
  induction stack generalizing depth with
  | nil =>
      cases depth <;> rfl
  | cons _ rest ih =>
      cases depth with
      | zero =>
          rfl
      | succ depth =>
          exact ih depth

inductive UnaryOp where
  | iszero
  | notOp
  deriving Repr, DecidableEq

inductive BinaryOp where
  | add
  | mul
  | div
  | signextend
  | modOp
  | sub
  | eq
  | lt
  | gt
  | andOp
  | orOp
  | xor
  | byteOp
  | shl
  | shr
  | sar
  deriving Repr, DecidableEq

def UnaryOp.eval : UnaryOp -> Word -> Word
  | UnaryOp.iszero, value => SharedSemantics.iszeroWord value
  | UnaryOp.notOp, value => SharedSemantics.notWord value

def BinaryOp.eval : BinaryOp -> Word -> Word -> Word
  | BinaryOp.add, lhs, rhs => SharedSemantics.addWord lhs rhs
  | BinaryOp.mul, lhs, rhs => SharedSemantics.mulWord lhs rhs
  | BinaryOp.div, lhs, rhs => SharedSemantics.divWord lhs rhs
  | BinaryOp.signextend, lhs, rhs => SharedSemantics.signextendWord lhs rhs
  | BinaryOp.modOp, lhs, rhs => SharedSemantics.modWord lhs rhs
  | BinaryOp.sub, lhs, rhs => SharedSemantics.subWord lhs rhs
  | BinaryOp.eq, lhs, rhs => SharedSemantics.eqWord lhs rhs
  | BinaryOp.lt, lhs, rhs => SharedSemantics.ltWord lhs rhs
  | BinaryOp.gt, lhs, rhs => SharedSemantics.gtWord lhs rhs
  | BinaryOp.andOp, lhs, rhs => SharedSemantics.andWord lhs rhs
  | BinaryOp.orOp, lhs, rhs => SharedSemantics.orWord lhs rhs
  | BinaryOp.xor, lhs, rhs => SharedSemantics.xorWord lhs rhs
  | BinaryOp.byteOp, lhs, rhs => SharedSemantics.byteWord lhs rhs
  | BinaryOp.shl, lhs, rhs => SharedSemantics.shlWord lhs rhs
  | BinaryOp.shr, lhs, rhs => SharedSemantics.shrWord lhs rhs
  | BinaryOp.sar, lhs, rhs => SharedSemantics.sarWord lhs rhs

theorem norm_zero : SharedSemantics.norm 0 = 0 := by
  simp [SharedSemantics.norm]

theorem one_lt_wordModulus : 1 < SharedSemantics.wordModulus := by
  native_decide

theorem byte_lt_wordModulus : 256 < SharedSemantics.wordModulus := by
  native_decide

theorem norm_one : SharedSemantics.norm 1 = 1 := by
  unfold SharedSemantics.norm
  exact Nat.mod_eq_of_lt one_lt_wordModulus

theorem norm_eq_of_lt_byte {value : Word} (hByte : value < 256) :
    SharedSemantics.norm value = value := by
  unfold SharedSemantics.norm
  exact Nat.mod_eq_of_lt (Nat.lt_trans hByte byte_lt_wordModulus)

theorem norm_if_one_zero (p : Prop) [Decidable p] :
    SharedSemantics.norm (if p then 1 else 0) =
      (if p then 1 else 0) := by
  by_cases h : p <;> simp [h, norm_zero, norm_one]

theorem UnaryOp.eval_normalized (op : UnaryOp) (value : Word) :
    SharedSemantics.norm (op.eval value) = op.eval value := by
  cases op with
  | iszero =>
      simpa [UnaryOp.eval, SharedSemantics.iszeroWord]
        using norm_if_one_zero (SharedSemantics.norm value = 0)
  | notOp =>
      simp [UnaryOp.eval, SharedSemantics.notWord,
        SharedSemantics.norm_norm]

theorem BinaryOp.eval_normalized
    (op : BinaryOp) (lhs rhs : Word) :
    SharedSemantics.norm (op.eval lhs rhs) = op.eval lhs rhs := by
  cases op with
  | add =>
      simp [BinaryOp.eval, SharedSemantics.addWord,
        SharedSemantics.norm_norm]
  | mul =>
      simp [BinaryOp.eval, SharedSemantics.mulWord,
        SharedSemantics.norm_norm]
  | div =>
      by_cases hZero : SharedSemantics.norm rhs = 0
      · simp [BinaryOp.eval, SharedSemantics.divWord, hZero, norm_zero]
      · simp [BinaryOp.eval, SharedSemantics.divWord, hZero,
          SharedSemantics.norm_norm]
  | signextend =>
      by_cases hIx : SharedSemantics.norm lhs < 32
      · simp [BinaryOp.eval, SharedSemantics.signextendWord, hIx,
          SharedSemantics.norm_norm]
      · simp [BinaryOp.eval, SharedSemantics.signextendWord, hIx,
          SharedSemantics.norm_norm]
  | modOp =>
      by_cases hZero : SharedSemantics.norm rhs = 0
      · simp [BinaryOp.eval, SharedSemantics.modWord, hZero, norm_zero]
      · simp [BinaryOp.eval, SharedSemantics.modWord, hZero,
          SharedSemantics.norm_norm]
  | sub =>
      simp [BinaryOp.eval, SharedSemantics.subWord,
        SharedSemantics.norm_norm]
  | eq =>
      simpa [BinaryOp.eval, SharedSemantics.eqWord]
        using norm_if_one_zero
          (SharedSemantics.norm lhs = SharedSemantics.norm rhs)
  | lt =>
      simpa [BinaryOp.eval, SharedSemantics.ltWord]
        using norm_if_one_zero
          (SharedSemantics.norm lhs < SharedSemantics.norm rhs)
  | gt =>
      simpa [BinaryOp.eval, SharedSemantics.gtWord]
        using norm_if_one_zero
          (SharedSemantics.norm rhs < SharedSemantics.norm lhs)
  | andOp =>
      simp [BinaryOp.eval, SharedSemantics.andWord,
        SharedSemantics.norm_norm]
  | orOp =>
      simp [BinaryOp.eval, SharedSemantics.orWord,
        SharedSemantics.norm_norm]
  | xor =>
      simp [BinaryOp.eval, SharedSemantics.xorWord,
        SharedSemantics.norm_norm]
  | byteOp =>
      by_cases hIx : SharedSemantics.norm lhs < 32
      · simp [BinaryOp.eval, SharedSemantics.byteWord, hIx,
          SharedSemantics.norm_norm]
      · simp [BinaryOp.eval, SharedSemantics.byteWord, hIx, norm_zero]
  | shl =>
      by_cases hShift : 256 <= SharedSemantics.norm lhs
      · simp [BinaryOp.eval, SharedSemantics.shlWord, hShift, norm_zero]
      · simp [BinaryOp.eval, SharedSemantics.shlWord, hShift,
          SharedSemantics.norm_norm]
  | shr =>
      by_cases hShift : 256 <= SharedSemantics.norm lhs
      · simp [BinaryOp.eval, SharedSemantics.shrWord, hShift, norm_zero]
      · simp [BinaryOp.eval, SharedSemantics.shrWord, hShift,
          SharedSemantics.norm_norm]
  | sar =>
      by_cases hShift : 256 <= SharedSemantics.norm lhs
      · by_cases hSigned : SharedSemantics.signedValue rhs < 0
        · simp [BinaryOp.eval, SharedSemantics.sarWord, hShift, hSigned,
            SharedSemantics.norm_norm]
        · simp [BinaryOp.eval, SharedSemantics.sarWord, hShift, hSigned,
            norm_zero]
      · simp [BinaryOp.eval, SharedSemantics.sarWord, hShift,
          SharedSemantics.signedToWord, SharedSemantics.norm_norm]

/--
Normalized, checked-input Yul expression fragment. This is an AST-level
milestone, not a parser claim. Binary expressions evaluate their right argument
first to match the EVM-dialect Yul stack compilation order documented by
Solidity and used by Nethermind's `evalArgs`.
-/
inductive Expr where
  | word : Word -> Expr
  | var : Name -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  deriving Repr, DecidableEq

def Expr.eval? (env : Env) : Expr -> Option Word
  | Expr.word value => some (SharedSemantics.norm value)
  | Expr.var name => Env.lookup? env name
  | Expr.unary op expr => do
      let value ← expr.eval? env
      some (op.eval value)
  | Expr.binary op lhs rhs => do
      let rhsValue ← rhs.eval? env
      let lhsValue ← lhs.eval? env
      some (op.eval lhsValue rhsValue)

theorem Expr.eval?_normalized :
    ∀ {env : Env} {expr : Expr} {value : Word},
      expr.eval? env = some value ->
      SharedSemantics.norm value = value := by
  intro env expr
  induction expr with
  | word literal =>
      intro value hEval
      simp [Expr.eval?] at hEval
      cases hEval
      exact SharedSemantics.norm_norm literal
  | var name =>
      intro value hEval
      simp [Expr.eval?] at hEval
      induction env with
      | nil =>
          simp [Env.lookup?] at hEval
      | cons binding rest ih =>
          cases binding with
          | mk candidate stored =>
              by_cases hCandidate : candidate = name
              · simp [Env.lookup?, hCandidate] at hEval
                cases hEval
                exact SharedSemantics.norm_norm stored
              · simp [Env.lookup?, hCandidate] at hEval
                exact ih hEval
  | unary op expr ih =>
      intro value hEval
      simp [Expr.eval?] at hEval
      cases hExpr : Expr.eval? env expr with
      | none =>
          simp [hExpr] at hEval
      | some exprValue =>
          simp [hExpr] at hEval
          cases hEval
          exact UnaryOp.eval_normalized op exprValue
  | binary op lhs rhs lhsIH rhsIH =>
      intro value hEval
      simp [Expr.eval?] at hEval
      cases hRhs : Expr.eval? env rhs with
      | none =>
          simp [hRhs] at hEval
      | some rhsValue =>
          simp [hRhs] at hEval
          cases hLhs : Expr.eval? env lhs with
          | none =>
              simp [hLhs] at hEval
          | some lhsValue =>
              simp [hLhs] at hEval
              cases hEval
              exact BinaryOp.eval_normalized op lhsValue rhsValue

def Expr.acceptedWithLayout? (layout : Layout) : Expr -> Bool
  | Expr.word _ => true
  | Expr.var name => (Layout.indexOf? layout name).isSome
  | Expr.unary _ expr => expr.acceptedWithLayout? layout
  | Expr.binary _ lhs rhs =>
      lhs.acceptedWithLayout? layout && rhs.acceptedWithLayout? layout

/--
First structured statement fragment. `letIn` is intentionally non-shadowing in
the accepted/compiler path so the initial stack-layout invariant can stay
simple and explicit.
-/
inductive Stmt where
  | returnExpr : Expr -> Stmt
  | exprThen : Expr -> Stmt -> Stmt
  | block : Stmt -> Stmt
  | letIn : Name -> Expr -> Stmt -> Stmt
  deriving Repr, DecidableEq

def Stmt.eval? (env : Env) : Stmt -> Option Word
  | Stmt.returnExpr expr => expr.eval? env
  | Stmt.exprThen expr body => do
      let _ ← expr.eval? env
      body.eval? env
  | Stmt.block body => body.eval? env
  | Stmt.letIn name rhs body => do
      let rhsValue ← rhs.eval? env
      body.eval? ((name, rhsValue) :: env)

def Stmt.acceptedWithLayout? (layout : Layout) : Stmt -> Bool
  | Stmt.returnExpr expr => expr.acceptedWithLayout? layout
  | Stmt.exprThen expr body =>
      expr.acceptedWithLayout? layout &&
        body.acceptedWithLayout? layout
  | Stmt.block body => body.acceptedWithLayout? layout
  | Stmt.letIn name rhs body =>
      (Layout.indexOf? layout name).isNone &&
        rhs.acceptedWithLayout? layout &&
          body.acceptedWithLayout? (name :: layout)

def Stmt.evalByte? (stmt : Stmt) : Option Word := do
  let value ← stmt.eval? []
  if value < 256 then
    some value
  else
    none

/--
Closed-program accepted checker for the current pure fragment when the final
returned word is byte-sized. This is an AST checker, not a parser or gas claim.
-/
def Stmt.acceptedTopByte? (stmt : Stmt) : Bool :=
  stmt.acceptedWithLayout? [] && stmt.evalByte?.isSome

theorem Stmt.evalByte?_eq_some
    {stmt : Stmt} {value : Word}
    (hEvalByte : stmt.evalByte? = some value) :
    stmt.eval? [] = some value ∧ value < 256 := by
  unfold Stmt.evalByte? at hEvalByte
  cases hEval : stmt.eval? [] with
  | none =>
      simp [hEval] at hEvalByte
  | some evaluated =>
      simp [hEval] at hEvalByte
      by_cases hByte : evaluated < 256
      · simp [hByte] at hEvalByte
        cases hEvalByte
        exact ⟨by simp, hByte⟩
      · simp [hByte] at hEvalByte

inductive StackInstr where
  | push : Word -> StackInstr
  | dup : Nat -> StackInstr
  | swap : Nat -> StackInstr
  | pop : StackInstr
  | unary : UnaryOp -> StackInstr
  | binary : BinaryOp -> StackInstr
  deriving Repr, DecidableEq

def StackInstr.exec : StackInstr -> Stack -> Option Stack
  | StackInstr.push value, stack =>
      some (SharedSemantics.norm value :: stack)
  | StackInstr.dup depth, stack => do
      let value ← stackAt stack depth
      some (value :: stack)
  | StackInstr.swap _, [] =>
      none
  | StackInstr.swap index, top :: rest => do
      let target ← rest[index]?
      let rest' ← L04_StackCfg.replaceAt? rest index top
      some (target :: rest')
  | StackInstr.pop, [] =>
      none
  | StackInstr.pop, _ :: rest =>
      some rest
  | StackInstr.unary op, value :: rest =>
      some (op.eval value :: rest)
  | StackInstr.unary _, [] =>
      none
  | StackInstr.binary op, lhs :: rhs :: rest =>
      some (op.eval lhs rhs :: rest)
  | StackInstr.binary _, _ =>
      none

def StackCode.run : List StackInstr -> Stack -> Option Stack
  | [], stack => some stack
  | instr :: rest, stack => do
      let stack' ← instr.exec stack
      StackCode.run rest stack'

theorem StackCode.run_append (first second : List StackInstr)
    (stack : Stack) :
    StackCode.run (first ++ second) stack =
      match StackCode.run first stack with
      | some stack' => StackCode.run second stack'
      | none => none := by
  induction first generalizing stack with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [StackCode.run]
      cases hExec : StackInstr.exec instr stack with
      | none =>
          rfl
      | some stack' =>
          exact ih stack'

namespace StackInstr

def stackDepthAfter? : Nat -> StackInstr -> Option Nat
  | depth, StackInstr.push _ => some (depth + 1)
  | depth, StackInstr.dup index =>
      if index < depth then some (depth + 1) else none
  | depth, StackInstr.swap index =>
      if index + 1 < depth then some depth else none
  | depth + 1, StackInstr.pop => some depth
  | 0, StackInstr.pop => none
  | depth + 1, StackInstr.unary _ => some (depth + 1)
  | 0, StackInstr.unary _ => none
  | 0, StackInstr.binary _ => none
  | 1, StackInstr.binary _ => none
  | depth + 2, StackInstr.binary _ => some (depth + 1)

end StackInstr

namespace StackCode

def stackDepthAfter? : Nat -> List StackInstr -> Option Nat
  | depth, [] => some depth
  | depth, instr :: rest => do
      let depth' ← instr.stackDepthAfter? depth
      stackDepthAfter? depth' rest

theorem stackDepthAfter?_append
    (first second : List StackInstr) (depth : Nat) :
    stackDepthAfter? depth (first ++ second) =
      match stackDepthAfter? depth first with
      | some depth' => stackDepthAfter? depth' second
      | none => none := by
  induction first generalizing depth with
  | nil =>
      simp [stackDepthAfter?]
  | cons instr rest ih =>
      simp [stackDepthAfter?]
      cases StackInstr.stackDepthAfter? depth instr <;> simp [ih]

end StackCode

namespace UnaryOp

def toStackCfg? : UnaryOp -> Option L04_StackCfg.PrimOp
  | UnaryOp.iszero => some L04_StackCfg.PrimOp.iszero
  | UnaryOp.notOp => some L04_StackCfg.PrimOp.notOp

theorem toStackCfg?_complete (op : UnaryOp) :
    ∃ cfgOp, op.toStackCfg? = some cfgOp := by
  cases op <;> simp [toStackCfg?]

end UnaryOp

namespace BinaryOp

def toStackCfg? : BinaryOp -> Option L04_StackCfg.PrimOp
  | BinaryOp.add => some L04_StackCfg.PrimOp.add
  | BinaryOp.mul => some L04_StackCfg.PrimOp.mul
  | BinaryOp.div => some L04_StackCfg.PrimOp.div
  | BinaryOp.modOp => some L04_StackCfg.PrimOp.modOp
  | BinaryOp.sub => some L04_StackCfg.PrimOp.sub
  | BinaryOp.eq => some L04_StackCfg.PrimOp.eq
  | BinaryOp.lt => some L04_StackCfg.PrimOp.lt
  | BinaryOp.gt => some L04_StackCfg.PrimOp.gt
  | BinaryOp.andOp => some L04_StackCfg.PrimOp.andOp
  | BinaryOp.orOp => some L04_StackCfg.PrimOp.orOp
  | BinaryOp.xor => some L04_StackCfg.PrimOp.xor

theorem toStackCfg?_complete (op : BinaryOp) :
    ∃ cfgOp, op.toStackCfg? = some cfgOp := by
  cases op <;> simp [toStackCfg?]

end BinaryOp

namespace StackInstr

def toStackCfg? : StackInstr -> Option (List L04_StackCfg.Instr)
  | StackInstr.push value =>
      some [L04_StackCfg.Instr.push
        (L04_StackCfg.Atom.word (SharedSemantics.norm value))]
  | StackInstr.dup depth =>
      some [L04_StackCfg.Instr.dup depth]
  | StackInstr.swap index =>
      some [L04_StackCfg.Instr.swap index]
  | StackInstr.pop =>
      some [L04_StackCfg.Instr.pop]
  | StackInstr.unary op => do
      let cfgOp ← op.toStackCfg?
      some [L04_StackCfg.Instr.op cfgOp]
  | StackInstr.binary op => do
      let cfgOp ← op.toStackCfg?
      some [L04_StackCfg.Instr.swap 0, L04_StackCfg.Instr.op cfgOp]

theorem toStackCfg?_correct
    {instr : StackInstr} {cfg : List L04_StackCfg.Instr}
    {stack out : Stack}
    (hLower : instr.toStackCfg? = some cfg)
    (hExec : instr.exec stack = some out) :
    L04_StackCfg.execInstrs stack cfg = some out := by
  cases instr with
  | push value =>
      simp [toStackCfg?] at hLower
      cases hLower
      simpa [StackInstr.exec, L04_StackCfg.execInstrs,
        L04_StackCfg.execInstr] using hExec
  | dup depth =>
      simp [toStackCfg?] at hLower
      cases hLower
      cases hAt : stackAt stack depth with
      | none =>
          simp [StackInstr.exec, hAt] at hExec
      | some value =>
          simp [StackInstr.exec, hAt] at hExec
          cases hExec
          rw [stackAt_eq_getElem?] at hAt
          simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr, hAt]
  | swap index =>
      simp [toStackCfg?] at hLower
      cases hLower
      cases stack with
      | nil =>
          simp [StackInstr.exec] at hExec
      | cons top rest =>
          cases hTarget : rest[index]? with
          | none =>
              simp [StackInstr.exec, hTarget] at hExec
          | some target =>
              simp [StackInstr.exec, hTarget] at hExec
              cases hReplace : L04_StackCfg.replaceAt? rest index top with
              | none =>
                  simp [hReplace] at hExec
              | some rest' =>
                  simp [hReplace] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    hTarget, hReplace]
  | pop =>
      simp [toStackCfg?] at hLower
      cases hLower
      cases stack with
      | nil =>
          simp [StackInstr.exec] at hExec
      | cons top rest =>
          simp [StackInstr.exec] at hExec
          cases hExec
          simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr]
  | unary op =>
      cases op with
      | iszero =>
          simp [toStackCfg?, UnaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons value rest =>
              simp [StackInstr.exec, UnaryOp.eval] at hExec
              cases hExec
              simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr]
      | notOp =>
          simp [toStackCfg?, UnaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons value rest =>
              simp [StackInstr.exec, UnaryOp.eval] at hExec
              cases hExec
              simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr]
  | binary op =>
      cases op with
      | add =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | mul =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | div =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | modOp =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | sub =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | eq =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | lt =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | gt =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | andOp =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | orOp =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]
      | xor =>
          simp [toStackCfg?, BinaryOp.toStackCfg?] at hLower
          cases hLower
          cases stack with
          | nil =>
              simp [StackInstr.exec] at hExec
          | cons lhs rest =>
              cases rest with
              | nil =>
                  simp [StackInstr.exec] at hExec
              | cons rhs tail =>
                  simp [StackInstr.exec, BinaryOp.eval] at hExec
                  cases hExec
                  simp [L04_StackCfg.execInstrs, L04_StackCfg.execInstr,
                    L04_StackCfg.replaceAt?]

theorem toStackCfg?_stackDepth
    {instr : StackInstr} {cfg : List L04_StackCfg.Instr}
    {depth : Nat}
    (hLower : instr.toStackCfg? = some cfg) :
    L04_StackCfg.stackDepthAfter? depth cfg =
      instr.stackDepthAfter? depth := by
  cases instr with
  | push value =>
      simp [toStackCfg?, StackInstr.stackDepthAfter?] at hLower ⊢
      cases hLower
      simp [L04_StackCfg.stackDepthAfter?,
        L04_StackCfg.Instr.stackDepthAfter?]
  | dup index =>
      simp [toStackCfg?, StackInstr.stackDepthAfter?] at hLower ⊢
      cases hLower
      by_cases hIndex : index < depth <;>
        simp [L04_StackCfg.stackDepthAfter?,
          L04_StackCfg.Instr.stackDepthAfter?, hIndex]
  | swap index =>
      simp [toStackCfg?, StackInstr.stackDepthAfter?] at hLower ⊢
      cases hLower
      by_cases hIndex : index + 1 < depth <;>
        simp [L04_StackCfg.stackDepthAfter?,
          L04_StackCfg.Instr.stackDepthAfter?, hIndex]
  | pop =>
      simp [toStackCfg?, StackInstr.stackDepthAfter?] at hLower ⊢
      cases hLower
      cases depth <;>
        simp [L04_StackCfg.stackDepthAfter?,
          L04_StackCfg.Instr.stackDepthAfter?]
  | unary op =>
      simp [toStackCfg?] at hLower
      cases op <;>
        simp [UnaryOp.toStackCfg?] at hLower
      all_goals
        cases hLower
        cases depth <;>
          simp [L04_StackCfg.stackDepthAfter?,
            L04_StackCfg.Instr.stackDepthAfter?,
            StackInstr.stackDepthAfter?]
  | binary op =>
      simp [toStackCfg?] at hLower
      cases op <;>
        simp [BinaryOp.toStackCfg?] at hLower
      all_goals
        cases hLower
        cases depth with
        | zero =>
            simp [L04_StackCfg.stackDepthAfter?,
              L04_StackCfg.Instr.stackDepthAfter?,
              StackInstr.stackDepthAfter?]
        | succ depth =>
            cases depth with
            | zero =>
                simp [L04_StackCfg.stackDepthAfter?,
                  L04_StackCfg.Instr.stackDepthAfter?,
                  StackInstr.stackDepthAfter?]
            | succ depth =>
                simp [L04_StackCfg.stackDepthAfter?,
                  L04_StackCfg.Instr.stackDepthAfter?,
                  StackInstr.stackDepthAfter?]

theorem toStackCfg?_pseudoFree
    {instr : StackInstr} {cfg : List L04_StackCfg.Instr}
    (hLower : instr.toStackCfg? = some cfg) :
    L04_StackCfg.InstrsPseudoFree cfg := by
  cases instr with
  | push value =>
      simp [toStackCfg?] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_singleton_push
        (L04_StackCfg.Atom.word (SharedSemantics.norm value))
  | dup depth =>
      simp [toStackCfg?] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_singleton_dup depth
  | swap index =>
      simp [toStackCfg?] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_singleton_swap index
  | pop =>
      simp [toStackCfg?] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_singleton_pop
  | unary op =>
      simp [toStackCfg?] at hLower
      rcases UnaryOp.toStackCfg?_complete op with ⟨cfgOp, hOp⟩
      simp [hOp] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_singleton_op cfgOp
  | binary op =>
      simp [toStackCfg?] at hLower
      rcases BinaryOp.toStackCfg?_complete op with ⟨cfgOp, hOp⟩
      simp [hOp] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_append
        (L04_StackCfg.InstrsPseudoFree_singleton_swap 0)
        (L04_StackCfg.InstrsPseudoFree_singleton_op cfgOp)

end StackInstr

namespace StackCode

def toStackCfg? : List StackInstr -> Option (List L04_StackCfg.Instr)
  | [] => some []
  | instr :: rest => do
      let cfgInstr ← instr.toStackCfg?
      let cfgRest ← toStackCfg? rest
      some (cfgInstr ++ cfgRest)

theorem toStackCfg?_correct
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    {stack out : Stack}
    (hLower : toStackCfg? code = some cfg)
    (hRun : run code stack = some out) :
    L04_StackCfg.execInstrs stack cfg = some out := by
  induction code generalizing stack cfg out with
  | nil =>
      simp [toStackCfg?] at hLower
      cases hLower
      simpa [run, L04_StackCfg.execInstrs] using hRun
  | cons instr rest ih =>
      simp [toStackCfg?, run] at hLower hRun
      cases hInstrCfg : instr.toStackCfg? with
      | none =>
          simp [hInstrCfg] at hLower
      | some cfgInstr =>
          simp [hInstrCfg] at hLower
          cases hRestCfg : toStackCfg? rest with
          | none =>
              simp [hRestCfg] at hLower
          | some cfgRest =>
              simp [hRestCfg] at hLower
              cases hInstrExec : instr.exec stack with
              | none =>
                  simp [hInstrExec] at hRun
              | some stack' =>
                  simp [hInstrExec] at hRun
                  cases hLower
                  rw [L04_StackCfg.execInstrs_append]
                  simp [StackInstr.toStackCfg?_correct hInstrCfg
                    hInstrExec]
                  exact ih hRestCfg hRun

theorem toStackCfg?_stackDepth
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    {depth : Nat}
    (hLower : toStackCfg? code = some cfg) :
    L04_StackCfg.stackDepthAfter? depth cfg =
      stackDepthAfter? depth code := by
  induction code generalizing cfg depth with
  | nil =>
      simp [toStackCfg?] at hLower
      cases hLower
      simp [stackDepthAfter?, L04_StackCfg.stackDepthAfter?]
  | cons instr rest ih =>
      simp [toStackCfg?] at hLower
      cases hInstrCfg : instr.toStackCfg? with
      | none =>
          simp [hInstrCfg] at hLower
      | some cfgInstr =>
          simp [hInstrCfg] at hLower
          cases hRestCfg : toStackCfg? rest with
          | none =>
              simp [hRestCfg] at hLower
          | some cfgRest =>
              simp [hRestCfg] at hLower
              cases hLower
              rw [L04_StackCfg.stackDepthAfter?_append]
              rw [StackInstr.toStackCfg?_stackDepth hInstrCfg]
              simp [StackCode.stackDepthAfter?]
              cases StackInstr.stackDepthAfter? depth instr <;>
                simp [ih hRestCfg]

theorem toStackCfg?_pseudoFree
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    (hLower : toStackCfg? code = some cfg) :
    L04_StackCfg.InstrsPseudoFree cfg := by
  induction code generalizing cfg with
  | nil =>
      simp [toStackCfg?] at hLower
      cases hLower
      exact L04_StackCfg.InstrsPseudoFree_nil
  | cons instr rest ih =>
      simp [toStackCfg?] at hLower
      cases hInstrCfg : instr.toStackCfg? with
      | none =>
          simp [hInstrCfg] at hLower
      | some cfgInstr =>
          simp [hInstrCfg] at hLower
          cases hRestCfg : toStackCfg? rest with
          | none =>
              simp [hRestCfg] at hLower
          | some cfgRest =>
              simp [hRestCfg] at hLower
              cases hLower
              exact L04_StackCfg.InstrsPseudoFree_append
                (StackInstr.toStackCfg?_pseudoFree hInstrCfg)
                (ih hRestCfg)

end StackCode

def compileExprAt (extraDepth : Nat) (layout : Layout) :
    Expr -> Option (List StackInstr)
  | Expr.word value =>
      some [StackInstr.push value]
  | Expr.var name => do
      let depth ← Layout.indexOf? layout name
      some [StackInstr.dup (extraDepth + depth)]
  | Expr.unary op expr => do
      let code ← compileExprAt extraDepth layout expr
      some (code ++ [StackInstr.unary op])
  | Expr.binary op lhs rhs => do
      let rhsCode ← compileExprAt extraDepth layout rhs
      let lhsCode ← compileExprAt (extraDepth + 1) layout lhs
      some (rhsCode ++ (lhsCode ++ [StackInstr.binary op]))

def compileExpr (layout : Layout) (expr : Expr) :
    Option (List StackInstr) :=
  compileExprAt 0 layout expr

namespace StackInstr

theorem toStackCfg?_complete (instr : StackInstr) :
    ∃ cfg, instr.toStackCfg? = some cfg := by
  cases instr with
  | push value =>
      simp [toStackCfg?]
  | dup depth =>
      simp [toStackCfg?]
  | swap index =>
      simp [toStackCfg?]
  | pop =>
      simp [toStackCfg?]
  | unary op =>
      rcases UnaryOp.toStackCfg?_complete op with ⟨cfgOp, hOp⟩
      exact ⟨[L04_StackCfg.Instr.op cfgOp], by
        simp [toStackCfg?, hOp]⟩
  | binary op =>
      rcases BinaryOp.toStackCfg?_complete op with ⟨cfgOp, hOp⟩
      exact ⟨[L04_StackCfg.Instr.swap 0, L04_StackCfg.Instr.op cfgOp], by
        simp [toStackCfg?, hOp]⟩

end StackInstr

namespace StackCode

theorem toStackCfg?_complete :
    ∀ code : List StackInstr, ∃ cfg, toStackCfg? code = some cfg
  | [] => ⟨[], rfl⟩
  | instr :: rest =>
      let ⟨cfgInstr, hInstr⟩ := StackInstr.toStackCfg?_complete instr
      let ⟨cfgRest, hRest⟩ := toStackCfg?_complete rest
      ⟨cfgInstr ++ cfgRest, by
        simp [toStackCfg?, hInstr, hRest]⟩

end StackCode

theorem compileExprAt_complete_of_accepted :
    ∀ {expr : Expr} {extraDepth : Nat} {layout : Layout},
      expr.acceptedWithLayout? layout = true ->
      ∃ code, compileExprAt extraDepth layout expr = some code := by
  intro expr
  induction expr with
  | word value =>
      intro extraDepth layout _hAccepted
      exact ⟨[StackInstr.push value], rfl⟩
  | var name =>
      intro extraDepth layout hAccepted
      simp [Expr.acceptedWithLayout?] at hAccepted
      cases hIndex : Layout.indexOf? layout name with
      | none =>
          simp [hIndex] at hAccepted
      | some depth =>
          exact ⟨[StackInstr.dup (extraDepth + depth)], by
            simp [compileExprAt, hIndex]⟩
  | unary op expr ih =>
      intro extraDepth layout hAccepted
      simp [Expr.acceptedWithLayout?] at hAccepted
      rcases ih (extraDepth := extraDepth) hAccepted with ⟨code, hCode⟩
      exact ⟨code ++ [StackInstr.unary op], by
        simp [compileExprAt, hCode]⟩
  | binary op lhs rhs lhsIH rhsIH =>
      intro extraDepth layout hAccepted
      simp [Expr.acceptedWithLayout?] at hAccepted
      rcases hAccepted with ⟨hLhs, hRhs⟩
      rcases rhsIH (extraDepth := extraDepth) hRhs with
        ⟨rhsCode, hRhsCode⟩
      rcases lhsIH (extraDepth := extraDepth + 1) hLhs with
        ⟨lhsCode, hLhsCode⟩
      exact ⟨rhsCode ++ (lhsCode ++ [StackInstr.binary op]), by
        simp [compileExprAt, hRhsCode, hLhsCode]⟩

theorem compileExpr_complete_of_accepted
    {layout : Layout} {expr : Expr}
    (hAccepted : expr.acceptedWithLayout? layout = true) :
    ∃ code, compileExpr layout expr = some code := by
  exact compileExprAt_complete_of_accepted hAccepted

theorem compileExpr_toStackCfg?_complete_of_accepted
    {layout : Layout} {expr : Expr}
    (hAccepted : expr.acceptedWithLayout? layout = true) :
    ∃ code cfg,
      compileExpr layout expr = some code ∧
        StackCode.toStackCfg? code = some cfg := by
  rcases compileExpr_complete_of_accepted hAccepted with ⟨code, hCode⟩
  rcases StackCode.toStackCfg?_complete code with ⟨cfg, hCfg⟩
  exact ⟨code, cfg, hCode, hCfg⟩

def compileStmt (layout : Layout) : Stmt -> Option (List StackInstr)
  | Stmt.returnExpr expr =>
      compileExpr layout expr
  | Stmt.exprThen expr body => do
      let exprCode ← compileExpr layout expr
      let bodyCode ← compileStmt layout body
      some (exprCode ++ (StackInstr.pop :: bodyCode))
  | Stmt.block body =>
      compileStmt layout body
  | Stmt.letIn name rhs body => do
      if (Layout.indexOf? layout name).isSome then
        none
      else
        let rhsCode ← compileExpr layout rhs
        let bodyCode ← compileStmt (name :: layout) body
        some (rhsCode ++ (bodyCode ++ [StackInstr.swap 0, StackInstr.pop]))

theorem compileStmt_complete_of_accepted :
    ∀ {stmt : Stmt} {layout : Layout},
      stmt.acceptedWithLayout? layout = true ->
      ∃ code, compileStmt layout stmt = some code := by
  intro stmt
  induction stmt with
  | returnExpr expr =>
      intro layout hAccepted
      exact compileExpr_complete_of_accepted hAccepted
  | exprThen expr body bodyIH =>
      intro layout hAccepted
      simp [Stmt.acceptedWithLayout?] at hAccepted
      rcases hAccepted with ⟨hExprAccepted, hBodyAccepted⟩
      rcases compileExpr_complete_of_accepted hExprAccepted with
        ⟨exprCode, hExprCode⟩
      rcases bodyIH hBodyAccepted with ⟨bodyCode, hBodyCode⟩
      exact ⟨exprCode ++ (StackInstr.pop :: bodyCode), by
        simp [compileStmt, hExprCode, hBodyCode]⟩
  | block body bodyIH =>
      intro layout hAccepted
      exact bodyIH hAccepted
  | letIn name rhs body bodyIH =>
      intro layout hAccepted
      cases hFresh : Layout.indexOf? layout name with
      | some depth =>
          simp [Stmt.acceptedWithLayout?, hFresh] at hAccepted
      | none =>
          simp [Stmt.acceptedWithLayout?, hFresh] at hAccepted
          rcases hAccepted with ⟨hRhsAccepted, hBodyAccepted⟩
          rcases compileExpr_complete_of_accepted hRhsAccepted with
            ⟨rhsCode, hRhsCode⟩
          rcases bodyIH hBodyAccepted with ⟨bodyCode, hBodyCode⟩
          exact ⟨rhsCode ++ (bodyCode ++ [StackInstr.swap 0, StackInstr.pop]), by
            simp [compileStmt, hFresh, hRhsCode, hBodyCode]⟩

theorem compileStmt_toStackCfg?_complete_of_accepted
    {layout : Layout} {stmt : Stmt}
    (hAccepted : stmt.acceptedWithLayout? layout = true) :
    ∃ code cfg,
      compileStmt layout stmt = some code ∧
        StackCode.toStackCfg? code = some cfg := by
  rcases compileStmt_complete_of_accepted hAccepted with ⟨code, hCode⟩
  rcases StackCode.toStackCfg?_complete code with ⟨cfg, hCfg⟩
  exact ⟨code, cfg, hCode, hCfg⟩

def compileStmtToStackCfg? (layout : Layout) (stmt : Stmt) :
    Option L04_StackCfg.Program := do
  let code ← compileStmt layout stmt
  let cfgCode ← StackCode.toStackCfg? code
  some (L04_StackCfg.Program.returnCode cfgCode)

theorem compileStmtToStackCfg?_complete_of_accepted
    {layout : Layout} {stmt : Stmt}
    (hAccepted : stmt.acceptedWithLayout? layout = true) :
    ∃ program, compileStmtToStackCfg? layout stmt = some program := by
  rcases compileStmt_toStackCfg?_complete_of_accepted hAccepted with
    ⟨code, cfg, hCode, hCfg⟩
  exact ⟨L04_StackCfg.Program.returnCode cfg, by
    simp [compileStmtToStackCfg?, hCode, hCfg]⟩

def compileReturnExprToStackCfg? (layout : Layout) (expr : Expr) :
    Option L04_StackCfg.Program := do
  let code ← compileExpr layout expr
  let cfgCode ← StackCode.toStackCfg? code
  some (L04_StackCfg.Program.returnCode cfgCode)

theorem compileReturnExprToStackCfg?_complete_of_accepted
    {layout : Layout} {expr : Expr}
    (hAccepted : expr.acceptedWithLayout? layout = true) :
    ∃ program, compileReturnExprToStackCfg? layout expr = some program := by
  rcases compileExpr_toStackCfg?_complete_of_accepted hAccepted with
    ⟨code, cfg, hCode, hCfg⟩
  exact ⟨L04_StackCfg.Program.returnCode cfg, by
    simp [compileReturnExprToStackCfg?, hCode, hCfg]⟩

def RelEnvStackAt
    (extraDepth : Nat) (env : Env) (layout : Layout) (stack : Stack) : Prop :=
  ∀ name depth,
    Layout.indexOf? layout name = some depth ->
      Env.lookup? env name = stackAt stack (extraDepth + depth)

theorem RelEnvStackAt.cons_fresh
    {env : Env} {layout : Layout} {stack : Stack}
    {name : Name} {value : Word}
    (hRel : RelEnvStackAt 0 env layout stack)
    (hNorm : SharedSemantics.norm value = value)
    (_hFresh : Layout.indexOf? layout name = none) :
    RelEnvStackAt 0 ((name, value) :: env) (name :: layout)
      (value :: stack) := by
  intro query depth hIndex
  by_cases hName : name = query
  · subst query
    simp [Layout.indexOf?, Layout.indexOfAux?] at hIndex
    cases hIndex
    simp [Env.lookup?, hNorm, stackAt]
  · have hTail := Layout.indexOf?_cons_ne hName hIndex
    rcases hTail with ⟨oldDepth, hOldIndex, hDepth⟩
    have hLookup : Env.lookup? ((name, value) :: env) query =
        Env.lookup? env query := by
      simp [Env.lookup?, hName]
    rw [hLookup, hRel query oldDepth hOldIndex]
    subst depth
    simp [stackAt, Nat.add_comm]

theorem RelEnvStackAt.shift
    {extraDepth : Nat} {env : Env} {layout : Layout} {stack : Stack}
    (hRel : RelEnvStackAt extraDepth env layout stack)
    (temp : Word) :
    RelEnvStackAt (extraDepth + 1) env layout (temp :: stack) := by
  intro name depth hIndex
  rw [hRel name depth hIndex]
  have hDepth :
      extraDepth + 1 + depth = (extraDepth + depth) + 1 := by
    omega
  rw [hDepth]
  exact stackAt_cons_succ temp stack (extraDepth + depth)

theorem compileExprAt_correct :
    ∀ {expr : Expr} {extraDepth : Nat} {layout : Layout}
      {env : Env} {stack : Stack} {code : List StackInstr}
      {value : Word},
      compileExprAt extraDepth layout expr = some code ->
      expr.eval? env = some value ->
      RelEnvStackAt extraDepth env layout stack ->
      StackCode.run code stack = some (value :: stack) := by
  intro expr
  induction expr with
  | word literal =>
      intro extraDepth layout env stack code value hCompile hEval _hRel
      simp [compileExprAt, Expr.eval?] at hCompile hEval
      cases hCompile
      cases hEval
      simp [StackCode.run, StackInstr.exec]
  | var name =>
      intro extraDepth layout env stack code value hCompile hEval hRel
      simp [compileExprAt] at hCompile
      simp [Expr.eval?] at hEval
      cases hIndex : Layout.indexOf? layout name with
      | none =>
          simp [hIndex] at hCompile
      | some depth =>
          simp [hIndex] at hCompile
          cases hCompile
          have hStack := hRel name depth hIndex
          rw [hEval] at hStack
          simp [StackCode.run, StackInstr.exec]
          rw [← hStack]
          rfl
  | unary op expr ih =>
      intro extraDepth layout env stack code value hCompile hEval hRel
      simp [compileExprAt, Expr.eval?] at hCompile hEval
      cases hCode : compileExprAt extraDepth layout expr with
      | none =>
          simp [hCode] at hCompile
      | some exprCode =>
          simp [hCode] at hCompile
          cases hExprEval : Expr.eval? env expr with
          | none =>
              simp [hExprEval] at hEval
          | some exprValue =>
              simp [hExprEval] at hEval
              cases hCompile
              cases hEval
              rw [StackCode.run_append]
              simp [ih hCode hExprEval hRel, StackCode.run,
                StackInstr.exec]
  | binary op lhs rhs lhsIH rhsIH =>
      intro extraDepth layout env stack code value hCompile hEval hRel
      simp [compileExprAt, Expr.eval?] at hCompile hEval
      cases hRhsCode : compileExprAt extraDepth layout rhs with
      | none =>
          simp [hRhsCode] at hCompile
      | some rhsCode =>
          simp [hRhsCode] at hCompile
          cases hLhsCode :
              compileExprAt (extraDepth + 1) layout lhs with
          | none =>
              simp [hLhsCode] at hCompile
          | some lhsCode =>
              simp [hLhsCode] at hCompile
              cases hRhsEval : Expr.eval? env rhs with
              | none =>
                  simp [hRhsEval] at hEval
              | some rhsValue =>
                  simp [hRhsEval] at hEval
                  cases hLhsEval : Expr.eval? env lhs with
                  | none =>
                      simp [hLhsEval] at hEval
                  | some lhsValue =>
                      simp [hLhsEval] at hEval
                      cases hCompile
                      cases hEval
                      rw [StackCode.run_append]
                      simp [rhsIH hRhsCode hRhsEval hRel]
                      rw [StackCode.run_append]
                      have hShift :=
                        RelEnvStackAt.shift hRel rhsValue
                      simp [lhsIH hLhsCode hLhsEval hShift,
                        StackCode.run, StackInstr.exec]

theorem compileExpr_correct
    {layout : Layout} {env : Env} {stack : Stack} {expr : Expr}
    {code : List StackInstr} {value : Word}
    (hCompile : compileExpr layout expr = some code)
    (hEval : expr.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout stack) :
    StackCode.run code stack = some (value :: stack) := by
  exact compileExprAt_correct hCompile hEval hRel

theorem compileExprAt_stackDepth :
    ∀ {expr : Expr} {extraDepth : Nat} {layout : Layout}
      {code : List StackInstr},
      compileExprAt extraDepth layout expr = some code ->
      StackCode.stackDepthAfter? (extraDepth + layout.length) code =
        some (extraDepth + layout.length + 1) := by
  intro expr
  induction expr with
  | word literal =>
      intro extraDepth layout code hCompile
      simp [compileExprAt] at hCompile
      cases hCompile
      simp [StackCode.stackDepthAfter?, StackInstr.stackDepthAfter?]
  | var name =>
      intro extraDepth layout code hCompile
      simp [compileExprAt] at hCompile
      cases hIndex : Layout.indexOf? layout name with
      | none =>
          simp [hIndex] at hCompile
      | some depth =>
          simp [hIndex] at hCompile
          cases hCompile
          have hLt := Layout.indexOf?_lt_length hIndex
          simp [StackCode.stackDepthAfter?, StackInstr.stackDepthAfter?,
            hLt]
  | unary op expr ih =>
      intro extraDepth layout code hCompile
      simp [compileExprAt] at hCompile
      cases hCode : compileExprAt extraDepth layout expr with
      | none =>
          simp [hCode] at hCompile
      | some exprCode =>
          simp [hCode] at hCompile
          cases hCompile
          rw [StackCode.stackDepthAfter?_append]
          simp [ih hCode, StackCode.stackDepthAfter?,
            StackInstr.stackDepthAfter?]
  | binary op lhs rhs lhsIH rhsIH =>
      intro extraDepth layout code hCompile
      simp [compileExprAt] at hCompile
      cases hRhsCode : compileExprAt extraDepth layout rhs with
      | none =>
          simp [hRhsCode] at hCompile
      | some rhsCode =>
          simp [hRhsCode] at hCompile
          cases hLhsCode :
              compileExprAt (extraDepth + 1) layout lhs with
          | none =>
              simp [hLhsCode] at hCompile
          | some lhsCode =>
              simp [hLhsCode] at hCompile
              cases hCompile
              rw [StackCode.stackDepthAfter?_append]
              simp [rhsIH hRhsCode]
              rw [StackCode.stackDepthAfter?_append]
              have hLhsDepth := lhsIH hLhsCode
              have hDepthEq :
                  extraDepth + layout.length + 1 =
                    extraDepth + 1 + layout.length := by
                omega
              rw [hDepthEq]
              have hBinary :
                  StackInstr.stackDepthAfter?
                      (extraDepth + 1 + layout.length + 1)
                      (StackInstr.binary op) =
                    some (extraDepth + 1 + layout.length) := by
                have hEq :
                    extraDepth + 1 + layout.length + 1 =
                      (extraDepth + layout.length) + 2 := by
                  omega
                rw [hEq]
                simp [StackInstr.stackDepthAfter?]
                omega
              simp [hLhsDepth, StackCode.stackDepthAfter?, hBinary]

theorem compileExpr_stackDepth
    {layout : Layout} {expr : Expr} {code : List StackInstr}
    (hCompile : compileExpr layout expr = some code) :
    StackCode.stackDepthAfter? layout.length code =
      some (layout.length + 1) := by
  have hDepth :=
    compileExprAt_stackDepth
      (extraDepth := 0) (layout := layout) (expr := expr)
      hCompile
  simpa using hDepth

theorem compileExpr_toStackCfg_correct
    {layout : Layout} {env : Env} {stack : Stack} {expr : Expr}
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    {value : Word}
    (hCompile : compileExpr layout expr = some code)
    (hLower : StackCode.toStackCfg? code = some cfg)
    (hEval : expr.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout stack) :
    L04_StackCfg.execInstrs stack cfg = some (value :: stack) := by
  exact StackCode.toStackCfg?_correct hLower
    (compileExpr_correct hCompile hEval hRel)

theorem compileStmt_correct :
    ∀ {stmt : Stmt} {layout : Layout} {env : Env}
      {stack : Stack} {code : List StackInstr} {value : Word},
      compileStmt layout stmt = some code ->
      stmt.eval? env = some value ->
      RelEnvStackAt 0 env layout stack ->
      StackCode.run code stack = some (value :: stack) := by
  intro stmt
  induction stmt with
  | returnExpr expr =>
      intro layout env stack code value hCompile hEval hRel
      exact compileExpr_correct hCompile hEval hRel
  | exprThen expr body bodyIH =>
      intro layout env stack code value hCompile hEval hRel
      simp [compileStmt, Stmt.eval?] at hCompile hEval
      cases hExprCode : compileExpr layout expr with
      | none =>
          simp [hExprCode] at hCompile
      | some exprCode =>
          simp [hExprCode] at hCompile
          cases hBodyCode : compileStmt layout body with
          | none =>
              simp [hBodyCode] at hCompile
          | some bodyCode =>
              simp [hBodyCode] at hCompile
              cases hExprEval : expr.eval? env with
              | none =>
                  simp [hExprEval] at hEval
              | some exprValue =>
                  simp [hExprEval] at hEval
                  cases hCompile
                  rw [StackCode.run_append]
                  have hExprRun :=
                    compileExpr_correct hExprCode hExprEval hRel
                  simp [hExprRun, StackCode.run, StackInstr.exec]
                  exact bodyIH hBodyCode hEval hRel
  | block body bodyIH =>
      intro layout env stack code value hCompile hEval hRel
      exact bodyIH hCompile hEval hRel
  | letIn name rhs body bodyIH =>
      intro layout env stack code value hCompile hEval hRel
      simp [compileStmt, Stmt.eval?] at hCompile hEval
      cases hFresh : Layout.indexOf? layout name with
      | some depth =>
          simp [hFresh] at hCompile
      | none =>
          simp [hFresh] at hCompile
          cases hRhsCode : compileExpr layout rhs with
          | none =>
              simp [hRhsCode] at hCompile
          | some rhsCode =>
              simp [hRhsCode] at hCompile
              cases hBodyCode : compileStmt (name :: layout) body with
              | none =>
                  simp [hBodyCode] at hCompile
              | some bodyCode =>
                  simp [hBodyCode] at hCompile
                  cases hRhsEval : rhs.eval? env with
                  | none =>
                      simp [hRhsEval] at hEval
                  | some rhsValue =>
                      simp [hRhsEval] at hEval
                      cases hCompile
                      rw [StackCode.run_append]
                      have hRhsRun :=
                        compileExpr_correct hRhsCode hRhsEval hRel
                      simp [hRhsRun]
                      have hNorm :=
                        Expr.eval?_normalized hRhsEval
                      have hBodyRel :=
                        RelEnvStackAt.cons_fresh hRel hNorm hFresh
                      rw [StackCode.run_append]
                      simp [bodyIH hBodyCode hEval hBodyRel,
                        StackCode.run, StackInstr.exec,
                        L04_StackCfg.replaceAt?]

theorem compileStmt_stackDepth :
    ∀ {stmt : Stmt} {layout : Layout} {code : List StackInstr},
      compileStmt layout stmt = some code ->
      StackCode.stackDepthAfter? layout.length code =
        some (layout.length + 1) := by
  intro stmt
  induction stmt with
  | returnExpr expr =>
      intro layout code hCompile
      exact compileExpr_stackDepth hCompile
  | exprThen expr body bodyIH =>
      intro layout code hCompile
      simp [compileStmt] at hCompile
      cases hExprCode : compileExpr layout expr with
      | none =>
          simp [hExprCode] at hCompile
      | some exprCode =>
          simp [hExprCode] at hCompile
          cases hBodyCode : compileStmt layout body with
          | none =>
              simp [hBodyCode] at hCompile
          | some bodyCode =>
              simp [hBodyCode] at hCompile
              cases hCompile
              rw [StackCode.stackDepthAfter?_append]
              simp [compileExpr_stackDepth hExprCode,
                StackCode.stackDepthAfter?, StackInstr.stackDepthAfter?]
              exact bodyIH hBodyCode
  | block body bodyIH =>
      intro layout code hCompile
      exact bodyIH hCompile
  | letIn name rhs body bodyIH =>
      intro layout code hCompile
      simp [compileStmt] at hCompile
      cases hFresh : Layout.indexOf? layout name with
      | some depth =>
          simp [hFresh] at hCompile
      | none =>
          simp [hFresh] at hCompile
          cases hRhsCode : compileExpr layout rhs with
          | none =>
              simp [hRhsCode] at hCompile
          | some rhsCode =>
              simp [hRhsCode] at hCompile
              cases hBodyCode : compileStmt (name :: layout) body with
              | none =>
                  simp [hBodyCode] at hCompile
              | some bodyCode =>
                  simp [hBodyCode] at hCompile
                  cases hCompile
                  rw [StackCode.stackDepthAfter?_append]
                  simp [compileExpr_stackDepth hRhsCode]
                  rw [StackCode.stackDepthAfter?_append]
                  have hBodyDepth := bodyIH hBodyCode
                  simp at hBodyDepth
                  simp [hBodyDepth, StackCode.stackDepthAfter?,
                    StackInstr.stackDepthAfter?]

theorem compileStmt_toStackCfg_correct
    {layout : Layout} {env : Env} {stack : Stack} {stmt : Stmt}
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    {value : Word}
    (hCompile : compileStmt layout stmt = some code)
    (hLower : StackCode.toStackCfg? code = some cfg)
    (hEval : stmt.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout stack) :
    L04_StackCfg.execInstrs stack cfg = some (value :: stack) := by
  exact StackCode.toStackCfg?_correct hLower
    (compileStmt_correct hCompile hEval hRel)

theorem compileStmt_toStackCfg_stackDepth
    {layout : Layout} {stmt : Stmt}
    {code : List StackInstr} {cfg : List L04_StackCfg.Instr}
    (hCompile : compileStmt layout stmt = some code)
    (hLower : StackCode.toStackCfg? code = some cfg) :
    L04_StackCfg.stackDepthAfter? layout.length cfg =
      some (layout.length + 1) := by
  rw [StackCode.toStackCfg?_stackDepth hLower]
  exact compileStmt_stackDepth hCompile

theorem compileReturnExprToStackCfg?_semantics
    {layout : Layout} {env : Env} {expr : Expr}
    {program : L04_StackCfg.Program} {value : Word}
    (hCompile :
      compileReturnExprToStackCfg? layout expr = some program)
    (hEval : expr.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout []) :
    L04_StackCfg.Semantics program
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  unfold compileReturnExprToStackCfg? at hCompile
  cases hExprCode : compileExpr layout expr with
  | none =>
      simp [hExprCode] at hCompile
  | some code =>
      simp [hExprCode] at hCompile
      cases hCfgCode : StackCode.toStackCfg? code with
      | none =>
          simp [hCfgCode] at hCompile
      | some cfgCode =>
          simp [hCfgCode] at hCompile
          cases hCompile
          exact L04_StackCfg.Program.returnCode_semantics
            (compileExpr_toStackCfg_correct hExprCode hCfgCode hEval hRel)

theorem compileStmtToStackCfg?_semantics
    {layout : Layout} {env : Env} {stmt : Stmt}
    {program : L04_StackCfg.Program} {value : Word}
    (hCompile :
      compileStmtToStackCfg? layout stmt = some program)
    (hEval : stmt.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout []) :
    L04_StackCfg.Semantics program
      (L01_ValidSolidity.Behavior.returnedWord value) := by
  unfold compileStmtToStackCfg? at hCompile
  cases hStmtCode : compileStmt layout stmt with
  | none =>
      simp [hStmtCode] at hCompile
  | some code =>
      simp [hStmtCode] at hCompile
      cases hCfgCode : StackCode.toStackCfg? code with
      | none =>
          simp [hCfgCode] at hCompile
      | some cfgCode =>
          simp [hCfgCode] at hCompile
          cases hCompile
          exact L04_StackCfg.Program.returnCode_semantics
            (compileStmt_toStackCfg_correct hStmtCode hCfgCode hEval hRel)

theorem compileStmtToStackCfg?_wf_top
    {stmt : Stmt} {program : L04_StackCfg.Program}
    (hCompile : compileStmtToStackCfg? [] stmt = some program) :
    L04_StackCfg.WF program := by
  unfold compileStmtToStackCfg? at hCompile
  cases hStmtCode : compileStmt [] stmt with
  | none =>
      simp [hStmtCode] at hCompile
  | some code =>
      simp [hStmtCode] at hCompile
      cases hCfgCode : StackCode.toStackCfg? code with
      | none =>
          simp [hCfgCode] at hCompile
      | some cfgCode =>
          simp [hCfgCode] at hCompile
          cases hCompile
          exact L04_StackCfg.Program.returnCode_wf
            (StackCode.toStackCfg?_pseudoFree hCfgCode)
            (by
              have hDepth :=
                compileStmt_toStackCfg_stackDepth hStmtCode hCfgCode
              simpa using hDepth)

theorem acceptedStmtToStackCfg_correct
    {layout : Layout} {env : Env} {stmt : Stmt} {value : Word}
    (hAccepted : stmt.acceptedWithLayout? layout = true)
    (hEval : stmt.eval? env = some value)
    (hRel : RelEnvStackAt 0 env layout []) :
    ∃ program,
      compileStmtToStackCfg? layout stmt = some program ∧
        (layout = [] -> L04_StackCfg.WF program) ∧
        L04_StackCfg.Semantics program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  rcases compileStmtToStackCfg?_complete_of_accepted hAccepted with
    ⟨program, hCompile⟩
  exact ⟨program, hCompile,
    (by
      intro hLayout
      subst layout
      exact compileStmtToStackCfg?_wf_top hCompile),
    compileStmtToStackCfg?_semantics hCompile hEval hRel⟩

theorem acceptedTopStmtToStackCfg_correct
    {stmt : Stmt} {value : Word}
    (hAccepted : stmt.acceptedWithLayout? [] = true)
    (hEval : stmt.eval? [] = some value) :
    ∃ program,
      compileStmtToStackCfg? [] stmt = some program ∧
        L04_StackCfg.WF program ∧
        L04_StackCfg.Semantics program
          (L01_ValidSolidity.Behavior.returnedWord value) := by
  have hRel : RelEnvStackAt 0 [] [] [] := by
    intro name depth hIndex
    simp [Layout.indexOf?, Layout.indexOfAux?] at hIndex
  rcases acceptedStmtToStackCfg_correct hAccepted hEval hRel with
    ⟨program, hCompile, hWF, hSemantics⟩
  exact ⟨program, hCompile, hWF rfl, hSemantics⟩

theorem acceptedTopStmtToL06_byte_correct
    {stmt : Stmt} {value : Word}
    (hAccepted : stmt.acceptedWithLayout? [] = true)
    (hEval : stmt.eval? [] = some value)
    (hByte : value < 256) :
    ∃ (cfgProgram : L04_StackCfg.Program)
      (bytecodeArtifact : Passes.P05_StackCfgToBytecode.Artifact)
      (evmArtifact : Passes.P06_BytecodeToEvm.Artifact),
      compileStmtToStackCfg? [] stmt = some cfgProgram ∧
      Passes.P05_StackCfgToBytecode.assemble? cfgProgram =
          some bytecodeArtifact ∧
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
          some evmArtifact ∧
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) := by
  have hRel : RelEnvStackAt 0 [] [] [] := by
    intro name depth hIndex
    simp [Layout.indexOf?, Layout.indexOfAux?] at hIndex
  rcases compileStmt_complete_of_accepted hAccepted with
    ⟨stackCode, hStackCode⟩
  rcases StackCode.toStackCfg?_complete stackCode with
    ⟨cfgCode, hCfgCode⟩
  let cfgProgram := L04_StackCfg.Program.returnCode cfgCode
  have hCompile :
      compileStmtToStackCfg? [] stmt = some cfgProgram := by
    simp [cfgProgram, compileStmtToStackCfg?, hStackCode, hCfgCode]
  have hExec :
      L04_StackCfg.execInstrs [] cfgCode = some [value] :=
    compileStmt_toStackCfg_correct hStackCode hCfgCode hEval hRel
  have hReturn : cfgProgram.IsReturnCode cfgCode := by
    simp [cfgProgram, L04_StackCfg.Program.returnCode_isReturnCode]
  rcases (Passes.P05_StackCfgToBytecode.assemble?_complete_for_returnCodeByte
      hReturn hExec hByte) with
    ⟨bytecodeArtifact, hAssemble⟩
  let evmArtifact : Passes.P06_BytecodeToEvm.Artifact :=
    { program := L06_Evm.Program.ofBytecode bytecodeArtifact.bytecode
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := by exact {} } }
  have hEmbed :
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
        some evmArtifact := by
    rfl
  have hL04 :
      L04_StackCfg.Semantics cfgProgram
        (L01_ValidSolidity.Behavior.returnedWord value) :=
    compileStmtToStackCfg?_semantics hCompile hEval hRel
  have hL05 :
      L05_Bytecode.Semantics bytecodeArtifact.bytecode
        (L01_ValidSolidity.Behavior.returnedWord value) :=
    (Passes.P05_StackCfgToBytecode.assemble?_sound
      hAssemble).preservesBehavior hL04
  have hL06 :
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) :=
    (Passes.P06_BytecodeToEvm.embed?_sound
      hEmbed).preservesBehavior hL05
  exact ⟨cfgProgram, bytecodeArtifact, evmArtifact,
    hCompile, hAssemble, hEmbed, hL06⟩

theorem acceptedTopByteStmtToL06_correct
    {stmt : Stmt}
    (hAccepted : stmt.acceptedTopByte? = true) :
    ∃ (value : Word)
      (cfgProgram : L04_StackCfg.Program)
      (bytecodeArtifact : Passes.P05_StackCfgToBytecode.Artifact)
      (evmArtifact : Passes.P06_BytecodeToEvm.Artifact),
      stmt.eval? [] = some value ∧
      compileStmtToStackCfg? [] stmt = some cfgProgram ∧
      Passes.P05_StackCfgToBytecode.assemble? cfgProgram =
          some bytecodeArtifact ∧
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
          some evmArtifact ∧
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) := by
  unfold Stmt.acceptedTopByte? at hAccepted
  cases hEvalByte : Stmt.evalByte? stmt with
  | none =>
      simp [hEvalByte] at hAccepted
  | some value =>
      simp [hEvalByte] at hAccepted
      rcases Stmt.evalByte?_eq_some hEvalByte with ⟨hEval, hByte⟩
      rcases acceptedTopStmtToL06_byte_correct
          hAccepted hEval hByte with
        ⟨cfgProgram, bytecodeArtifact, evmArtifact,
          hCompile, hAssemble, hEmbed, hL06⟩
      exact ⟨value, cfgProgram, bytecodeArtifact, evmArtifact,
        hEval, hCompile, hAssemble, hEmbed, hL06⟩

def returnWord0Expr : Expr :=
  Expr.word 0

theorem returnWord0Expr_to_l06_semantics :
    ∃ (cfgProgram : L04_StackCfg.Program)
      (bytecodeArtifact : Passes.P05_StackCfgToBytecode.Artifact)
      (evmArtifact : Passes.P06_BytecodeToEvm.Artifact),
      compileReturnExprToStackCfg? [] returnWord0Expr =
          some cfgProgram ∧
      Passes.P05_StackCfgToBytecode.assemble? cfgProgram =
          some bytecodeArtifact ∧
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
          some evmArtifact ∧
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord 0)) := by
  let cfgProgram := L04_StackCfg.Program.returnWord0
  let bytecodeArtifact : Passes.P05_StackCfgToBytecode.Artifact :=
    { bytecode := L05_Bytecode.Artifact.returnWord0
      wf := L05_Bytecode.Artifact.returnWord0_wf }
  let evmArtifact : Passes.P06_BytecodeToEvm.Artifact :=
    { program := L06_Evm.Program.ofBytecode
        L05_Bytecode.Artifact.returnWord0
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := L05_Bytecode.Artifact.returnWord0_wf } }
  refine ⟨cfgProgram, bytecodeArtifact, evmArtifact, ?_, ?_, ?_, ?_⟩
  · simp [cfgProgram, returnWord0Expr, compileReturnExprToStackCfg?,
      compileExpr, compileExprAt, StackCode.toStackCfg?,
      StackInstr.toStackCfg?, L04_StackCfg.Program.returnWord0,
      L04_StackCfg.Program.returnWord, SharedSemantics.norm,
      SharedSemantics.wordModulus]
  · have hNotStop :
        L04_StackCfg.Program.returnWord0 ≠ L04_StackCfg.Program.stop := by
      intro h
      cases h
    simp [cfgProgram, bytecodeArtifact,
      Passes.P05_StackCfgToBytecode.assemble?, hNotStop]
  · simp [evmArtifact, bytecodeArtifact,
      Passes.P06_BytecodeToEvm.embed?]
  · exact L06_Evm.Program.ofBytecode_returnWord0_semantics
      L05_Bytecode.Artifact.returnWord0_isReturnWord0

def returnByteExpr (value : Word) : Expr :=
  Expr.word value

theorem returnByteExpr_to_l06_semantics
    (value : Word) (hByte : value < 256) :
    ∃ (cfgProgram : L04_StackCfg.Program)
      (bytecodeArtifact : Passes.P05_StackCfgToBytecode.Artifact)
      (evmArtifact : Passes.P06_BytecodeToEvm.Artifact),
      compileReturnExprToStackCfg? [] (returnByteExpr value) =
          some cfgProgram ∧
      Passes.P05_StackCfgToBytecode.assemble? cfgProgram =
          some bytecodeArtifact ∧
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
          some evmArtifact ∧
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) := by
  let cfgProgram := L04_StackCfg.Program.returnWord value
  have hNorm := norm_eq_of_lt_byte hByte
  have hCompile :
      compileReturnExprToStackCfg? [] (returnByteExpr value) =
        some cfgProgram := by
    simp [cfgProgram, returnByteExpr, compileReturnExprToStackCfg?,
      compileExpr, compileExprAt, StackCode.toStackCfg?,
      StackInstr.toStackCfg?, L04_StackCfg.Program.returnWord,
      L04_StackCfg.Program.returnCode, hNorm]
  have hReturn : cfgProgram.IsReturnWord value := by
    simp [cfgProgram, L04_StackCfg.Program.returnWord_isReturnWord]
  rcases (Passes.P05_StackCfgToBytecode.assemble?_complete_for_returnByte
      hReturn hByte) with
    ⟨bytecodeArtifact, hAssemble⟩
  let evmArtifact : Passes.P06_BytecodeToEvm.Artifact :=
    { program := L06_Evm.Program.ofBytecode bytecodeArtifact.bytecode
      external := SharedSemantics.External.EvmExternal.empty
      wf := { bytecodeWF := by exact {} } }
  have hEmbed :
      Passes.P06_BytecodeToEvm.embed? bytecodeArtifact.bytecode =
        some evmArtifact := by
    rfl
  have hL04 :
      L04_StackCfg.Semantics cfgProgram
        (L01_ValidSolidity.Behavior.returnedWord value) := by
    exact L04_StackCfg.Program.returnWord_semantics value
  have hL05 :
      L05_Bytecode.Semantics bytecodeArtifact.bytecode
        (L01_ValidSolidity.Behavior.returnedWord value) :=
    (Passes.P05_StackCfgToBytecode.assemble?_sound
      hAssemble).preservesBehavior hL04
  have hL06 :
      L06_Evm.SemanticsWithExternal evmArtifact.external
        evmArtifact.program
        (L06_Evm.Outcome.pure
          (L01_ValidSolidity.Behavior.returnedWord value)) :=
    (Passes.P06_BytecodeToEvm.embed?_sound
      hEmbed).preservesBehavior hL05
  exact ⟨cfgProgram, bytecodeArtifact, evmArtifact,
    hCompile, hAssemble, hEmbed, hL06⟩

end YulEvm
end Spine
end SolidCore

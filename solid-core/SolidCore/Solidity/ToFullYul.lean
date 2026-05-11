import SolidCore.Compiler
import SolidCore.MVP
import SolidCore.Solidity.Interpreter

set_option linter.unusedSimpArgs false

namespace SolidCore
namespace Solidity
namespace Source

abbrev LegacyExpr := SolidCore.Solidity.Expr
abbrev MVPCoreStmt := SolidCore.Solidity.MVP.Stmt
abbrev MVPCoreProgram := SolidCore.Solidity.MVP.SourceProgram
abbrev MVPStateExpr := SolidCore.Solidity.MVP.StateExpr
abbrev YulExpr := SolidCoreYulCore.FullYul.Expr
abbrev YulStmt := SolidCoreYulCore.FullYul.Stmt

def uncheckedContext : Context :=
  { Context.empty with checked := false }

def emptyRuntime : Runtime :=
  Runtime.ofState State.empty

private theorem addWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.addWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.addWord lhs rhs := by
  unfold SolidCoreYulCore.addWord SolidCoreYulCore.norm
  rw [← Nat.add_mod lhs rhs SolidCoreYulCore.wordModulus]

private theorem norm_norm (value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.norm value := by
  unfold SolidCoreYulCore.norm
  exact Nat.mod_mod value SolidCoreYulCore.wordModulus

private theorem norm_zero : SolidCoreYulCore.norm 0 = 0 := rfl

private theorem norm_one : SolidCoreYulCore.norm 1 = 1 := by
  decide

private theorem notWord_norm_arg (value : Word) :
    SolidCoreYulCore.notWord (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.notWord value := by
  unfold SolidCoreYulCore.notWord
  simp [norm_norm]

private theorem iszeroWord_norm_arg (value : Word) :
    SolidCoreYulCore.iszeroWord (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.iszeroWord value := by
  unfold SolidCoreYulCore.iszeroWord
  simp [norm_norm]

private theorem boolWord_not_truthy_eq_iszeroWord (value : Word) :
    boolWord (!(wordTruthy value)) = SolidCoreYulCore.iszeroWord value := by
  unfold boolWord wordTruthy SolidCoreYulCore.iszeroWord
  by_cases h : SolidCoreYulCore.norm value = 0 <;> simp [h]

private theorem boolWord_not_wordEq_eq_iszero_eqWord (lhs rhs : Word) :
    boolWord (!(wordEq lhs rhs)) =
      SolidCoreYulCore.iszeroWord (SolidCoreYulCore.eqWord lhs rhs) := by
  have hNormOne : SolidCoreYulCore.norm 1 ≠ 0 := by decide
  have hNormZero : SolidCoreYulCore.norm 0 = 0 := by rfl
  unfold boolWord wordEq SolidCoreYulCore.eqWord SolidCoreYulCore.iszeroWord
  by_cases h : SolidCoreYulCore.norm lhs = SolidCoreYulCore.norm rhs <;>
    simp [h, hNormOne, hNormZero]

private theorem boolWord_and_truthy_eq_legacy_boolAnd (lhs rhs : Word) :
    boolWord (wordTruthy lhs && wordTruthy rhs) =
      SolidCoreYulCore.iszeroWord
        (SolidCoreYulCore.orWord
          (SolidCoreYulCore.iszeroWord lhs)
          (SolidCoreYulCore.iszeroWord rhs)) := by
  unfold boolWord wordTruthy SolidCoreYulCore.iszeroWord
  by_cases hL : SolidCoreYulCore.norm lhs = 0 <;>
  by_cases hR : SolidCoreYulCore.norm rhs = 0 <;>
  simp [hL, hR]
  all_goals decide

private theorem boolWord_or_truthy_eq_legacy_boolOr (lhs rhs : Word) :
    boolWord (wordTruthy lhs || wordTruthy rhs) =
      SolidCoreYulCore.iszeroWord
        (SolidCoreYulCore.andWord
          (SolidCoreYulCore.iszeroWord lhs)
          (SolidCoreYulCore.iszeroWord rhs)) := by
  unfold boolWord wordTruthy SolidCoreYulCore.iszeroWord
  by_cases hL : SolidCoreYulCore.norm lhs = 0 <;>
  by_cases hR : SolidCoreYulCore.norm rhs = 0 <;>
  simp [hL, hR]
  all_goals decide

private theorem subWord_zero_norm_arg (value : Word) :
    SolidCoreYulCore.subWord 0 (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.subWord 0 value := by
  unfold SolidCoreYulCore.subWord
  simp [norm_norm]

private theorem subWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.subWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.subWord lhs rhs := by
  unfold SolidCoreYulCore.subWord
  simp [norm_norm]

private theorem mulWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.mulWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.mulWord lhs rhs := by
  unfold SolidCoreYulCore.mulWord SolidCoreYulCore.norm
  rw [← Nat.mul_mod lhs rhs SolidCoreYulCore.wordModulus]

private theorem andWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.andWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.andWord lhs rhs := by
  unfold SolidCoreYulCore.andWord
  simp [norm_norm]

private theorem orWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.orWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.orWord lhs rhs := by
  unfold SolidCoreYulCore.orWord
  simp [norm_norm]

private theorem xorWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.xorWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.xorWord lhs rhs := by
  unfold SolidCoreYulCore.xorWord
  simp [norm_norm]

private theorem shlWord_norm_args (shift value : Word) :
    SolidCoreYulCore.shlWord (SolidCoreYulCore.norm shift)
        (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.shlWord shift value := by
  unfold SolidCoreYulCore.shlWord
  simp [norm_norm]

private theorem shrWord_norm_args (shift value : Word) :
    SolidCoreYulCore.shrWord (SolidCoreYulCore.norm shift)
        (SolidCoreYulCore.norm value) =
      SolidCoreYulCore.shrWord shift value := by
  unfold SolidCoreYulCore.shrWord
  simp [norm_norm]

private theorem ltWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.ltWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.ltWord lhs rhs := by
  unfold SolidCoreYulCore.ltWord
  simp [norm_norm]

private theorem gtWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.gtWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.gtWord lhs rhs := by
  unfold SolidCoreYulCore.gtWord
  simp [norm_norm]

private theorem eqWord_norm_args (lhs rhs : Word) :
    SolidCoreYulCore.eqWord (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      SolidCoreYulCore.eqWord lhs rhs := by
  unfold SolidCoreYulCore.eqWord
  simp [norm_norm]

private theorem addWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.addWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.addWord lhs rhs) := by
  unfold SolidCoreYulCore.addWord
  simp [norm_norm]

private theorem subWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.subWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.subWord lhs rhs) := by
  unfold SolidCoreYulCore.subWord
  simp [norm_norm]

private theorem mulWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.mulWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.mulWord lhs rhs) := by
  unfold SolidCoreYulCore.mulWord
  simp [norm_norm]

private theorem andWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.andWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.andWord lhs rhs) := by
  unfold SolidCoreYulCore.andWord
  simp [norm_norm]

private theorem orWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.orWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.orWord lhs rhs) := by
  unfold SolidCoreYulCore.orWord
  simp [norm_norm]

private theorem xorWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.xorWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.xorWord lhs rhs) := by
  unfold SolidCoreYulCore.xorWord
  simp [norm_norm]

private theorem ltWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.ltWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.ltWord lhs rhs) := by
  unfold SolidCoreYulCore.ltWord
  by_cases h : SolidCoreYulCore.norm lhs < SolidCoreYulCore.norm rhs
  · simp [h, norm_one]
  · simp [h, norm_zero]

private theorem gtWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.gtWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.gtWord lhs rhs) := by
  unfold SolidCoreYulCore.gtWord
  by_cases h : SolidCoreYulCore.norm rhs < SolidCoreYulCore.norm lhs
  · simp [h, norm_one]
  · simp [h, norm_zero]

private theorem eqWord_norm_result (lhs rhs : Word) :
    SolidCoreYulCore.eqWord lhs rhs =
      SolidCoreYulCore.norm (SolidCoreYulCore.eqWord lhs rhs) := by
  unfold SolidCoreYulCore.eqWord
  by_cases h : SolidCoreYulCore.norm lhs = SolidCoreYulCore.norm rhs
  · simp [h, norm_one]
  · simp [h, norm_zero]

private theorem norm_notWord_result (value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.notWord value) =
      SolidCoreYulCore.notWord value := by
  unfold SolidCoreYulCore.notWord
  simp [norm_norm]

private theorem norm_iszeroWord_result (value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.iszeroWord value) =
      SolidCoreYulCore.iszeroWord value := by
  unfold SolidCoreYulCore.iszeroWord
  by_cases h : SolidCoreYulCore.norm value = 0
  · simp [h, norm_one]
  · simp [h, norm_zero]

private theorem norm_shlWord_result (shift value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.shlWord shift value) =
      SolidCoreYulCore.shlWord shift value := by
  unfold SolidCoreYulCore.shlWord
  by_cases h : 256 <= SolidCoreYulCore.norm shift
  · simp [h, norm_zero]
  · simp [h, norm_norm]

private theorem norm_shrWord_result (shift value : Word) :
    SolidCoreYulCore.norm (SolidCoreYulCore.shrWord shift value) =
      SolidCoreYulCore.shrWord shift value := by
  unfold SolidCoreYulCore.shrWord
  by_cases h : 256 <= SolidCoreYulCore.norm shift
  · simp [h, norm_zero]
  · simp [h, norm_norm]

def UnaryOp.toLegacyWordUnchecked? :
    UnaryOp -> Option (LegacyExpr -> LegacyExpr)
  | UnaryOp.bitNot => some SolidCore.Solidity.Expr.bitNot
  | UnaryOp.logicalNot => some SolidCore.Solidity.Expr.iszero
  | UnaryOp.neg => some SolidCore.Solidity.Expr.neg

private theorem UnaryOp.toLegacyWordUnchecked?_eval
    {op : UnaryOp} {legacyOp : LegacyExpr -> LegacyExpr}
    (hOp : op.toLegacyWordUnchecked? = some legacyOp)
    (expr : LegacyExpr) :
    UnaryOp.apply false op (Value.word expr.eval) =
      Except.ok (Value.word (legacyOp expr).eval) := by
  cases op <;> simp [UnaryOp.toLegacyWordUnchecked?] at hOp
  · subst legacyOp
    simp [UnaryOp.apply, Value.expectWord, SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.notWord
            (SolidCoreYulCore.norm expr.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.notWord expr.eval))
    rw [notWord_norm_arg]
  · subst legacyOp
    simp [UnaryOp.apply, Value.expectWord, SolidCore.Solidity.Expr.eval,
      boolWord_not_truthy_eq_iszeroWord, Except.bind]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.norm expr.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord expr.eval))
    rw [iszeroWord_norm_arg]
  · subst legacyOp
    simp [UnaryOp.apply, Value.expectWord, SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.subWord 0
            (SolidCoreYulCore.norm expr.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.subWord 0 expr.eval))
    rw [subWord_zero_norm_arg]

private theorem Expr.eval_unary_toLegacyWordUnchecked
    {op : UnaryOp} {legacyOp : LegacyExpr -> LegacyExpr}
    (hOp : op.toLegacyWordUnchecked? = some legacyOp)
    (runtime : Runtime)
    {expr : Expr} {legacy : LegacyExpr}
    (hEval : expr.eval uncheckedContext runtime =
      Except.ok (Value.word legacy.eval)) :
    Expr.eval uncheckedContext runtime (Expr.unary op expr) =
      Except.ok (Value.word (legacyOp legacy).eval) := by
  have hEvalRecord :
      expr.eval
          { storageFields := Context.empty.storageFields
            eventDecls := Context.empty.eventDecls
            checked := false } runtime =
        Except.ok (Value.word legacy.eval) := by
    simpa [uncheckedContext] using hEval
  cases op <;> simp [UnaryOp.toLegacyWordUnchecked?] at hOp
  · subst legacyOp
    simpa [Expr.eval, hEvalRecord, uncheckedContext] using
      UnaryOp.toLegacyWordUnchecked?_eval
        (op := UnaryOp.bitNot)
        (legacyOp := SolidCore.Solidity.Expr.bitNot)
        rfl legacy
  · subst legacyOp
    simpa [Expr.eval, hEvalRecord, uncheckedContext] using
      UnaryOp.toLegacyWordUnchecked?_eval
        (op := UnaryOp.logicalNot)
        (legacyOp := SolidCore.Solidity.Expr.iszero)
        rfl legacy
  · subst legacyOp
    simpa [Expr.eval, hEvalRecord, uncheckedContext] using
      UnaryOp.toLegacyWordUnchecked?_eval
        (op := UnaryOp.neg)
        (legacyOp := SolidCore.Solidity.Expr.neg)
        rfl legacy

def BinaryOp.toLegacyWordUnchecked? :
    BinaryOp -> Option (LegacyExpr -> LegacyExpr -> LegacyExpr)
  | BinaryOp.add => some SolidCore.Solidity.Expr.add
  | BinaryOp.sub => some SolidCore.Solidity.Expr.sub
  | BinaryOp.mul => some SolidCore.Solidity.Expr.mul
  | BinaryOp.bitAnd => some SolidCore.Solidity.Expr.bitAnd
  | BinaryOp.bitOr => some SolidCore.Solidity.Expr.bitOr
  | BinaryOp.bitXor => some SolidCore.Solidity.Expr.bitXor
  | BinaryOp.shl => some SolidCore.Solidity.Expr.shl
  | BinaryOp.shr => some SolidCore.Solidity.Expr.shr
  | BinaryOp.lt => some SolidCore.Solidity.Expr.lt
  | BinaryOp.gt => some SolidCore.Solidity.Expr.gt
  | BinaryOp.le => some SolidCore.Solidity.Expr.le
  | BinaryOp.ge => some SolidCore.Solidity.Expr.ge
  | BinaryOp.eq => some SolidCore.Solidity.Expr.eq
  | BinaryOp.ne => some SolidCore.Solidity.Expr.ne
  | BinaryOp.boolAnd => some SolidCore.Solidity.Expr.boolAnd
  | BinaryOp.boolOr => some SolidCore.Solidity.Expr.boolOr
  | _ => none

private theorem BinaryOp.toLegacyWordUnchecked?_eval
    {op : BinaryOp} {legacyOp : LegacyExpr -> LegacyExpr -> LegacyExpr}
    (hOp : op.toLegacyWordUnchecked? = some legacyOp)
    (lhs rhs : LegacyExpr) :
    BinaryOp.apply false op (Value.word lhs.eval) (Value.word rhs.eval) =
      Except.ok (Value.word (legacyOp lhs rhs).eval) := by
  cases op <;> simp [BinaryOp.toLegacyWordUnchecked?] at hOp
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, checkedAdd, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.addWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.addWord lhs.eval rhs.eval))
    rw [addWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, checkedSub, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.subWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.subWord lhs.eval rhs.eval))
    rw [subWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, checkedMul, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.mulWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.mulWord lhs.eval rhs.eval))
    rw [mulWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.andWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.andWord lhs.eval rhs.eval))
    rw [andWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.orWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.orWord lhs.eval rhs.eval))
    rw [orWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.xorWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.xorWord lhs.eval rhs.eval))
    rw [xorWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.shlWord
            (SolidCoreYulCore.norm rhs.eval)
            (SolidCoreYulCore.norm lhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.shlWord rhs.eval lhs.eval))
    rw [shlWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.shrWord
            (SolidCoreYulCore.norm rhs.eval)
            (SolidCoreYulCore.norm lhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.shrWord rhs.eval lhs.eval))
    rw [shrWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.ltWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.ltWord lhs.eval rhs.eval))
    rw [ltWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.gtWord
            (SolidCoreYulCore.norm lhs.eval)
            (SolidCoreYulCore.norm rhs.eval))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.gtWord lhs.eval rhs.eval))
    rw [gtWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval, boolWord_not_truthy_eq_iszeroWord]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.gtWord
              (SolidCoreYulCore.norm lhs.eval)
              (SolidCoreYulCore.norm rhs.eval)))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.gtWord lhs.eval rhs.eval)))
    rw [gtWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval, boolWord_not_truthy_eq_iszeroWord]
    change
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.ltWord
              (SolidCoreYulCore.norm lhs.eval)
              (SolidCoreYulCore.norm rhs.eval)))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.ltWord lhs.eval rhs.eval)))
    rw [ltWord_norm_args]
  · subst legacyOp
    simp [BinaryOp.apply, wordEq, boolWord, SolidCore.Solidity.Expr.eval,
      SolidCoreYulCore.eqWord]
  · subst legacyOp
    simp [BinaryOp.apply, SolidCore.Solidity.Expr.eval,
      boolWord_not_wordEq_eq_iszero_eqWord]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (boolWord
            (wordTruthy (SolidCoreYulCore.norm lhs.eval) &&
             wordTruthy (SolidCoreYulCore.norm rhs.eval)))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.orWord
              (SolidCoreYulCore.iszeroWord lhs.eval)
              (SolidCoreYulCore.iszeroWord rhs.eval))))
    rw [boolWord_and_truthy_eq_legacy_boolAnd]
    simp [SolidCoreYulCore.iszeroWord, SolidCoreYulCore.orWord, norm_norm]
  · subst legacyOp
    simp [BinaryOp.apply, BinaryOp.applyWord, Value.expectWord,
      SolidCore.Solidity.Expr.eval]
    change
      Except.ok
        (Value.word
          (boolWord
            (wordTruthy (SolidCoreYulCore.norm lhs.eval) ||
             wordTruthy (SolidCoreYulCore.norm rhs.eval)))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.andWord
              (SolidCoreYulCore.iszeroWord lhs.eval)
              (SolidCoreYulCore.iszeroWord rhs.eval))))
    rw [boolWord_or_truthy_eq_legacy_boolOr]
    simp [SolidCoreYulCore.iszeroWord, SolidCoreYulCore.andWord, norm_norm]

private theorem Expr.eval_binary_toLegacyWordUnchecked
    {op : BinaryOp} {legacyOp : LegacyExpr -> LegacyExpr -> LegacyExpr}
    (hOp : op.toLegacyWordUnchecked? = some legacyOp)
    (runtime : Runtime)
    {lhs rhs : Expr} {lhsLegacy rhsLegacy : LegacyExpr}
    (hLhsEval : lhs.eval uncheckedContext runtime =
      Except.ok (Value.word lhsLegacy.eval))
    (hRhsEval : rhs.eval uncheckedContext runtime =
      Except.ok (Value.word rhsLegacy.eval)) :
    Expr.eval uncheckedContext runtime (Expr.binary op lhs rhs) =
      Except.ok (Value.word (legacyOp lhsLegacy rhsLegacy).eval) := by
  have hLhsEvalRecord :
      lhs.eval
          { storageFields := Context.empty.storageFields
            eventDecls := Context.empty.eventDecls
            checked := false } runtime =
        Except.ok (Value.word lhsLegacy.eval) := by
    simpa [uncheckedContext] using hLhsEval
  have hRhsEvalRecord :
      rhs.eval
          { storageFields := Context.empty.storageFields
            eventDecls := Context.empty.eventDecls
            checked := false } runtime =
        Except.ok (Value.word rhsLegacy.eval) := by
    simpa [uncheckedContext] using hRhsEval
  cases op <;> simp [BinaryOp.toLegacyWordUnchecked?] at hOp
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.add)
        (legacyOp := SolidCore.Solidity.Expr.add)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.sub)
        (legacyOp := SolidCore.Solidity.Expr.sub)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.mul)
        (legacyOp := SolidCore.Solidity.Expr.mul)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.bitAnd)
        (legacyOp := SolidCore.Solidity.Expr.bitAnd)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.bitOr)
        (legacyOp := SolidCore.Solidity.Expr.bitOr)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.bitXor)
        (legacyOp := SolidCore.Solidity.Expr.bitXor)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.shl)
        (legacyOp := SolidCore.Solidity.Expr.shl)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.shr)
        (legacyOp := SolidCore.Solidity.Expr.shr)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.lt)
        (legacyOp := SolidCore.Solidity.Expr.lt)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.gt)
        (legacyOp := SolidCore.Solidity.Expr.gt)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.le)
        (legacyOp := SolidCore.Solidity.Expr.le)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.ge)
        (legacyOp := SolidCore.Solidity.Expr.ge)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.eq)
        (legacyOp := SolidCore.Solidity.Expr.eq)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simpa [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, uncheckedContext] using
      BinaryOp.toLegacyWordUnchecked?_eval
        (op := BinaryOp.ne)
        (legacyOp := SolidCore.Solidity.Expr.ne)
        rfl lhsLegacy rhsLegacy
  · subst legacyOp
    simp [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, Value.expectWord,
      SolidCore.Solidity.Expr.eval, uncheckedContext]
    change
      (if wordTruthy (SolidCoreYulCore.norm lhsLegacy.eval) then
        Except.ok
          (Value.word
            (boolWord (wordTruthy (SolidCoreYulCore.norm rhsLegacy.eval))))
      else
        Except.ok (Value.word 0)) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.orWord
              (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
              (SolidCoreYulCore.iszeroWord rhsLegacy.eval))))
    rw [← boolWord_and_truthy_eq_legacy_boolAnd
      lhsLegacy.eval rhsLegacy.eval]
    unfold wordTruthy boolWord
    simp [norm_norm]
    by_cases hL : SolidCoreYulCore.norm lhsLegacy.eval = 0 <;>
    by_cases hR : SolidCoreYulCore.norm rhsLegacy.eval = 0 <;>
    simp [hL, hR]
  · subst legacyOp
    simp [Expr.eval, hLhsEvalRecord, hRhsEvalRecord, Value.expectWord,
      SolidCore.Solidity.Expr.eval, uncheckedContext]
    change
      (if wordTruthy (SolidCoreYulCore.norm lhsLegacy.eval) then
        Except.ok (Value.word 1)
      else
        Except.ok
          (Value.word
            (boolWord (wordTruthy (SolidCoreYulCore.norm rhsLegacy.eval))))) =
      Except.ok
        (Value.word
          (SolidCoreYulCore.iszeroWord
            (SolidCoreYulCore.andWord
              (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
              (SolidCoreYulCore.iszeroWord rhsLegacy.eval))))
    rw [← boolWord_or_truthy_eq_legacy_boolOr
      lhsLegacy.eval rhsLegacy.eval]
    unfold wordTruthy boolWord
    simp [norm_norm]
    by_cases hL : SolidCoreYulCore.norm lhsLegacy.eval = 0 <;>
    by_cases hR : SolidCoreYulCore.norm rhsLegacy.eval = 0 <;>
    simp [hL, hR]

def Expr.toLegacyUnchecked? : Expr -> Option LegacyExpr
  | Expr.word value => some (SolidCore.Solidity.Expr.lit value)
  | Expr.unary op expr =>
      match op.toLegacyWordUnchecked?, expr.toLegacyUnchecked? with
      | some legacyOp, some legacy => some (legacyOp legacy)
      | _, _ => none
  | Expr.binary op lhs rhs =>
      match op.toLegacyWordUnchecked?, lhs.toLegacyUnchecked?,
          rhs.toLegacyUnchecked? with
      | some legacyOp, some lhsLegacy, some rhsLegacy =>
          some (legacyOp lhsLegacy rhsLegacy)
      | _, _, _ => none
  | _ => none

def Expr.listToLegacyUnchecked? :
    List Expr -> Option (List LegacyExpr)
  | [] => some []
  | expr :: rest =>
      match expr.toLegacyUnchecked?, Expr.listToLegacyUnchecked? rest with
      | some legacy, some legacyRest => some (legacy :: legacyRest)
      | _, _ => none

theorem Expr.toLegacyUnchecked?_eval_norm
    {expr : Expr} {legacy : LegacyExpr}
    (h : expr.toLegacyUnchecked? = some legacy) :
    SolidCoreYulCore.norm legacy.eval = legacy.eval := by
  induction expr generalizing legacy with
  | word value =>
      simp [Expr.toLegacyUnchecked?] at h
      subst legacy
      simp [SolidCore.Solidity.Expr.eval, norm_norm]
  | var name =>
      simp [Expr.toLegacyUnchecked?] at h
  | storage name =>
      simp [Expr.toLegacyUnchecked?] at h
  | length expr ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | index base index base_ih index_ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | unary op expr ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hExpr : expr.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
        | some legacyExpr =>
            simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
            subst legacy
            cases op <;> simp [UnaryOp.toLegacyWordUnchecked?] at hOp
            · subst legacyOp
              simpa [SolidCore.Solidity.Expr.eval] using
                norm_notWord_result legacyExpr.eval
            · subst legacyOp
              simpa [SolidCore.Solidity.Expr.eval] using
                norm_iszeroWord_result legacyExpr.eval
            · subst legacyOp
              exact (subWord_norm_result 0 legacyExpr.eval).symm
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hLhs : lhs.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hLhs] at h
        | some lhsLegacy =>
            cases hRhs : rhs.toLegacyUnchecked? with
            | none =>
                simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
            | some rhsLegacy =>
                simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
                subst legacy
                cases op <;> simp [BinaryOp.toLegacyWordUnchecked?] at hOp
                · subst legacyOp
                  exact (addWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (subWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (mulWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (andWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (orWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (xorWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_shlWord_result rhsLegacy.eval lhsLegacy.eval
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_shrWord_result rhsLegacy.eval lhsLegacy.eval
                · subst legacyOp
                  exact (ltWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  exact (gtWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_iszeroWord_result
                      (SolidCoreYulCore.gtWord lhsLegacy.eval rhsLegacy.eval)
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_iszeroWord_result
                      (SolidCoreYulCore.ltWord lhsLegacy.eval rhsLegacy.eval)
                · subst legacyOp
                  exact (eqWord_norm_result lhsLegacy.eval rhsLegacy.eval).symm
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_iszeroWord_result
                      (SolidCoreYulCore.eqWord lhsLegacy.eval rhsLegacy.eval)
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_iszeroWord_result
                      (SolidCoreYulCore.orWord
                        (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
                        (SolidCoreYulCore.iszeroWord rhsLegacy.eval))
                · subst legacyOp
                  simpa [SolidCore.Solidity.Expr.eval] using
                    norm_iszeroWord_result
                      (SolidCoreYulCore.andWord
                        (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
                        (SolidCoreYulCore.iszeroWord rhsLegacy.eval))

theorem Expr.toLegacyUnchecked?_eval_runtime
    {expr : Expr} {legacy : LegacyExpr}
    (h : expr.toLegacyUnchecked? = some legacy)
    (runtime : Runtime) :
    expr.eval uncheckedContext runtime =
      Except.ok (Value.word legacy.eval) := by
  induction expr generalizing legacy runtime with
  | word value =>
      simp [Expr.toLegacyUnchecked?] at h
      subst legacy
      simp [Expr.eval, SolidCore.Solidity.Expr.eval, normWord]
  | var name =>
      simp [Expr.toLegacyUnchecked?] at h
  | storage name =>
      simp [Expr.toLegacyUnchecked?] at h
  | length expr ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | index base index base_ih index_ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | unary op expr ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hExpr : expr.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
        | some legacyExpr =>
            simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
            subst legacy
            have hEval :
                expr.eval uncheckedContext runtime =
                  Except.ok (Value.word legacyExpr.eval) :=
              ih hExpr runtime
            exact Expr.eval_unary_toLegacyWordUnchecked hOp runtime hEval
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hLhs : lhs.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hLhs] at h
        | some lhsLegacy =>
            cases hRhs : rhs.toLegacyUnchecked? with
            | none => simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
            | some rhsLegacy =>
                simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
                subst legacy
                have hLhsEval' :
                    lhs.eval uncheckedContext runtime =
                      Except.ok (Value.word lhsLegacy.eval) :=
                  lhs_ih hLhs runtime
                have hRhsEval' :
                    rhs.eval uncheckedContext runtime =
                      Except.ok (Value.word rhsLegacy.eval) :=
                  rhs_ih hRhs runtime
                have hLhsEval :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsLegacy.eval) := by
                  simpa [uncheckedContext] using lhs_ih hLhs runtime
                have hRhsEval :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsLegacy.eval) := by
                  simpa [uncheckedContext] using rhs_ih hRhs runtime
                exact
                  Expr.eval_binary_toLegacyWordUnchecked
                    hOp runtime hLhsEval' hRhsEval'

theorem Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
    (context : Context) (hChecked : context.checked = false)
    {expr : Expr} {legacy : LegacyExpr}
    (h : expr.toLegacyUnchecked? = some legacy)
    (runtime : Runtime) :
    expr.eval context runtime =
      Except.ok (Value.word legacy.eval) := by
  induction expr generalizing legacy runtime with
  | word value =>
      simp [Expr.toLegacyUnchecked?] at h
      subst legacy
      simp [Expr.eval, SolidCore.Solidity.Expr.eval, normWord]
  | var name =>
      simp [Expr.toLegacyUnchecked?] at h
  | storage name =>
      simp [Expr.toLegacyUnchecked?] at h
  | length expr ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | index base index base_ih index_ih =>
      simp [Expr.toLegacyUnchecked?] at h
  | unary op expr ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hExpr : expr.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
        | some legacyExpr =>
            simp [Expr.toLegacyUnchecked?, hOp, hExpr] at h
            subst legacy
            have hEval :
                expr.eval context runtime =
                  Except.ok (Value.word legacyExpr.eval) :=
              ih hExpr runtime
            cases op <;> simp [UnaryOp.toLegacyWordUnchecked?] at hOp
            · subst legacyOp
              simpa [Expr.eval, hEval, hChecked] using
                UnaryOp.toLegacyWordUnchecked?_eval
                  (op := UnaryOp.bitNot)
                  (legacyOp := SolidCore.Solidity.Expr.bitNot)
                  rfl legacyExpr
            · subst legacyOp
              simpa [Expr.eval, hEval, hChecked] using
                UnaryOp.toLegacyWordUnchecked?_eval
                  (op := UnaryOp.logicalNot)
                  (legacyOp := SolidCore.Solidity.Expr.iszero)
                  rfl legacyExpr
            · subst legacyOp
              simpa [Expr.eval, hEval, hChecked] using
                UnaryOp.toLegacyWordUnchecked?_eval
                  (op := UnaryOp.neg)
                  (legacyOp := SolidCore.Solidity.Expr.neg)
                  rfl legacyExpr
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases hOp : op.toLegacyWordUnchecked? with
      | none => simp [Expr.toLegacyUnchecked?, hOp] at h
      | some legacyOp =>
        cases hLhs : lhs.toLegacyUnchecked? with
        | none => simp [Expr.toLegacyUnchecked?, hOp, hLhs] at h
        | some lhsLegacy =>
            cases hRhs : rhs.toLegacyUnchecked? with
            | none => simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
            | some rhsLegacy =>
                simp [Expr.toLegacyUnchecked?, hOp, hLhs, hRhs] at h
                subst legacy
                have hLhsEval :
                    lhs.eval context runtime =
                      Except.ok (Value.word lhsLegacy.eval) :=
                  lhs_ih hLhs runtime
                have hRhsEval :
                    rhs.eval context runtime =
                      Except.ok (Value.word rhsLegacy.eval) :=
                  rhs_ih hRhs runtime
                cases op <;> simp [BinaryOp.toLegacyWordUnchecked?] at hOp
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.add)
                      (legacyOp := SolidCore.Solidity.Expr.add)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.sub)
                      (legacyOp := SolidCore.Solidity.Expr.sub)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.mul)
                      (legacyOp := SolidCore.Solidity.Expr.mul)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.bitAnd)
                      (legacyOp := SolidCore.Solidity.Expr.bitAnd)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.bitOr)
                      (legacyOp := SolidCore.Solidity.Expr.bitOr)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.bitXor)
                      (legacyOp := SolidCore.Solidity.Expr.bitXor)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.shl)
                      (legacyOp := SolidCore.Solidity.Expr.shl)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.shr)
                      (legacyOp := SolidCore.Solidity.Expr.shr)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.lt)
                      (legacyOp := SolidCore.Solidity.Expr.lt)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.gt)
                      (legacyOp := SolidCore.Solidity.Expr.gt)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.le)
                      (legacyOp := SolidCore.Solidity.Expr.le)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.ge)
                      (legacyOp := SolidCore.Solidity.Expr.ge)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.eq)
                      (legacyOp := SolidCore.Solidity.Expr.eq)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simpa [Expr.eval, hLhsEval, hRhsEval, hChecked] using
                    BinaryOp.toLegacyWordUnchecked?_eval
                      (op := BinaryOp.ne)
                      (legacyOp := SolidCore.Solidity.Expr.ne)
                      rfl lhsLegacy rhsLegacy
                · subst legacyOp
                  simp [Expr.eval, hLhsEval, hRhsEval, Value.expectWord,
                    SolidCore.Solidity.Expr.eval, hChecked]
                  change
                    (if wordTruthy (SolidCoreYulCore.norm lhsLegacy.eval) then
                      Except.ok
                        (Value.word
                          (boolWord
                            (wordTruthy
                              (SolidCoreYulCore.norm rhsLegacy.eval))))
                    else
                      Except.ok (Value.word 0)) =
                    Except.ok
                      (Value.word
                        (SolidCoreYulCore.iszeroWord
                          (SolidCoreYulCore.orWord
                            (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
                            (SolidCoreYulCore.iszeroWord rhsLegacy.eval))))
                  rw [← boolWord_and_truthy_eq_legacy_boolAnd
                    lhsLegacy.eval rhsLegacy.eval]
                  unfold wordTruthy boolWord
                  simp [norm_norm]
                  by_cases hL :
                      SolidCoreYulCore.norm lhsLegacy.eval = 0 <;>
                  by_cases hR :
                      SolidCoreYulCore.norm rhsLegacy.eval = 0 <;>
                  simp [hL, hR]
                · subst legacyOp
                  simp [Expr.eval, hLhsEval, hRhsEval, Value.expectWord,
                    SolidCore.Solidity.Expr.eval, hChecked]
                  change
                    (if wordTruthy (SolidCoreYulCore.norm lhsLegacy.eval) then
                      Except.ok (Value.word 1)
                    else
                      Except.ok
                        (Value.word
                          (boolWord
                            (wordTruthy
                              (SolidCoreYulCore.norm rhsLegacy.eval))))) =
                    Except.ok
                      (Value.word
                        (SolidCoreYulCore.iszeroWord
                          (SolidCoreYulCore.andWord
                            (SolidCoreYulCore.iszeroWord lhsLegacy.eval)
                            (SolidCoreYulCore.iszeroWord rhsLegacy.eval))))
                  rw [← boolWord_or_truthy_eq_legacy_boolOr
                    lhsLegacy.eval rhsLegacy.eval]
                  unfold wordTruthy boolWord
                  simp [norm_norm]
                  by_cases hL :
                      SolidCoreYulCore.norm lhsLegacy.eval = 0 <;>
                  by_cases hR :
                      SolidCoreYulCore.norm rhsLegacy.eval = 0 <;>
                  simp [hL, hR]

theorem Expr.toLegacyUnchecked?_eval
    {expr : Expr} {legacy : LegacyExpr}
    (h : expr.toLegacyUnchecked? = some legacy) :
    expr.eval uncheckedContext emptyRuntime =
      Except.ok (Value.word legacy.eval) :=
  Expr.toLegacyUnchecked?_eval_runtime h emptyRuntime

theorem Expr.listToLegacyUnchecked?_evalList_runtime_of_checked_false
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    {exprs : List Expr} {legacies : List LegacyExpr}
    (h : Expr.listToLegacyUnchecked? exprs = some legacies) :
    ∃ values : List Value,
      Expr.evalList context runtime exprs = Except.ok values := by
  induction exprs generalizing legacies with
  | nil =>
      simp [Expr.listToLegacyUnchecked?] at h
      subst legacies
      exact ⟨[], by simp [Expr.evalList]⟩
  | cons expr rest ih =>
      cases hExpr : expr.toLegacyUnchecked? with
      | none =>
          simp [Expr.listToLegacyUnchecked?, hExpr] at h
      | some legacy =>
          cases hRest : Expr.listToLegacyUnchecked? rest with
          | none =>
              simp [Expr.listToLegacyUnchecked?, hExpr, hRest] at h
          | some legacyRest =>
              simp [Expr.listToLegacyUnchecked?, hExpr, hRest] at h
              subst legacies
              obtain ⟨restValues, hRestEval⟩ := ih hRest
              have hExprEval :
                  expr.eval context runtime =
                    Except.ok (Value.word legacy.eval) :=
                Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
                  context hChecked hExpr runtime
              exact
                ⟨Value.word legacy.eval :: restValues,
                  by
                    simp [Expr.evalList, hExprEval, hRestEval,
                      Bind.bind, Except.bind]⟩

def Expr.toFullYulWithLocalWord?
    (sourceName : String) (yulName : SolidCoreYulCore.FullYul.Name) :
    Expr -> Option YulExpr
  | Expr.word value =>
      some
        (SolidCoreYulCore.FullYul.Expr.value
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm value)))
  | Expr.var name =>
      if name = sourceName then
        some (SolidCoreYulCore.FullYul.Expr.var yulName)
      else
        none
  | Expr.unary UnaryOp.bitNot expr =>
      match expr.toFullYulWithLocalWord? sourceName yulName with
      | some yulExpr =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.notOp [yulExpr])
      | none => none
  | Expr.unary UnaryOp.logicalNot expr =>
      match expr.toFullYulWithLocalWord? sourceName yulName with
      | some yulExpr =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero [yulExpr])
      | none => none
  | Expr.unary UnaryOp.neg expr =>
      match expr.toFullYulWithLocalWord? sourceName yulName with
      | some yulExpr =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.sub
              [ SolidCoreYulCore.FullYul.Expr.value
                  (SolidCoreYulCore.FullYul.Value.word 0)
              , yulExpr ])
      | none => none
  | Expr.binary BinaryOp.add lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.add [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.sub lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.sub [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.mul lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.mul [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.bitAnd lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.andOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.bitOr lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.orOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.bitXor lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.xorOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.shl lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.shlOp [rhsYul, lhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.shr lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.shrOp [rhsYul, lhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.lt lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.ltOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.gt lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.gtOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.eq lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.eqOp [lhsYul, rhsYul])
      | _, _ => none
  | Expr.binary BinaryOp.ne lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero
              [SolidCoreYulCore.FullYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.eqOp [lhsYul, rhsYul]])
      | _, _ => none
  | Expr.binary BinaryOp.le lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero
              [SolidCoreYulCore.FullYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.gtOp [lhsYul, rhsYul]])
      | _, _ => none
  | Expr.binary BinaryOp.ge lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero
              [SolidCoreYulCore.FullYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.ltOp [lhsYul, rhsYul]])
      | _, _ => none
  | Expr.binary BinaryOp.boolAnd lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero
              [SolidCoreYulCore.FullYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.orOp
                [ SolidCoreYulCore.FullYul.Expr.builtin
                    SolidCoreYulCore.Evm.Builtin.iszero [lhsYul]
                , SolidCoreYulCore.FullYul.Expr.builtin
                    SolidCoreYulCore.Evm.Builtin.iszero [rhsYul] ]])
      | _, _ => none
  | Expr.binary BinaryOp.boolOr lhs rhs =>
      match lhs.toFullYulWithLocalWord? sourceName yulName,
          rhs.toFullYulWithLocalWord? sourceName yulName with
      | some lhsYul, some rhsYul =>
          some
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.iszero
              [SolidCoreYulCore.FullYul.Expr.builtin
                SolidCoreYulCore.Evm.Builtin.andOp
                [ SolidCoreYulCore.FullYul.Expr.builtin
                    SolidCoreYulCore.Evm.Builtin.iszero [lhsYul]
                , SolidCoreYulCore.FullYul.Expr.builtin
                    SolidCoreYulCore.Evm.Builtin.iszero [rhsYul] ]])
      | _, _ => none
  | _ => none

theorem Expr.toFullYulWithLocalWord?_correct_env
    {sourceName : String} {yulName : SolidCoreYulCore.FullYul.Name}
    {expr : Expr} {yulExpr : YulExpr}
    (hCompile :
      expr.toFullYulWithLocalWord? sourceName yulName = some yulExpr)
    (runtime : Runtime) (config : SolidCoreYulCore.SymYul.Config)
    (localValue : Word)
    (hSourceLocal :
      runtime.lookupLocal? sourceName = some (Value.word localValue))
    (hYulLocal :
      SolidCoreYulCore.FullYul.lookup? config.env yulName =
        some (SolidCoreYulCore.FullYul.Value.word localValue)) :
    ∃ value : Word,
      expr.eval uncheckedContext runtime = Except.ok (Value.word value) ∧
      SolidCoreYulCore.SymYul.evalExpr config yulExpr =
        some (SolidCoreYulCore.FullYul.Value.word value, config) := by
  induction expr generalizing yulExpr runtime config localValue with
  | word value =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
      subst yulExpr
      exact
        ⟨SolidCoreYulCore.norm value, by
          simp [Expr.eval, normWord, SolidCoreYulCore.SymYul.evalExpr],
        by
          simp [SolidCoreYulCore.SymYul.evalExpr]⟩
  | var name =>
      by_cases hName : name = sourceName
      · subst name
        simp [Expr.toFullYulWithLocalWord?] at hCompile
        subst yulExpr
        have hSourceLocal' :
            LocalEnv.lookup? runtime.locals sourceName =
              some (Value.word localValue) := by
          simpa [Runtime.lookupLocal?] using hSourceLocal
        exact
          ⟨localValue, by
            simp [Expr.eval, Runtime.lookupLocal?, hSourceLocal',
              uncheckedContext],
          by
            simp [SolidCoreYulCore.SymYul.evalExpr, hYulLocal]⟩
      · simp [Expr.toFullYulWithLocalWord?, hName] at hCompile
  | storage name =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | length expr ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | index base index base_ih index_ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | unary op expr ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case bitNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            rcases ih hExpr runtime config localValue
                hSourceLocal hYulLocal with
              ⟨innerValue, hInnerEval, hInnerYul⟩
            have hInnerEval' :
                expr.eval
                    { storageFields := Context.empty.storageFields
                      eventDecls := Context.empty.eventDecls
                      checked := false } runtime =
                  Except.ok (Value.word innerValue) := by
              simpa [uncheckedContext] using hInnerEval
            refine ⟨SolidCoreYulCore.notWord innerValue, ?_, ?_⟩
            · simp [Expr.eval, hInnerEval', UnaryOp.apply,
                Value.expectWord, uncheckedContext]
              change
                Except.ok
                    (Value.word
                      (SolidCoreYulCore.notWord
                        (SolidCoreYulCore.norm innerValue))) =
                  Except.ok
                    (Value.word (SolidCoreYulCore.notWord innerValue))
              rw [notWord_norm_arg]
            · simp [SolidCoreYulCore.SymYul.evalExpr,
                SolidCoreYulCore.SymYul.evalExprs,
                SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                hInnerYul, SolidCore.Solidity.evalEvmBuiltin_not_word]
      case logicalNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            rcases ih hExpr runtime config localValue
                hSourceLocal hYulLocal with
              ⟨innerValue, hInnerEval, hInnerYul⟩
            have hInnerEval' :
                expr.eval
                    { storageFields := Context.empty.storageFields
                      eventDecls := Context.empty.eventDecls
                      checked := false } runtime =
                  Except.ok (Value.word innerValue) := by
              simpa [uncheckedContext] using hInnerEval
            refine ⟨SolidCoreYulCore.iszeroWord innerValue, ?_, ?_⟩
            · simp [Expr.eval, hInnerEval', UnaryOp.apply,
                Value.expectWord, boolWord_not_truthy_eq_iszeroWord,
                uncheckedContext, Except.bind]
              change
                Except.ok
                    (Value.word
                      (SolidCoreYulCore.iszeroWord
                        (SolidCoreYulCore.norm innerValue))) =
                  Except.ok
                    (Value.word (SolidCoreYulCore.iszeroWord innerValue))
              rw [iszeroWord_norm_arg]
            · simp [SolidCoreYulCore.SymYul.evalExpr,
                SolidCoreYulCore.SymYul.evalExprs,
                SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                hInnerYul, SolidCore.Solidity.evalEvmBuiltin_iszero_word]
      case neg =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            rcases ih hExpr runtime config localValue
                hSourceLocal hYulLocal with
              ⟨innerValue, hInnerEval, hInnerYul⟩
            have hInnerEval' :
                expr.eval
                    { storageFields := Context.empty.storageFields
                      eventDecls := Context.empty.eventDecls
                      checked := false } runtime =
                  Except.ok (Value.word innerValue) := by
              simpa [uncheckedContext] using hInnerEval
            refine ⟨SolidCoreYulCore.subWord 0 innerValue, ?_, ?_⟩
            · simp [Expr.eval, hInnerEval', UnaryOp.apply,
                Value.expectWord, uncheckedContext, Except.bind]
              change
                Except.ok
                    (Value.word
                      (SolidCoreYulCore.subWord 0
                        (SolidCoreYulCore.norm innerValue))) =
                  Except.ok
                    (Value.word (SolidCoreYulCore.subWord 0 innerValue))
              rw [subWord_zero_norm_arg]
            · simp [SolidCoreYulCore.SymYul.evalExpr,
                SolidCoreYulCore.SymYul.evalExprs,
                SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                hInnerYul, SolidCore.Solidity.evalEvmBuiltin_sub_word]
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case add =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.addWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord, checkedAdd,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.addWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.addWord lhsValue rhsValue))
                  rw [addWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_add_word]
      case sub =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.subWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord, checkedSub,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.subWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.subWord lhsValue rhsValue))
                  rw [subWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_sub_word]
      case mul =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.mulWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord, checkedMul,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.mulWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.mulWord lhsValue rhsValue))
                  rw [mulWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_mul_word]
      case bitAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.andWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.andWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.andWord lhsValue rhsValue))
                  rw [andWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_and_word]
      case bitOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.orWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.orWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.orWord lhsValue rhsValue))
                  rw [orWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_or_word]
      case bitXor =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.xorWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.xorWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.xorWord lhsValue rhsValue))
                  rw [xorWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_xor_word]
      case shl =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.shlWord rhsValue lhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.shlWord
                            (SolidCoreYulCore.norm rhsValue)
                            (SolidCoreYulCore.norm lhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.shlWord rhsValue lhsValue))
                  rw [shlWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hRhsYul, hLhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_shl_word]
      case shr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.shrWord rhsValue lhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.shrWord
                            (SolidCoreYulCore.norm rhsValue)
                            (SolidCoreYulCore.norm lhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.shrWord rhsValue lhsValue))
                  rw [shrWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hRhsYul, hLhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_shr_word]
      case lt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.ltWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.ltWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.ltWord lhsValue rhsValue))
                  rw [ltWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_lt_word]
      case gt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.gtWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, uncheckedContext]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.gtWord
                            (SolidCoreYulCore.norm lhsValue)
                            (SolidCoreYulCore.norm rhsValue))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.gtWord lhsValue rhsValue))
                  rw [gtWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_gt_word]
      case eq =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.eqWord lhsValue rhsValue, ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, wordEq, boolWord,
                    SolidCoreYulCore.eqWord, uncheckedContext,
                    Except.bind]
                  rfl
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_eq_word]
      case ne =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.iszeroWord
                    (SolidCoreYulCore.eqWord lhsValue rhsValue), ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, boolWord_not_wordEq_eq_iszero_eqWord,
                    uncheckedContext, Except.bind]
                  rfl
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_eq_word,
                    SolidCore.Solidity.evalEvmBuiltin_iszero_word]
      case le =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.iszeroWord
                    (SolidCoreYulCore.gtWord lhsValue rhsValue), ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, boolWord_not_truthy_eq_iszeroWord,
                    uncheckedContext, Except.bind]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.iszeroWord
                            (SolidCoreYulCore.gtWord
                              (SolidCoreYulCore.norm lhsValue)
                              (SolidCoreYulCore.norm rhsValue)))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.iszeroWord
                            (SolidCoreYulCore.gtWord lhsValue rhsValue)))
                  rw [gtWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_gt_word,
                    SolidCore.Solidity.evalEvmBuiltin_iszero_word]
      case ge =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.iszeroWord
                    (SolidCoreYulCore.ltWord lhsValue rhsValue), ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    BinaryOp.apply, BinaryOp.applyWord,
                    Value.expectWord, boolWord_not_truthy_eq_iszeroWord,
                    uncheckedContext, Except.bind]
                  change
                    Except.ok
                        (Value.word
                          (SolidCoreYulCore.iszeroWord
                            (SolidCoreYulCore.ltWord
                              (SolidCoreYulCore.norm lhsValue)
                              (SolidCoreYulCore.norm rhsValue)))) =
                      Except.ok
                        (Value.word
                          (SolidCoreYulCore.iszeroWord
                            (SolidCoreYulCore.ltWord lhsValue rhsValue)))
                  rw [ltWord_norm_args]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_lt_word,
                    SolidCore.Solidity.evalEvmBuiltin_iszero_word]
      case boolAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.iszeroWord
                    (SolidCoreYulCore.orWord
                      (SolidCoreYulCore.iszeroWord lhsValue)
                      (SolidCoreYulCore.iszeroWord rhsValue)), ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    Value.expectWord, uncheckedContext]
                  change
                    (if wordTruthy (SolidCoreYulCore.norm lhsValue) then
                      Except.ok
                        (Value.word
                          (boolWord
                            (wordTruthy (SolidCoreYulCore.norm rhsValue))))
                    else
                      Except.ok (Value.word 0)) =
                    Except.ok
                      (Value.word
                        (SolidCoreYulCore.iszeroWord
                          (SolidCoreYulCore.orWord
                            (SolidCoreYulCore.iszeroWord lhsValue)
                            (SolidCoreYulCore.iszeroWord rhsValue))))
                  rw [← boolWord_and_truthy_eq_legacy_boolAnd
                    lhsValue rhsValue]
                  unfold wordTruthy boolWord
                  simp [norm_norm]
                  by_cases hL : SolidCoreYulCore.norm lhsValue = 0 <;>
                  by_cases hR : SolidCoreYulCore.norm rhsValue = 0 <;>
                  simp [hL, hR]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_iszero_word,
                    SolidCore.Solidity.evalEvmBuiltin_or_word]
      case boolOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                rcases lhs_ih hLhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨lhsValue, hLhsEval, hLhsYul⟩
                rcases rhs_ih hRhs runtime config localValue
                    hSourceLocal hYulLocal with
                  ⟨rhsValue, hRhsEval, hRhsYul⟩
                have hLhsEval' :
                    lhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word lhsValue) := by
                  simpa [uncheckedContext] using hLhsEval
                have hRhsEval' :
                    rhs.eval
                        { storageFields := Context.empty.storageFields
                          eventDecls := Context.empty.eventDecls
                          checked := false } runtime =
                      Except.ok (Value.word rhsValue) := by
                  simpa [uncheckedContext] using hRhsEval
                refine
                  ⟨SolidCoreYulCore.iszeroWord
                    (SolidCoreYulCore.andWord
                      (SolidCoreYulCore.iszeroWord lhsValue)
                      (SolidCoreYulCore.iszeroWord rhsValue)), ?_, ?_⟩
                · simp [Expr.eval, hLhsEval', hRhsEval',
                    Value.expectWord, uncheckedContext]
                  change
                    (if wordTruthy (SolidCoreYulCore.norm lhsValue) then
                      Except.ok (Value.word 1)
                    else
                      Except.ok
                        (Value.word
                          (boolWord
                            (wordTruthy (SolidCoreYulCore.norm rhsValue))))) =
                    Except.ok
                      (Value.word
                        (SolidCoreYulCore.iszeroWord
                          (SolidCoreYulCore.andWord
                            (SolidCoreYulCore.iszeroWord lhsValue)
                            (SolidCoreYulCore.iszeroWord rhsValue))))
                  rw [← boolWord_or_truthy_eq_legacy_boolOr
                    lhsValue rhsValue]
                  unfold wordTruthy boolWord
                  simp [norm_norm]
                  by_cases hL : SolidCoreYulCore.norm lhsValue = 0 <;>
                  by_cases hR : SolidCoreYulCore.norm rhsValue = 0 <;>
                  simp [hL, hR]
                · simp [SolidCoreYulCore.SymYul.evalExpr,
                    SolidCoreYulCore.SymYul.evalExprs,
                    SolidCoreYulCore.SymYul.evalExprsAsYulValues,
                    hLhsYul, hRhsYul,
                    SolidCore.Solidity.evalEvmBuiltin_iszero_word,
                    SolidCore.Solidity.evalEvmBuiltin_and_word]

def localExprRuntime (sourceName : String) (value : Word) : Runtime :=
  { state := State.empty
    locals := [[(sourceName, Value.word value)]] }

def localExprConfig
    (yulName : SolidCoreYulCore.FullYul.Name) (value : Word) :
    SolidCoreYulCore.SymYul.Config :=
  { SolidCoreYulCore.SymYul.Config.empty with
    env := [(yulName, SolidCoreYulCore.FullYul.Value.word value)] }

def localReadAddFiveExpr : Expr :=
  Expr.binary BinaryOp.add (Expr.var "x") (Expr.word 5)

def localReadAddFiveYul : YulExpr :=
  SolidCoreYulCore.FullYul.Expr.builtin
    SolidCoreYulCore.Evm.Builtin.add
    [ SolidCoreYulCore.FullYul.Expr.var SolidCore.Solidity.localName
    , SolidCoreYulCore.FullYul.Expr.value
        (SolidCoreYulCore.FullYul.Value.word 5) ]

theorem localReadAddFiveExpr_toFullYulWithLocalWord :
    localReadAddFiveExpr.toFullYulWithLocalWord? "x"
        SolidCore.Solidity.localName =
      some localReadAddFiveYul := by
  rfl

theorem localReadAddFiveExpr_toFullYulWithLocalWord_correct :
    ∃ value : Word,
      localReadAddFiveExpr.eval uncheckedContext
          (localExprRuntime "x" 2) =
        Except.ok (Value.word value) ∧
      SolidCoreYulCore.SymYul.evalExpr
          (localExprConfig SolidCore.Solidity.localName 2)
          localReadAddFiveYul =
        some
          (SolidCoreYulCore.FullYul.Value.word value,
            localExprConfig SolidCore.Solidity.localName 2) := by
  exact
    Expr.toFullYulWithLocalWord?_correct_env
      localReadAddFiveExpr_toFullYulWithLocalWord
      (localExprRuntime "x" 2)
      (localExprConfig SolidCore.Solidity.localName 2)
      2
      (by rfl)
      (by rfl)

theorem Expr.toFullYulWithLocalWord?_compilerEmittable
    {sourceName : String} {yulName : SolidCoreYulCore.FullYul.Name}
    {expr : Expr} {yulExpr : YulExpr}
    (hCompile :
      expr.toFullYulWithLocalWord? sourceName yulName = some yulExpr) :
    SolidCoreYulCore.FullYul.CompilerEmittableExpr
      SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
      yulExpr := by
  induction expr generalizing yulExpr with
  | word value =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
      subst yulExpr
      exact
        SolidCoreYulCore.FullYul.CompilerEmittableExpr.value
          (SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreValue.word
            (SolidCoreYulCore.norm value))
  | var name =>
      by_cases hName : name = sourceName
      · subst name
        simp [Expr.toFullYulWithLocalWord?] at hCompile
        subst yulExpr
        exact SolidCoreYulCore.FullYul.CompilerEmittableExpr.var yulName
      · simp [Expr.toFullYulWithLocalWord?, hName] at hCompile
  | storage name =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | length expr ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | index base index base_ih index_ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | unary op expr ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case bitNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            exact
              SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.notOp
                (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                  (ih hExpr)
                  SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case logicalNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            exact
              SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                  (ih hExpr)
                  SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case neg =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            exact
              SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sub
                (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                  (SolidCoreYulCore.FullYul.CompilerEmittableExpr.value
                    (SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreValue.word 0))
                  (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                    (ih hExpr)
                    SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case add =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.add
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case sub =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.sub
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case mul =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.mul
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case bitAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.andOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case bitOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.orOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case bitXor =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.xorOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case shl =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.shlOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (rhs_ih hRhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (lhs_ih hLhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case shr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.shrOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (rhs_ih hRhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (lhs_ih hLhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case lt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.ltOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case gt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.gtOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case eq =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.eqOp
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (lhs_ih hLhs)
                      (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                        (rhs_ih hRhs)
                        SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
      case ne =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                        SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.eqOp
                        (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                          (lhs_ih hLhs)
                          (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                            (rhs_ih hRhs)
                            SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)))
                      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case le =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                        SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.gtOp
                        (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                          (lhs_ih hLhs)
                          (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                            (rhs_ih hRhs)
                            SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)))
                      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case ge =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                        SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.ltOp
                        (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                          (lhs_ih hLhs)
                          (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                            (rhs_ih hRhs)
                            SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)))
                      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case boolAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                        SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.orOp
                        (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                          (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                            SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                            (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                              (lhs_ih hLhs)
                              SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
                          (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                            (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                              SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                              (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                                (rhs_ih hRhs)
                                SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
                            SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)))
                      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)
      case boolOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName yulName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName yulName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                exact
                  SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                    SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                    (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                      (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                        SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.andOp
                        (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                          (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                            SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                            (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                              (lhs_ih hLhs)
                              SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
                          (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                            (SolidCoreYulCore.FullYul.CompilerEmittableExpr.builtin
                              SolidCoreYulCore.FullYul.CompilerProfile.CurrentSolidCoreBuiltin.iszero
                              (SolidCoreYulCore.FullYul.CompilerEmittableExprs.cons
                                (rhs_ih hRhs)
                                SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil))
                            SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)))
                      SolidCoreYulCore.FullYul.CompilerEmittableExprs.nil)

theorem Expr.toFullYulWithLocalWord?_staticChecked_local
    {sourceName : String} {expr : Expr} {yulExpr : YulExpr}
    (hCompile :
      expr.toFullYulWithLocalWord? sourceName
          SolidCore.Solidity.localName = some yulExpr) :
    SolidCoreYulCore.FullYul.checkExpr
      { vars := [SolidCore.Solidity.localName,
          SolidCore.Solidity.returnName], funcs := [] }
      yulExpr = true := by
  induction expr generalizing yulExpr with
  | word value =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
      subst yulExpr
      simp [SolidCoreYulCore.FullYul.checkExpr]
  | var name =>
      by_cases hName : name = sourceName
      · subst name
        simp [Expr.toFullYulWithLocalWord?] at hCompile
        subst yulExpr
        simp [SolidCoreYulCore.FullYul.checkExpr,
          SolidCoreYulCore.FullYul.containsName,
          SolidCore.Solidity.localName, SolidCore.Solidity.returnName]
      · simp [Expr.toFullYulWithLocalWord?, hName] at hCompile
  | storage name =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | length expr ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | index base index base_ih index_ih =>
      simp [Expr.toFullYulWithLocalWord?] at hCompile
  | unary op expr ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case bitNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            simp [SolidCoreYulCore.FullYul.checkExpr,
              SolidCoreYulCore.FullYul.checkExprs,
              SolidCoreYulCore.Evm.Builtin.signature?, ih hExpr]
      case logicalNot =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            simp [SolidCoreYulCore.FullYul.checkExpr,
              SolidCoreYulCore.FullYul.checkExprs,
              SolidCoreYulCore.Evm.Builtin.signature?, ih hExpr]
      case neg =>
        cases hExpr :
            expr.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
        | some innerYul =>
            simp [Expr.toFullYulWithLocalWord?, hExpr] at hCompile
            subst yulExpr
            simp [SolidCoreYulCore.FullYul.checkExpr,
              SolidCoreYulCore.FullYul.checkExprs,
              SolidCoreYulCore.Evm.Builtin.signature?, ih hExpr]
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases op <;> try simp [Expr.toFullYulWithLocalWord?] at hCompile
      case add =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case sub =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case mul =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case bitAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case bitOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case bitXor =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case shl =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case shr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case lt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case gt =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case eq =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case ne =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case le =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case ge =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case boolAnd =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]
      case boolOr =>
        cases hLhs :
            lhs.toFullYulWithLocalWord? sourceName
              SolidCore.Solidity.localName with
        | none =>
            simp [Expr.toFullYulWithLocalWord?, hLhs] at hCompile
        | some lhsYul =>
            cases hRhs :
                rhs.toFullYulWithLocalWord? sourceName
                  SolidCore.Solidity.localName with
            | none =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
            | some rhsYul =>
                simp [Expr.toFullYulWithLocalWord?, hLhs, hRhs]
                  at hCompile
                subst yulExpr
                simp [SolidCoreYulCore.FullYul.checkExpr,
                  SolidCoreYulCore.FullYul.checkExprs,
                  SolidCoreYulCore.Evm.Builtin.signature?,
                  lhs_ih hLhs, rhs_ih hRhs]

def sourceStorageContext (name : String) (slot : Word) : Context :=
  { uncheckedContext with
    storageFields := [{ name := name, slot := slot }] }

def sourceStorageRuntime (slot value : Word) : Runtime :=
  Runtime.ofState
    { State.empty with
      storage :=
        [(SolidCoreYulCore.norm slot, SolidCoreYulCore.norm value)] }

theorem WordMap.lookup?_eq_of_norm
    (storage : WordMap) {left right : Word}
    (hNorm :
      SolidCoreYulCore.norm left = SolidCoreYulCore.norm right) :
    WordMap.lookup? storage left = WordMap.lookup? storage right := by
  induction storage with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp [WordMap.lookup?, wordEq, hNorm, ih]

theorem WordMap.lookup?_norm_result
    (storage : WordMap) (slot value : Word)
    (hLookup : WordMap.lookup? storage slot = some value) :
    SolidCoreYulCore.norm value = value := by
  induction storage with
  | nil =>
      simp [WordMap.lookup?] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨key, entryValue⟩
      by_cases hKey : wordEq key slot
      · simp [WordMap.lookup?, hKey] at hLookup
        subst value
        exact norm_norm entryValue
      · simp [WordMap.lookup?, hKey] at hLookup
        exact ih hLookup

theorem WordMap.lookup?_insertLoop_same
    (storage : WordMap) (slot value : Word) :
    WordMap.lookup? (WordMap.insertLoop storage slot value) slot =
      some (SolidCoreYulCore.norm value) := by
  induction storage with
  | nil =>
      simp [WordMap.insertLoop, WordMap.lookup?, wordEq, norm_norm]
  | cons entry rest ih =>
      rcases entry with ⟨entryKey, entryValue⟩
      by_cases hEntry : wordEq entryKey slot = true
      · have hStored : wordEq (SolidCoreYulCore.norm slot) slot = true := by
          simp [wordEq, norm_norm]
        simp [WordMap.insertLoop, WordMap.lookup?, hEntry, hStored,
          norm_norm]
      · have hEntryFalse : wordEq entryKey slot = false := by
          cases h : wordEq entryKey slot <;> simp [h] at hEntry ⊢
        simp [WordMap.insertLoop, WordMap.lookup?, hEntryFalse, ih]

theorem WordMap.lookup?_insertLoop_other
    (storage : WordMap) {slot query value : Word}
    (hOther :
      SolidCoreYulCore.norm slot ≠ SolidCoreYulCore.norm query) :
    WordMap.lookup? (WordMap.insertLoop storage slot value) query =
      WordMap.lookup? storage query := by
  induction storage with
  | nil =>
      have hStored : wordEq (SolidCoreYulCore.norm slot) query = false := by
        have hNot :
            ¬ SolidCoreYulCore.norm (SolidCoreYulCore.norm slot) =
              SolidCoreYulCore.norm query := by
          simpa [norm_norm] using hOther
        simp [wordEq, hNot]
      simp [WordMap.insertLoop, WordMap.lookup?, hStored]
  | cons entry rest ih =>
      rcases entry with ⟨entryKey, entryValue⟩
      by_cases hEntrySlot : wordEq entryKey slot = true
      · have hEntryNorm :
            SolidCoreYulCore.norm entryKey =
              SolidCoreYulCore.norm slot := by
          simpa [wordEq] using hEntrySlot
        have hEntryQuery : wordEq entryKey query = false := by
          have hNot :
              ¬ SolidCoreYulCore.norm entryKey =
                SolidCoreYulCore.norm query := by
            intro hContr
            exact hOther (by simpa [hEntryNorm] using hContr)
          simp [wordEq, hNot]
        have hStored : wordEq (SolidCoreYulCore.norm slot) query = false := by
          have hNot :
              ¬ SolidCoreYulCore.norm (SolidCoreYulCore.norm slot) =
                SolidCoreYulCore.norm query := by
            simpa [norm_norm] using hOther
          simp [wordEq, hNot]
        simp [WordMap.insertLoop, WordMap.lookup?, hEntrySlot, hEntryQuery,
          hStored]
      · have hEntrySlotFalse : wordEq entryKey slot = false :=
          by
            cases h : wordEq entryKey slot <;> simp [h] at hEntrySlot ⊢
        by_cases hEntryQuery : wordEq entryKey query = true
        · simp [WordMap.insertLoop, WordMap.lookup?, hEntrySlotFalse,
            hEntryQuery]
        · have hEntryQueryFalse : wordEq entryKey query = false := by
            cases h : wordEq entryKey query <;> simp [h] at hEntryQuery ⊢
          simp [WordMap.insertLoop, WordMap.lookup?, hEntrySlotFalse,
            hEntryQueryFalse, ih]

theorem State.loadSlot_eq_of_norm
    (state : State) {left right : Word}
    (hNorm :
      SolidCoreYulCore.norm left = SolidCoreYulCore.norm right) :
    state.loadSlot left = state.loadSlot right := by
  simp [State.loadSlot, WordMap.lookup?_eq_of_norm state.storage hNorm]

theorem State.loadSlot_norm (state : State) (slot : Word) :
    SolidCoreYulCore.norm (state.loadSlot slot) = state.loadSlot slot := by
  cases hLookup : WordMap.lookup? state.storage slot with
  | none =>
      simp [State.loadSlot, hLookup, norm_zero]
  | some value =>
      have hNorm :=
        WordMap.lookup?_norm_result state.storage slot value hLookup
      simpa [State.loadSlot, hLookup] using hNorm

theorem WordMap.insertLoop_norm_value
    (storage : WordMap) (slot value : Word) :
    WordMap.insertLoop storage slot (SolidCoreYulCore.norm value) =
      WordMap.insertLoop storage slot value := by
  induction storage with
  | nil =>
      simp [WordMap.insertLoop, norm_norm]
  | cons entry rest ih =>
      rcases entry with ⟨entrySlot, entryValue⟩
      by_cases hEntrySlot : wordEq entrySlot slot = true
      · simp [WordMap.insertLoop, hEntrySlot, norm_norm]
      · have hEntrySlotFalse : wordEq entrySlot slot = false := by
          cases h : wordEq entrySlot slot <;> simp [h] at hEntrySlot ⊢
        simp [WordMap.insertLoop, hEntrySlotFalse, ih]

theorem State.storeSlot_norm_value
    (state : State) (slot value : Word) :
    state.storeSlot slot (SolidCoreYulCore.norm value) =
      state.storeSlot slot value := by
  simp [State.storeSlot, WordMap.insertLoop_norm_value]

theorem State.loadSlot_storeSlot_same
    (state : State) (slot value : Word) :
    (state.storeSlot slot value).loadSlot slot =
      SolidCoreYulCore.norm value := by
  simp [State.storeSlot, State.loadSlot,
    WordMap.lookup?_insertLoop_same]

theorem State.loadSlot_storeSlot_of_norm_eq
    (state : State) {slot query value : Word}
    (hEq :
      SolidCoreYulCore.norm slot = SolidCoreYulCore.norm query) :
    (state.storeSlot slot value).loadSlot query =
      SolidCoreYulCore.norm value := by
  have hLoadEq :
      (state.storeSlot slot value).loadSlot query =
        (state.storeSlot slot value).loadSlot slot :=
    State.loadSlot_eq_of_norm (state.storeSlot slot value) hEq.symm
  rw [hLoadEq]
  exact State.loadSlot_storeSlot_same state slot value

theorem State.loadSlot_storeSlot_other
    (state : State) {slot query value : Word}
    (hOther :
      SolidCoreYulCore.norm slot ≠ SolidCoreYulCore.norm query) :
    (state.storeSlot slot value).loadSlot query =
      state.loadSlot query := by
  simp [State.storeSlot, State.loadSlot,
    WordMap.lookup?_insertLoop_other state.storage hOther]

def storageSlotValue (slot : Word) : SolidCoreYulCore.FullYul.Value :=
  SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot)

def storageWordValue (value : Word) : SolidCoreYulCore.FullYul.Value :=
  SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm value)

def storageFieldsToMVPStorage
    (fields : List StorageField) (state : State) :
    SolidCoreYulCore.FullYul.AccountValueMap :=
  match fields with
  | [] => []
  | field :: rest =>
      SolidCoreYulCore.FullYul.writeAccountValueMap
        (storageFieldsToMVPStorage rest state)
        SolidCore.Solidity.storageAccountZero
        (storageSlotValue field.slot)
        (storageWordValue (state.loadSlot field.slot))

def State.toMVPStorage (context : Context) (state : State) :
    SolidCoreYulCore.FullYul.AccountValueMap :=
  storageFieldsToMVPStorage context.storageFields state

theorem storageFieldsToMVPStorage_lookup_of_storageSlot?
    (fields : List StorageField) (state : State)
    {name : String} {slot : Word}
    (hSlot :
      ({ Context.empty with storageFields := fields }.storageSlot? name =
        some slot)) :
    SolidCoreYulCore.FullYul.lookupAccountValueMap?
        (storageFieldsToMVPStorage fields state)
        SolidCore.Solidity.storageAccountZero
        (storageSlotValue slot) =
      some (storageWordValue (state.loadSlot slot)) := by
  induction fields with
  | nil =>
      simp [Context.storageSlot?] at hSlot
  | cons field rest ih =>
      by_cases hName : field.name = name
      · have hSlotEq : field.slot = slot := by
          simpa [Context.storageSlot?, hName] using hSlot
        subst slot
        simp [storageFieldsToMVPStorage, storageSlotValue,
          storageWordValue,
          SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same]
      · have hRest :
            ({ Context.empty with storageFields := rest }.storageSlot? name =
              some slot) := by
          simpa [Context.storageSlot?, hName] using hSlot
        by_cases hKey :
            storageSlotValue field.slot = storageSlotValue slot
        · have hNorm :
              SolidCoreYulCore.norm field.slot =
                SolidCoreYulCore.norm slot := by
            simpa [storageSlotValue] using hKey
          have hLoad :
              state.loadSlot field.slot = state.loadSlot slot :=
            State.loadSlot_eq_of_norm state hNorm
          simp [storageFieldsToMVPStorage, hKey, hLoad,
            storageWordValue,
            SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same]
        · have hLookup :
            SolidCoreYulCore.FullYul.lookupAccountValueMap?
                (SolidCoreYulCore.FullYul.writeAccountValueMap
                  (storageFieldsToMVPStorage rest state)
                  SolidCore.Solidity.storageAccountZero
                  (storageSlotValue field.slot)
                  (storageWordValue (state.loadSlot field.slot)))
                SolidCore.Solidity.storageAccountZero
                (storageSlotValue slot) =
              SolidCoreYulCore.FullYul.lookupAccountValueMap?
                (storageFieldsToMVPStorage rest state)
                SolidCore.Solidity.storageAccountZero
                (storageSlotValue slot) :=
            SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same_address_other_key
              (storageFieldsToMVPStorage rest state)
              SolidCore.Solidity.storageAccountZero
              (key := storageSlotValue field.slot)
              (query := storageSlotValue slot)
              (value := storageWordValue (state.loadSlot field.slot))
              hKey
          simpa [storageFieldsToMVPStorage, hLookup] using ih hRest

theorem State.toMVPStorage_lookup_of_storageSlot?
    (context : Context) (state : State)
    {name : String} {slot : Word}
    (hSlot : context.storageSlot? name = some slot) :
    SolidCoreYulCore.FullYul.lookupAccountValueMap?
        (state.toMVPStorage context)
        SolidCore.Solidity.storageAccountZero
        (storageSlotValue slot) =
      some (storageWordValue (state.loadSlot slot)) := by
  simpa [State.toMVPStorage] using
    storageFieldsToMVPStorage_lookup_of_storageSlot?
      context.storageFields state (name := name) (slot := slot)
      (by
        simpa [Context.storageSlot?] using hSlot)

def Runtime.toMVPStateWithContext
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value) :
    SolidCore.Solidity.MVP.State :=
  { returnValue := returnValue
    storage := runtime.state.toMVPStorage context }

def Runtime.MVPStateRelated
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (state : SolidCore.Solidity.MVP.State) : Prop :=
  state.returnValue = returnValue ∧
    ∀ {name : String} {slot : Word},
      context.storageSlot? name = some slot ->
      SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
        SolidCoreYulCore.FullYul.Value.word
          (runtime.state.loadSlot slot)

def yulStorageMap1 (slot value : Word) :
    SolidCoreYulCore.FullYul.AccountValueMap :=
  SolidCoreYulCore.FullYul.writeAccountValueMap []
    SolidCore.Solidity.storageAccountZero
    (storageSlotValue slot)
    (storageWordValue value)

theorem State.toMVPStorage_sourceStorageContext
    (name : String) (slot value : Word) :
    (sourceStorageRuntime slot value).state.toMVPStorage
        (sourceStorageContext name slot) =
      yulStorageMap1 slot value := by
  simp [State.toMVPStorage, storageFieldsToMVPStorage,
    sourceStorageContext, sourceStorageRuntime, Runtime.ofState,
    State.loadSlot, WordMap.lookup?, wordEq, yulStorageMap1,
    storageSlotValue, storageWordValue, norm_norm]

theorem Runtime.toMVPStateWithContext_sourceStorageRuntime
    (name : String) (slot value returnValue : Word) :
    Runtime.toMVPStateWithContext
        (sourceStorageContext name slot)
        (sourceStorageRuntime slot value)
        (storageWordValue returnValue) =
      { returnValue := storageWordValue returnValue
        storage := yulStorageMap1 slot value } := by
  simp [Runtime.toMVPStateWithContext,
    State.toMVPStorage_sourceStorageContext]

theorem MVPStateExpr.storage_relation_toMVPStateWithContext
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value) :
    ∀ {name : String} {slot : Word},
      context.storageSlot? name = some slot ->
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
        SolidCoreYulCore.FullYul.Value.word
          (runtime.state.loadSlot slot) := by
  intro name slot hSlot
  have hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (runtime.state.toMVPStorage context)
          SolidCore.Solidity.storageAccountZero
          (storageSlotValue slot) =
        some (storageWordValue (runtime.state.loadSlot slot)) :=
    State.toMVPStorage_lookup_of_storageSlot? context runtime.state hSlot
  have hLoadNorm :
      SolidCoreYulCore.norm (runtime.state.loadSlot slot) =
        runtime.state.loadSlot slot :=
    State.loadSlot_norm runtime.state slot
  have hLookup' :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (runtime.state.toMVPStorage context)
          SolidCore.Solidity.storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm slot)) =
        some
          (SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot)) := by
    simpa [storageSlotValue, storageWordValue, hLoadNorm] using hLookup
  simp [Runtime.toMVPStateWithContext,
    SolidCore.Solidity.MVP.StateExpr.eval,
    SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?,
    hLookup']

theorem Runtime.toMVPStateWithContext_related
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value) :
    Runtime.MVPStateRelated context runtime returnValue
      (Runtime.toMVPStateWithContext context runtime returnValue) := by
  constructor
  · rfl
  · exact
      MVPStateExpr.storage_relation_toMVPStateWithContext
        context runtime returnValue

theorem Runtime.MVPStateRelated.withReturn
    {context : Context} {runtime : Runtime}
    {oldReturnValue newReturnValue : SolidCoreYulCore.FullYul.Value}
    {state : SolidCore.Solidity.MVP.State}
    (hRelated :
      Runtime.MVPStateRelated context runtime oldReturnValue state) :
    Runtime.MVPStateRelated context runtime newReturnValue
      (state.withReturn newReturnValue) := by
  rcases hRelated with ⟨_hReturn, hStorage⟩
  constructor
  · rfl
  · intro name slot hSlot
    simpa [SolidCore.Solidity.MVP.State.withReturn] using
      hStorage hSlot

theorem Runtime.MVPStateRelated.pushScope
    {context : Context} {runtime : Runtime}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {state : SolidCore.Solidity.MVP.State}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Runtime.MVPStateRelated context runtime.pushScope returnValue state := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  constructor
  · exact hReturn
  · intro name slot hSlot
    simpa [Runtime.pushScope] using hStorage hSlot

theorem Runtime.MVPStateRelated.popScope
    {context : Context} {runtime : Runtime}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {state : SolidCore.Solidity.MVP.State}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Runtime.MVPStateRelated context (Runtime.popScope runtime)
      returnValue state := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  constructor
  · exact hReturn
  · intro name slot hSlot
    simpa [Runtime.popScope] using hStorage hSlot

theorem Runtime.MVPStateRelated.ofUncheckedContext
    {context : Context} {runtime : Runtime}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {state : SolidCore.Solidity.MVP.State}
    (hRelated :
      Runtime.MVPStateRelated { context with checked := false } runtime
        returnValue state) :
    Runtime.MVPStateRelated context runtime returnValue state := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  constructor
  · exact hReturn
  · intro name slot hSlot
    have hUncheckedSlot :
        ({ context with checked := false } : Context).storageSlot? name =
          some slot := by
      simpa [Context.storageSlot?] using hSlot
    exact hStorage hUncheckedSlot

def Result.RelatesMVPCore
    (context : Context) : Result ->
      SolidCore.Solidity.MVP.Result -> Prop
  | Result.normal runtime,
      SolidCore.Solidity.MVP.Result.normal state =>
      ∃ returnValue : SolidCoreYulCore.FullYul.Value,
        Runtime.MVPStateRelated context runtime returnValue state
  | Result.returned runtime [Value.word value],
      SolidCore.Solidity.MVP.Result.returned state =>
      Runtime.MVPStateRelated context runtime
        (SolidCoreYulCore.FullYul.Value.word value) state
  | Result.reverted runtime _,
      SolidCore.Solidity.MVP.Result.reverted state =>
      ∃ returnValue : SolidCoreYulCore.FullYul.Value,
        Runtime.MVPStateRelated context runtime returnValue state
  | _, _ => False

theorem Result.RelatesMVPCore.normal_toMVPStateWithContext
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value) :
    Result.RelatesMVPCore context
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal
        (Runtime.toMVPStateWithContext context runtime returnValue)) := by
  exact
    ⟨returnValue,
      Runtime.toMVPStateWithContext_related
        context runtime returnValue⟩

theorem Result.RelatesMVPCore.returnedWord_of_related
    {context : Context} {runtime : Runtime} {value : Word}
    {state : SolidCore.Solidity.MVP.State}
    (hRelated :
      Runtime.MVPStateRelated context runtime
        (SolidCoreYulCore.FullYul.Value.word value) state) :
    Result.RelatesMVPCore context
      (Result.returned runtime [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned state) := by
  exact hRelated

theorem Result.RelatesMVPCore.returnedWord_toMVPStateWithContext
    (context : Context) (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (value : Word) :
    Result.RelatesMVPCore context
      (Result.returned runtime [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned
        ((Runtime.toMVPStateWithContext context runtime returnValue).withReturn
          (SolidCoreYulCore.FullYul.Value.word value))) := by
  exact
    Result.RelatesMVPCore.returnedWord_of_related
      ((Runtime.toMVPStateWithContext_related
          context runtime returnValue).withReturn)

theorem Result.RelatesMVPCore.reverted_of_related
    {context : Context} {runtime : Runtime} {data : RevertData}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Result.RelatesMVPCore context
      (Result.reverted runtime data)
      (SolidCore.Solidity.MVP.Result.reverted state) := by
  exact ⟨returnValue, hRelated⟩

theorem MVPStateExpr.storage_eval_sourceStorageContext
    (name : String) (slot storedValue returnValue : Word) :
    SolidCore.Solidity.MVP.StateExpr.eval
        (Runtime.toMVPStateWithContext
          (sourceStorageContext name slot)
          (sourceStorageRuntime slot storedValue)
          (storageWordValue returnValue))
        (SolidCore.Solidity.MVP.StateExpr.load
          (SolidCore.Solidity.Expr.lit slot)) =
      storageWordValue storedValue := by
  rw [Runtime.toMVPStateWithContext_sourceStorageRuntime]
  simp [
    SolidCore.Solidity.MVP.StateExpr.eval,
    SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?,
    yulStorageMap1, storageSlotValue, storageWordValue,
    SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same,
    norm_norm]

theorem MVPStateExpr.storage_relation_sourceStorageContext
    (fieldName : String) (slot storedValue returnValue : Word) :
    ∀ {name : String} {slot' : Word},
      (sourceStorageContext fieldName slot).storageSlot? name = some slot' ->
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext
            (sourceStorageContext fieldName slot)
            (sourceStorageRuntime slot storedValue)
            (storageWordValue returnValue))
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot')) =
        SolidCoreYulCore.FullYul.Value.word
          ((sourceStorageRuntime slot storedValue).state.loadSlot slot') := by
  intro name slot' hSlot
  have hSlotEq : slot' = slot := by
    by_cases hName : fieldName = name
    · subst name
      simp [sourceStorageContext, Context.storageSlot?] at hSlot
      exact hSlot.symm
    · simp [sourceStorageContext, Context.storageSlot?, hName] at hSlot
  subst slot'
  simpa [sourceStorageRuntime, Runtime.ofState, State.loadSlot,
    WordMap.lookup?, wordEq, storageWordValue, norm_norm] using
    MVPStateExpr.storage_eval_sourceStorageContext
      fieldName slot storedValue returnValue

theorem MVPState_store_load_same
    (state : SolidCore.Solidity.MVP.State) (slot value : Word) :
    SolidCore.Solidity.MVP.State.load
        (SolidCore.Solidity.MVP.State.store state
          (SolidCore.Solidity.Expr.lit slot)
          (SolidCore.Solidity.Expr.lit value))
        (SolidCore.Solidity.Expr.lit slot) =
      storageWordValue value := by
  have hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (SolidCore.Solidity.storageWrite state.storage
            (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot))
            (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm value)))
          SolidCore.Solidity.storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot)) =
        some
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm value)) := by
    simpa [SolidCore.Solidity.storageWrite] using
      SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same
        state.storage SolidCore.Solidity.storageAccountZero
        (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot))
        (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm value))
  simp [SolidCore.Solidity.MVP.State.store,
    SolidCore.Solidity.MVP.State.storeValue,
    SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?,
    storageSlotValue, storageWordValue, hLookup, norm_norm]

theorem MVPState_storeValue_load_same
    (state : SolidCore.Solidity.MVP.State) (slot : Word)
    (value : SolidCoreYulCore.FullYul.Value) :
    SolidCore.Solidity.MVP.State.load
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot) value)
        (SolidCore.Solidity.Expr.lit slot) =
      value := by
  have hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (SolidCore.Solidity.storageWrite state.storage
            (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot))
            value)
          SolidCore.Solidity.storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot)) =
        some value := by
    simpa [SolidCore.Solidity.storageWrite] using
      SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same
        state.storage SolidCore.Solidity.storageAccountZero
        (SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot))
        value
  simp [SolidCore.Solidity.MVP.State.storeValue,
    SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?,
    hLookup, norm_norm]

theorem MVPState_load_eq_of_norm
    (state : SolidCore.Solidity.MVP.State) {left right : Word}
    (hNorm :
      SolidCoreYulCore.norm left = SolidCoreYulCore.norm right) :
    SolidCore.Solidity.MVP.State.load state
        (SolidCore.Solidity.Expr.lit left) =
      SolidCore.Solidity.MVP.State.load state
        (SolidCore.Solidity.Expr.lit right) := by
  simp [SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?, hNorm]

theorem MVPState_storeValue_load_of_norm_eq
    (state : SolidCore.Solidity.MVP.State)
    {slot query : Word} (value : SolidCoreYulCore.FullYul.Value)
    (hEq :
      SolidCoreYulCore.norm slot = SolidCoreYulCore.norm query) :
    SolidCore.Solidity.MVP.State.load
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot) value)
        (SolidCore.Solidity.Expr.lit query) =
      value := by
  have hLoadEq :=
    MVPState_load_eq_of_norm
      (SolidCore.Solidity.MVP.State.storeValue state
        (SolidCore.Solidity.Expr.lit slot) value)
      (left := query) (right := slot) hEq.symm
  rw [hLoadEq]
  exact MVPState_storeValue_load_same state slot value

theorem MVPState_storeValue_load_other
    (state : SolidCore.Solidity.MVP.State)
    {slot query : Word} (value : SolidCoreYulCore.FullYul.Value)
    (hOther :
      SolidCoreYulCore.norm slot ≠ SolidCoreYulCore.norm query) :
    SolidCore.Solidity.MVP.State.load
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot) value)
        (SolidCore.Solidity.Expr.lit query) =
      SolidCore.Solidity.MVP.State.load state
        (SolidCore.Solidity.Expr.lit query) := by
  have hKey :
      SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm slot) ≠
        SolidCoreYulCore.FullYul.Value.word (SolidCoreYulCore.norm query) := by
    intro hContr
    injection hContr with hNorm
    exact hOther hNorm
  have hLookup :
      SolidCoreYulCore.FullYul.lookupAccountValueMap?
          (SolidCore.Solidity.storageWrite state.storage
            (SolidCoreYulCore.FullYul.Value.word
              (SolidCoreYulCore.norm slot))
            value)
          SolidCore.Solidity.storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm query)) =
        SolidCoreYulCore.FullYul.lookupAccountValueMap?
          state.storage
          SolidCore.Solidity.storageAccountZero
          (SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm query)) := by
    simpa [SolidCore.Solidity.storageWrite] using
      SolidCoreYulCore.FullYul.lookupAccountValueMap_write_same_address_other_key
        state.storage SolidCore.Solidity.storageAccountZero
        (key :=
          SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm slot))
        (query :=
          SolidCoreYulCore.FullYul.Value.word
            (SolidCoreYulCore.norm query))
        (value := value)
        hKey
  simp [SolidCore.Solidity.MVP.State.storeValue,
    SolidCore.Solidity.MVP.State.load,
    SolidCore.Solidity.Expr.eval,
    SolidCore.Solidity.storageLookup?,
    hLookup, norm_norm]

theorem Runtime.MVPStateRelated.storeSlot_storeValue
    {context : Context} {runtime : Runtime}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {state : SolidCore.Solidity.MVP.State}
    {slot value : Word}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hValueNorm : SolidCoreYulCore.norm value = value) :
    Runtime.MVPStateRelated context
      { runtime with state := runtime.state.storeSlot slot value }
      returnValue
      (SolidCore.Solidity.MVP.State.storeValue state
        (SolidCore.Solidity.Expr.lit slot)
        (SolidCoreYulCore.FullYul.Value.word value)) := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  constructor
  · simpa [SolidCore.Solidity.MVP.State.storeValue] using hReturn
  · intro name query hSlot
    by_cases hEq :
        SolidCoreYulCore.norm slot = SolidCoreYulCore.norm query
    · have hMVP :=
        MVPState_storeValue_load_of_norm_eq state
          (value := SolidCoreYulCore.FullYul.Value.word value)
          (slot := slot) (query := query) hEq
      have hSource :=
        State.loadSlot_storeSlot_of_norm_eq runtime.state
          (slot := slot) (query := query) (value := value) hEq
      have hSourceValue :
          SolidCoreYulCore.FullYul.Value.word value =
            SolidCoreYulCore.FullYul.Value.word
              ({ runtime with
                state := runtime.state.storeSlot slot value }.state.loadSlot
                  query) := by
        rw [hSource, hValueNorm]
      rw [show
        SolidCore.Solidity.MVP.StateExpr.eval
            (SolidCore.Solidity.MVP.State.storeValue state
              (SolidCore.Solidity.Expr.lit slot)
              (SolidCoreYulCore.FullYul.Value.word value))
            (SolidCore.Solidity.MVP.StateExpr.load
              (SolidCore.Solidity.Expr.lit query)) =
          SolidCoreYulCore.FullYul.Value.word value by
            simpa [SolidCore.Solidity.MVP.StateExpr.eval] using hMVP]
      exact hSourceValue
    · have hMVP :=
        MVPState_storeValue_load_other state
          (value := SolidCoreYulCore.FullYul.Value.word value)
          (slot := slot) (query := query) hEq
      have hSource :=
        State.loadSlot_storeSlot_other runtime.state
          (slot := slot) (query := query) (value := value) hEq
      have hSourceValue :
          SolidCoreYulCore.FullYul.Value.word
              (runtime.state.loadSlot query) =
            SolidCoreYulCore.FullYul.Value.word
              ({ runtime with
                state := runtime.state.storeSlot slot value }.state.loadSlot
                  query) := by
        rw [hSource]
      rw [show
        SolidCore.Solidity.MVP.StateExpr.eval
            (SolidCore.Solidity.MVP.State.storeValue state
              (SolidCore.Solidity.Expr.lit slot)
              (SolidCoreYulCore.FullYul.Value.word value))
            (SolidCore.Solidity.MVP.StateExpr.load
              (SolidCore.Solidity.Expr.lit query)) =
          SolidCore.Solidity.MVP.StateExpr.eval state
            (SolidCore.Solidity.MVP.StateExpr.load
              (SolidCore.Solidity.Expr.lit query)) by
            simpa [SolidCore.Solidity.MVP.StateExpr.eval] using hMVP]
      rw [hStorage (name := name) (slot := query) hSlot]
      exact hSourceValue

def Expr.toMVPStateUnchecked? (context : Context) (expr : Expr) :
    Option MVPStateExpr :=
  match expr.toLegacyUnchecked? with
  | some pureExpr =>
      some (SolidCore.Solidity.MVP.StateExpr.pure pureExpr)
  | none =>
      match expr with
      | Expr.storage name =>
          match context.storageSlot? name with
          | some slot =>
              some
                (SolidCore.Solidity.MVP.StateExpr.load
                  (SolidCore.Solidity.Expr.lit slot))
          | none => none
      | Expr.unary op inner =>
          match inner.toMVPStateUnchecked? context with
          | some innerState =>
              match op with
              | UnaryOp.bitNot => some (SolidCore.Solidity.MVP.StateExpr.bitNot innerState)
              | UnaryOp.logicalNot =>
                  some (SolidCore.Solidity.MVP.StateExpr.iszero innerState)
              | UnaryOp.neg => none
          | none => none
      | Expr.binary op lhs rhs =>
          match lhs.toMVPStateUnchecked? context,
              rhs.toMVPStateUnchecked? context with
          | some lhsState, some rhsState =>
              match op with
              | BinaryOp.add =>
                  some (SolidCore.Solidity.MVP.StateExpr.add lhsState rhsState)
              | BinaryOp.sub =>
                  some (SolidCore.Solidity.MVP.StateExpr.sub lhsState rhsState)
              | BinaryOp.mul =>
                  some (SolidCore.Solidity.MVP.StateExpr.mul lhsState rhsState)
              | BinaryOp.bitAnd =>
                  some (SolidCore.Solidity.MVP.StateExpr.bitAnd lhsState rhsState)
              | BinaryOp.bitOr =>
                  some (SolidCore.Solidity.MVP.StateExpr.bitOr lhsState rhsState)
              | BinaryOp.bitXor =>
                  some (SolidCore.Solidity.MVP.StateExpr.bitXor lhsState rhsState)
              | BinaryOp.lt =>
                  some (SolidCore.Solidity.MVP.StateExpr.lt lhsState rhsState)
              | BinaryOp.gt =>
                  some (SolidCore.Solidity.MVP.StateExpr.gt lhsState rhsState)
              | BinaryOp.eq =>
                  some (SolidCore.Solidity.MVP.StateExpr.eq lhsState rhsState)
              | _ => none
          | _, _ => none
      | _ => none

theorem Expr.toMVPStateUnchecked?_of_toLegacyUnchecked?
    (context : Context) {expr : Expr} {legacy : LegacyExpr}
    (hLegacy : expr.toLegacyUnchecked? = some legacy) :
    expr.toMVPStateUnchecked? context =
      some (SolidCore.Solidity.MVP.StateExpr.pure legacy) := by
  unfold Expr.toMVPStateUnchecked?
  rw [hLegacy]

theorem Expr.toMVPStateUnchecked?_storage_sourceStorageContext
    (name : String) (slot : Word) :
    (Expr.storage name).toMVPStateUnchecked?
        (sourceStorageContext name slot) =
      some
        (SolidCore.Solidity.MVP.StateExpr.load
          (SolidCore.Solidity.Expr.lit slot)) := by
  simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?,
    sourceStorageContext, Context.storageSlot?]

def BinaryOp.toMVPStateExpr? :
    BinaryOp -> Option (MVPStateExpr -> MVPStateExpr -> MVPStateExpr)
  | BinaryOp.add => some SolidCore.Solidity.MVP.StateExpr.add
  | BinaryOp.sub => some SolidCore.Solidity.MVP.StateExpr.sub
  | BinaryOp.mul => some SolidCore.Solidity.MVP.StateExpr.mul
  | BinaryOp.bitAnd => some SolidCore.Solidity.MVP.StateExpr.bitAnd
  | BinaryOp.bitOr => some SolidCore.Solidity.MVP.StateExpr.bitOr
  | BinaryOp.bitXor => some SolidCore.Solidity.MVP.StateExpr.bitXor
  | BinaryOp.lt => some SolidCore.Solidity.MVP.StateExpr.lt
  | BinaryOp.gt => some SolidCore.Solidity.MVP.StateExpr.gt
  | BinaryOp.eq => some SolidCore.Solidity.MVP.StateExpr.eq
  | _ => none

def BinaryOp.evalMVPWord? : BinaryOp -> Option (Word -> Word -> Word)
  | BinaryOp.add => some SolidCoreYulCore.addWord
  | BinaryOp.sub => some SolidCoreYulCore.subWord
  | BinaryOp.mul => some SolidCoreYulCore.mulWord
  | BinaryOp.bitAnd => some SolidCoreYulCore.andWord
  | BinaryOp.bitOr => some SolidCoreYulCore.orWord
  | BinaryOp.bitXor => some SolidCoreYulCore.xorWord
  | BinaryOp.lt => some SolidCoreYulCore.ltWord
  | BinaryOp.gt => some SolidCoreYulCore.gtWord
  | BinaryOp.eq => some SolidCoreYulCore.eqWord
  | _ => none

theorem BinaryOp.toMVPStateExpr?_eq_some_iff_evalMVPWord?
    {op : BinaryOp} :
    (∃ mk, op.toMVPStateExpr? = some mk) ↔
      (∃ eval, op.evalMVPWord? = some eval) := by
  cases op <;> simp [BinaryOp.toMVPStateExpr?, BinaryOp.evalMVPWord?]

theorem BinaryOp.apply_evalMVPWord?
    {op : BinaryOp} {eval : Word -> Word -> Word}
    (hOp : op.evalMVPWord? = some eval)
    (lhs rhs : Word) :
    BinaryOp.apply false op (Value.word lhs) (Value.word rhs) =
      Except.ok (Value.word (eval lhs rhs)) := by
  cases op <;> simp [BinaryOp.evalMVPWord?] at hOp <;>
    try subst eval <;>
    simp [BinaryOp.apply, BinaryOp.applyWord, checkedAdd, checkedSub,
      checkedMul, Value.expectWord, wordEq, boolWord,
      SolidCoreYulCore.eqWord, addWord_norm_args, subWord_norm_args,
      mulWord_norm_args, andWord_norm_args, orWord_norm_args,
      xorWord_norm_args, ltWord_norm_args, gtWord_norm_args,
      norm_norm, Bind.bind, Except.bind]

theorem BinaryOp.evalMVPWord?_norm_args
    {op : BinaryOp} {eval : Word -> Word -> Word}
    (hOp : op.evalMVPWord? = some eval)
    (lhs rhs : Word) :
    eval (SolidCoreYulCore.norm lhs) (SolidCoreYulCore.norm rhs) =
      eval lhs rhs := by
  cases op <;> simp [BinaryOp.evalMVPWord?] at hOp
  all_goals
    try contradiction
  all_goals
    subst eval
    simp [addWord_norm_args, subWord_norm_args, mulWord_norm_args,
      andWord_norm_args, orWord_norm_args, xorWord_norm_args,
      ltWord_norm_args, gtWord_norm_args, eqWord_norm_args]

theorem BinaryOp.evalMVPWord?_norm_result
    {op : BinaryOp} {eval : Word -> Word -> Word}
    (hOp : op.evalMVPWord? = some eval)
    (lhs rhs : Word) :
    eval lhs rhs =
      SolidCoreYulCore.norm (eval lhs rhs) := by
  cases op <;> simp [BinaryOp.evalMVPWord?] at hOp
  · subst eval
    exact addWord_norm_result lhs rhs
  · subst eval
    exact subWord_norm_result lhs rhs
  · subst eval
    exact mulWord_norm_result lhs rhs
  · subst eval
    exact andWord_norm_result lhs rhs
  · subst eval
    exact orWord_norm_result lhs rhs
  · subst eval
    exact xorWord_norm_result lhs rhs
  · subst eval
    exact ltWord_norm_result lhs rhs
  · subst eval
    exact gtWord_norm_result lhs rhs
  · subst eval
    exact eqWord_norm_result lhs rhs

theorem BinaryOp.toMVPStateExpr?_evalMVPWord?_eval
    {op : BinaryOp}
    {mk : MVPStateExpr -> MVPStateExpr -> MVPStateExpr}
    {eval : Word -> Word -> Word}
    (hMk : op.toMVPStateExpr? = some mk)
    (hEval : op.evalMVPWord? = some eval)
    (state : SolidCore.Solidity.MVP.State)
    {lhsExpr rhsExpr : MVPStateExpr}
    {lhs rhs : Word}
    (hLhs :
      SolidCore.Solidity.MVP.StateExpr.eval state lhsExpr =
        SolidCoreYulCore.FullYul.Value.word lhs)
    (hRhs :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsExpr =
        SolidCoreYulCore.FullYul.Value.word rhs) :
    SolidCore.Solidity.MVP.StateExpr.eval state (mk lhsExpr rhsExpr) =
      SolidCoreYulCore.FullYul.Value.word (eval lhs rhs) := by
  cases op <;>
    simp [BinaryOp.toMVPStateExpr?, BinaryOp.evalMVPWord?]
      at hMk hEval
  all_goals
    try contradiction
  all_goals
    subst mk
    subst eval
    simp [SolidCore.Solidity.MVP.StateExpr.eval, hLhs, hRhs,
      Core.Storage.addValue, SolidCore.Solidity.MVP.StateExpr.subValue,
      SolidCore.Solidity.MVP.StateExpr.mulValue,
      SolidCore.Solidity.MVP.StateExpr.andValue,
      SolidCore.Solidity.MVP.StateExpr.orValue,
      SolidCore.Solidity.MVP.StateExpr.xorValue,
      SolidCore.Solidity.MVP.StateExpr.ltValue,
      SolidCore.Solidity.MVP.StateExpr.gtValue,
      SolidCore.Solidity.MVP.StateExpr.eqValue]

theorem Expr.toMVPStateUnchecked?_eval_runtime_of_storage
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr : expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word,
      expr.eval context runtime = Except.ok (Value.word value) ∧
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  induction expr generalizing stateExpr with
  | word value =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
      subst stateExpr
      exact ⟨SolidCoreYulCore.norm value, by simp [Expr.eval, normWord],
        by simp [SolidCore.Solidity.MVP.StateExpr.eval,
          SolidCore.Solidity.Expr.eval]⟩
  | var name =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | storage name =>
      cases hSlot : context.storageSlot? name with
      | none =>
          simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?,
            hSlot] at hExpr
      | some slot =>
          simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?,
            hSlot] at hExpr
          subst stateExpr
          exact
            ⟨runtime.state.loadSlot slot,
              by simp [Expr.eval, Runtime.loadStorageField, hSlot],
              hStorage hSlot⟩
  | length inner ih =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | index base idx base_ih idx_ih =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | unary op inner ih =>
      cases hLegacy : (Expr.unary op inner).toLegacyUnchecked? with
      | some legacy =>
          simp [Expr.toMVPStateUnchecked?, hLegacy] at hExpr
          subst stateExpr
          exact
            ⟨legacy.eval,
              Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
                context hChecked hLegacy runtime,
              by simp [SolidCore.Solidity.MVP.StateExpr.eval]⟩
      | none =>
          cases hInner : inner.toMVPStateUnchecked? context with
          | none =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hInner] at hExpr
          | some innerState =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hInner] at hExpr
              · subst stateExpr
                rcases ih hInner with ⟨value, hSource, hMVP⟩
                exact
                  ⟨SolidCoreYulCore.notWord value,
                      by
                        simp [Expr.eval, hSource, UnaryOp.apply,
                          Value.expectWord, hChecked, notWord_norm_arg,
                          Bind.bind, Except.bind],
                    by
                      simp [SolidCore.Solidity.MVP.StateExpr.eval, hMVP,
                        SolidCore.Solidity.MVP.StateExpr.notValue]⟩
              · subst stateExpr
                rcases ih hInner with ⟨value, hSource, hMVP⟩
                exact
                  ⟨SolidCoreYulCore.iszeroWord value,
                      by
                        simp [Expr.eval, hSource, UnaryOp.apply,
                          Value.expectWord, hChecked,
                          boolWord_not_truthy_eq_iszeroWord,
                          iszeroWord_norm_arg, Bind.bind, Except.bind],
                    by
                      simp [SolidCore.Solidity.MVP.StateExpr.eval, hMVP,
                        SolidCore.Solidity.MVP.StateExpr.iszeroValue]⟩
  | binary op lhs rhs lhs_ih rhs_ih =>
      cases hLegacy : (Expr.binary op lhs rhs).toLegacyUnchecked? with
      | some legacy =>
          simp [Expr.toMVPStateUnchecked?, hLegacy] at hExpr
          subst stateExpr
          exact
            ⟨legacy.eval,
              Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
                context hChecked hLegacy runtime,
              by simp [SolidCore.Solidity.MVP.StateExpr.eval]⟩
      | none =>
          cases hLhs : lhs.toMVPStateUnchecked? context with
          | none =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs] at hExpr
          | some lhsState =>
              cases hRhs : rhs.toMVPStateUnchecked? context with
              | none =>
                  cases op <;>
                    simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs, hRhs]
                      at hExpr
              | some rhsState =>
                  rcases lhs_ih hLhs with
                    ⟨lhsValue, hLhsSource, hLhsMVP⟩
                  rcases rhs_ih hRhs with
                    ⟨rhsValue, hRhsSource, hRhsMVP⟩
                  cases op <;>
                    simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs, hRhs]
                      at hExpr
                  all_goals
                    try contradiction
                  all_goals
                    subst stateExpr
                    simp [Expr.eval, hLhsSource, hRhsSource,
                        BinaryOp.apply, BinaryOp.applyWord, checkedAdd,
                        checkedSub, checkedMul, Value.expectWord, hChecked,
                        Bind.bind, Except.bind, addWord_norm_args,
                        subWord_norm_args, mulWord_norm_args,
                        andWord_norm_args, orWord_norm_args,
                        xorWord_norm_args, ltWord_norm_args,
                        gtWord_norm_args,
                        SolidCore.Solidity.MVP.StateExpr.eval, hLhsMVP,
                      hRhsMVP, Core.Storage.addValue,
                      SolidCore.Solidity.MVP.StateExpr.subValue,
                      SolidCore.Solidity.MVP.StateExpr.mulValue,
                      SolidCore.Solidity.MVP.StateExpr.andValue,
                      SolidCore.Solidity.MVP.StateExpr.orValue,
                      SolidCore.Solidity.MVP.StateExpr.xorValue,
                      SolidCore.Solidity.MVP.StateExpr.ltValue,
                      SolidCore.Solidity.MVP.StateExpr.gtValue,
                      SolidCore.Solidity.MVP.StateExpr.eqValue,
                      wordEq, boolWord, SolidCoreYulCore.eqWord]

theorem Expr.toMVPStateUnchecked?_eval_runtime_of_storage_result_norm
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr : expr.toMVPStateUnchecked? context = some stateExpr)
    {value : Word}
    (hEval : expr.eval context runtime = Except.ok (Value.word value)) :
    SolidCoreYulCore.norm value = value := by
  induction expr generalizing stateExpr value with
  | word literal =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
      subst stateExpr
      simp [Expr.eval, normWord] at hEval
      subst value
      exact norm_norm literal
  | var name =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | storage name =>
      cases hSlot : context.storageSlot? name with
      | none =>
          simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?,
            hSlot] at hExpr
      | some slot =>
          simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?,
            hSlot] at hExpr
          subst stateExpr
          simp [Expr.eval, Runtime.loadStorageField, hSlot] at hEval
          subst value
          exact State.loadSlot_norm runtime.state slot
  | length inner =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | index base idx =>
      simp [Expr.toMVPStateUnchecked?, Expr.toLegacyUnchecked?] at hExpr
  | unary op inner =>
      cases hLegacy : (Expr.unary op inner).toLegacyUnchecked? with
      | some legacy =>
          have hLegacyEval :=
            Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
              context hChecked hLegacy runtime
          rw [hLegacyEval] at hEval
          cases hEval
          exact Expr.toLegacyUnchecked?_eval_norm hLegacy
      | none =>
          cases hInner : inner.toMVPStateUnchecked? context with
          | none =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hInner] at hExpr
          | some innerState =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hInner] at hExpr
              · subst stateExpr
                rcases
                    Expr.toMVPStateUnchecked?_eval_runtime_of_storage
                      hChecked hStorage hInner with
                  ⟨innerValue, hInnerSource, _hInnerMVP⟩
                simp [Expr.eval, hInnerSource, UnaryOp.apply,
                  Value.expectWord, hChecked, notWord_norm_arg,
                  Bind.bind, Except.bind] at hEval
                subst value
                exact norm_notWord_result innerValue
              · subst stateExpr
                rcases
                    Expr.toMVPStateUnchecked?_eval_runtime_of_storage
                      hChecked hStorage hInner with
                  ⟨innerValue, hInnerSource, _hInnerMVP⟩
                simp [Expr.eval, hInnerSource, UnaryOp.apply,
                  Value.expectWord, hChecked,
                  boolWord_not_truthy_eq_iszeroWord,
                  iszeroWord_norm_arg, Bind.bind, Except.bind] at hEval
                subst value
                exact norm_iszeroWord_result innerValue
  | binary op lhs rhs =>
      cases hLegacy : (Expr.binary op lhs rhs).toLegacyUnchecked? with
      | some legacy =>
          have hLegacyEval :=
            Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
              context hChecked hLegacy runtime
          rw [hLegacyEval] at hEval
          cases hEval
          exact Expr.toLegacyUnchecked?_eval_norm hLegacy
      | none =>
          cases hLhs : lhs.toMVPStateUnchecked? context with
          | none =>
              cases op <;>
                simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs] at hExpr
          | some lhsState =>
              cases hRhs : rhs.toMVPStateUnchecked? context with
              | none =>
                  cases op <;>
                    simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs, hRhs]
                      at hExpr
              | some rhsState =>
                  rcases
                      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
                        hChecked hStorage hLhs with
                    ⟨lhsValue, hLhsSource, _hLhsMVP⟩
                  rcases
                      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
                        hChecked hStorage hRhs with
                    ⟨rhsValue, hRhsSource, _hRhsMVP⟩
                  cases hOpState : op.toMVPStateExpr? with
                  | none =>
                      cases op <;>
                        simp [Expr.toMVPStateUnchecked?, hLegacy, hLhs,
                          hRhs, BinaryOp.toMVPStateExpr?] at hExpr hOpState
                  | some mk =>
                      have hEvalExists :
                          ∃ eval, op.evalMVPWord? = some eval :=
                        (BinaryOp.toMVPStateExpr?_eq_some_iff_evalMVPWord?
                          (op := op)).mp ⟨mk, hOpState⟩
                      rcases hEvalExists with ⟨eval, hOpEval⟩
                      have hApply :=
                        BinaryOp.apply_evalMVPWord?
                          hOpEval lhsValue rhsValue
                      cases op <;>
                        simp [BinaryOp.evalMVPWord?,
                          BinaryOp.toMVPStateExpr?] at hOpEval hOpState
                      all_goals
                        subst eval
                        simp [Expr.eval, hLhsSource, hRhsSource, hChecked,
                          hApply, Bind.bind, Except.bind] at hEval
                        cases hEval
                      · exact (addWord_norm_result lhsValue rhsValue).symm
                      · exact (subWord_norm_result lhsValue rhsValue).symm
                      · exact (mulWord_norm_result lhsValue rhsValue).symm
                      · exact (andWord_norm_result lhsValue rhsValue).symm
                      · exact (orWord_norm_result lhsValue rhsValue).symm
                      · exact (xorWord_norm_result lhsValue rhsValue).symm
                      · exact (ltWord_norm_result lhsValue rhsValue).symm
                      · exact (gtWord_norm_result lhsValue rhsValue).symm
                      · exact (eqWord_norm_result lhsValue rhsValue).symm

theorem Expr.toMVPStateUnchecked?_eval_runtime_of_storage_norm
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr : expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word,
      expr.eval context runtime = Except.ok (Value.word value) ∧
      SolidCoreYulCore.norm value = value ∧
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
        hChecked hStorage hExpr with
    ⟨value, hSource, hMVP⟩
  exact
    ⟨value, hSource,
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage_result_norm
        hChecked hStorage hExpr hSource,
      hMVP⟩

theorem Expr.toMVPStateUnchecked?_eval_runtime_toMVPStateWithContext
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr : expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word,
      expr.eval context runtime = Except.ok (Value.word value) ∧
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  exact
    Expr.toMVPStateUnchecked?_eval_runtime_of_storage
      hChecked
      (MVPStateExpr.storage_relation_toMVPStateWithContext
        context runtime returnValue)
      hExpr

theorem Expr.toMVPStateUnchecked?_eval_runtime_toMVPStateWithContext_norm
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr : expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word,
      expr.eval context runtime = Except.ok (Value.word value) ∧
      SolidCoreYulCore.norm value = value ∧
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  exact
    Expr.toMVPStateUnchecked?_eval_runtime_of_storage_norm
      hChecked
      (MVPStateExpr.storage_relation_toMVPStateWithContext
        context runtime returnValue)
      hExpr

theorem Expr.toMVPStateUnchecked?_eval_sourceStorageContext
    (fieldName : String) (slot storedValue returnValue : Word)
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr :
      expr.toMVPStateUnchecked? (sourceStorageContext fieldName slot) =
        some stateExpr) :
    ∃ value : Word,
      expr.eval (sourceStorageContext fieldName slot)
          (sourceStorageRuntime slot storedValue) =
        Except.ok (Value.word value) ∧
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext
            (sourceStorageContext fieldName slot)
            (sourceStorageRuntime slot storedValue)
            (storageWordValue returnValue))
          stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  exact
    Expr.toMVPStateUnchecked?_eval_runtime_toMVPStateWithContext
      (context := sourceStorageContext fieldName slot)
      rfl
      (runtime := sourceStorageRuntime slot storedValue)
      (returnValue := storageWordValue returnValue)
      hExpr

theorem Expr.toMVPStateUnchecked?_pure_eval_runtime_of_checked_false
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    {expr : Expr} {legacy : LegacyExpr}
    (hLegacy : expr.toLegacyUnchecked? = some legacy) :
    ∃ stateExpr : MVPStateExpr, ∃ value : Word,
      expr.toMVPStateUnchecked? context = some stateExpr ∧
      expr.eval context runtime = Except.ok (Value.word value) ∧
      SolidCore.Solidity.MVP.StateExpr.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          stateExpr =
        SolidCoreYulCore.FullYul.Value.word value := by
  refine
    ⟨SolidCore.Solidity.MVP.StateExpr.pure legacy, legacy.eval, ?_, ?_, ?_⟩
  · exact Expr.toMVPStateUnchecked?_of_toLegacyUnchecked? context hLegacy
  · exact
      Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
        context hChecked hLegacy runtime
  · simp [SolidCore.Solidity.MVP.StateExpr.eval]

mutual

def Stmt.toMVPCoreUnchecked? (context : Context) :
    Stmt -> Option MVPCoreStmt
  | Stmt.skip => some SolidCore.Solidity.MVP.Stmt.skip
  | Stmt.block body =>
      Stmt.listToMVPCoreUnchecked? context body
  | Stmt.assign (LValue.storage name) expr =>
      match context.storageSlot? name, expr.toMVPStateUnchecked? context with
      | some slot, some value =>
          some
            (SolidCore.Solidity.MVP.Stmt.storeStateExpr
              (SolidCore.Solidity.Expr.lit slot) value)
      | _, _ => none
  | Stmt.assignOp (LValue.storage name) op expr =>
      match context.storageSlot? name, expr.toMVPStateUnchecked? context,
          op.toMVPStateExpr? with
      | some slot, some value, some mk =>
          some
            (SolidCore.Solidity.MVP.Stmt.storeStateExpr
              (SolidCore.Solidity.Expr.lit slot)
              (mk
                (SolidCore.Solidity.MVP.StateExpr.load
                  (SolidCore.Solidity.Expr.lit slot))
                value))
      | _, _, _ => none
  | Stmt.ifElse cond thenBranch elseBranch =>
      match cond.toLegacyUnchecked?,
          thenBranch.toMVPCoreUnchecked? context,
          elseBranch.toMVPCoreUnchecked? context with
      | some discr, some thenCore, some elseCore =>
          some
            (SolidCore.Solidity.MVP.Stmt.switchCases discr
              [(0, elseCore)] thenCore)
      | _, _, _ => none
  | Stmt.switch discr cases defaultBranch =>
      match discr.toLegacyUnchecked?,
          Stmt.switchCasesToMVPCoreUnchecked? context cases,
          Stmt.optionalToMVPCoreUnchecked? context defaultBranch with
      | some discrCore, some casesCore, some defaultCore =>
          some
            (SolidCore.Solidity.MVP.Stmt.switchCases discrCore
              casesCore defaultCore)
      | _, _, _ => none
  | Stmt.returnValues [expr] =>
      match expr.toMVPStateUnchecked? context with
      | some stateExpr =>
          some (SolidCore.Solidity.MVP.Stmt.returnStateExpr stateExpr)
      | none => none
  | Stmt.revert _ exprs =>
      match Expr.listToLegacyUnchecked? exprs with
      | some _ => some SolidCore.Solidity.MVP.Stmt.revert
      | none => none
  | Stmt.emitEvent _ _ => none
  | Stmt.unchecked body =>
      body.toMVPCoreUnchecked? { context with checked := false }
  | _ => none

def Stmt.listToMVPCoreUnchecked? (context : Context) :
    List Stmt -> Option MVPCoreStmt
  | [] => some SolidCore.Solidity.MVP.Stmt.skip
  | stmt :: rest =>
      match stmt.toMVPCoreUnchecked? context,
          Stmt.listToMVPCoreUnchecked? context rest with
      | some first, some second =>
          some (SolidCore.Solidity.MVP.Stmt.seq first second)
      | _, _ => none

def Stmt.optionalToMVPCoreUnchecked? (context : Context) :
    Option Stmt -> Option MVPCoreStmt
  | none => some SolidCore.Solidity.MVP.Stmt.skip
  | some stmt => stmt.toMVPCoreUnchecked? context

def Stmt.switchCasesToMVPCoreUnchecked? (context : Context) :
    List (Word × Stmt) -> Option (List (Word × MVPCoreStmt))
  | [] => some []
  | (label, branch) :: rest =>
      match branch.toMVPCoreUnchecked? context,
          Stmt.switchCasesToMVPCoreUnchecked? context rest with
      | some branchCore, some restCore =>
          some ((label, branchCore) :: restCore)
      | _, _ => none

end

def Stmt.toMVPCoreProgramUnchecked? (context : Context)
    (stmt : Stmt) : Option MVPCoreProgram :=
  match stmt.toMVPCoreUnchecked? context with
  | some body => some { body := body }
  | none => none

def Stmt.toFullYulViaMVPCoreUnchecked? (context : Context)
    (stmt : Stmt) : Option YulStmt :=
  match stmt.toMVPCoreProgramUnchecked? context with
  | some program =>
      some (SolidCore.Solidity.MVP.compileSourceProgramStmt program)
  | none => none

def Stmt.toFullYulViaMVPCoreUncheckedFuel? (context : Context)
    (stmt : Stmt) : Option Nat :=
  match stmt.toMVPCoreProgramUnchecked? context with
  | some program =>
      some (SolidCore.Solidity.MVP.compileSourceProgramFuel program)
  | none => none

theorem Stmt.toFullYulViaMVPCoreUnchecked?_accepted_currentSolidCore
    {context : Context} {stmt : Stmt} {yulStmt : YulStmt}
    (hCompile : stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt) :
    ∃ fuel : Nat,
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  unfold Stmt.toFullYulViaMVPCoreUnchecked? at hCompile
  unfold Stmt.toFullYulViaMVPCoreUncheckedFuel?
  cases hProgram : stmt.toMVPCoreProgramUnchecked? context with
  | none =>
      simp [hProgram] at hCompile
  | some program =>
      simp [hProgram] at hCompile
      subst yulStmt
      exact
        ⟨SolidCore.Solidity.MVP.compileSourceProgramFuel program,
          by simp [hProgram],
          SolidCore.Solidity.MVP.compileSourceProgram_accepted_currentSolidCore
            program⟩

def Stmt.toFullYulSourceViaMVPCoreUnchecked?
    (context : Context) (stmt : Stmt) : Option YulStmt :=
  stmt.toFullYulViaMVPCoreUnchecked? context

theorem Stmt.toFullYulSourceViaMVPCoreUnchecked?_success_elaborates_core
    {context : Context} {stmt : Stmt} {yulStmt : YulStmt}
    (hCompile :
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt) :
    ∃ program : MVPCoreProgram,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      yulStmt =
        SolidCore.Solidity.MVP.compileSourceProgramStmt program := by
  unfold Stmt.toFullYulSourceViaMVPCoreUnchecked? at hCompile
  unfold Stmt.toFullYulViaMVPCoreUnchecked? at hCompile
  cases hProgram : stmt.toMVPCoreProgramUnchecked? context with
  | none =>
      simp [hProgram] at hCompile
  | some program =>
      simp [hProgram] at hCompile
      exact ⟨program, by simp [hProgram], hCompile.symm⟩

theorem Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
    {context : Context} {stmt : Stmt} {yulStmt : YulStmt}
    (hCore :
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt) :
    stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt := by
  simp [Stmt.toFullYulSourceViaMVPCoreUnchecked?, hCore]

theorem Stmt.toFullYulSourceViaMVPCoreUnchecked?_accepted_currentSolidCore_of_core
    {context : Context} {stmt : Stmt} {yulStmt : YulStmt}
    (hCore :
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt) :
    ∃ fuel : Nat,
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_accepted_currentSolidCore
        hCore with
    ⟨fuel, hFuel, hAccepted⟩
  exact
    ⟨fuel, hFuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core hCore,
      hAccepted⟩

theorem Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
    {context : Context} {stmt : Stmt} {program : MVPCoreProgram}
    {result : SolidCore.Solidity.MVP.Result}
    (hElab : stmt.toMVPCoreProgramUnchecked? context = some program)
    (state : SolidCore.Solidity.MVP.State)
    (hEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result) :
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  refine
    ⟨SolidCore.Solidity.MVP.compileSourceProgramStmt program,
      SolidCore.Solidity.MVP.compileSourceProgramFuel program,
      ?_, ?_, ?_, ?_⟩
  · simp [Stmt.toFullYulViaMVPCoreUnchecked?, hElab]
  · simp [Stmt.toFullYulViaMVPCoreUncheckedFuel?, hElab]
  · simpa [hEval] using
      SolidCore.Solidity.MVP.compileSourceProgram_correct state program
  · exact
      SolidCore.Solidity.MVP.compileSourceProgram_accepted_currentSolidCore
        program

theorem Stmt.toFullYulSourceViaMVPCoreUnchecked?_correct_of_core_eval
    {context : Context} {stmt : Stmt} {program : MVPCoreProgram}
    {result : SolidCore.Solidity.MVP.Result}
    (hElab : stmt.toMVPCoreProgramUnchecked? context = some program)
    (state : SolidCore.Solidity.MVP.State)
    (hEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result) :
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hElab state hEval with
    ⟨yulStmt, fuel, hCoreCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, fuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core hCoreCompile,
      hFuel, hYul, hAccepted⟩

theorem Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      ∃ coreStmt : MVPCoreStmt,
        stmt.toMVPCoreUnchecked? context = some coreStmt ∧
        Stmt.eval sourceFuel context runtime stmt =
          some sourceResult ∧
        SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
          mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases hStmt with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  let program : MVPCoreProgram := { body := coreStmt }
  have hProgram :
      stmt.toMVPCoreProgramUnchecked? context =
        some program := by
    simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile, program]
  have hProgramEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        mvpResult := by
    simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
      using hCoreEval
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state hProgramEval with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul,
      hAccepted⟩

theorem Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      ∃ coreStmt : MVPCoreStmt,
        stmt.toMVPCoreUnchecked? context = some coreStmt ∧
        Stmt.eval sourceFuel context runtime stmt =
          some sourceResult ∧
        SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
          mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
        hStmt with
    ⟨yulStmt, yulFuel, hCoreCompile, hFuel, hSource, hYul,
      hAccepted⟩
  exact
    ⟨yulStmt, yulFuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.compile_sound_of_sourceToMVPCoreStmt_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      ∃ coreStmt : MVPCoreStmt,
        stmt.toMVPCoreUnchecked? context = some coreStmt ∧
        Stmt.eval sourceFuel context runtime stmt =
          some sourceResult ∧
        SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
          mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia hStmt

def Stmt.SourceToMVPCoreStmtCorrect
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmt : Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  ∃ coreStmt : MVPCoreStmt,
    stmt.toMVPCoreUnchecked? context = some coreStmt ∧
    Stmt.eval sourceFuel context runtime stmt =
      some sourceResult ∧
    SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
      mvpResult

theorem Stmt.compile_sound_of_sourceToMVPCoreStmtCorrect
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      Stmt.SourceToMVPCoreStmtCorrect
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.compile_sound_of_sourceToMVPCoreStmt_correct
      (by simpa [Stmt.SourceToMVPCoreStmtCorrect] using hStmt)

def Stmt.SourceToMVPCoreProgramCorrect
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmt : Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  ∃ program : MVPCoreProgram,
    stmt.toMVPCoreProgramUnchecked? context = some program ∧
    Stmt.eval sourceFuel context runtime stmt =
      some sourceResult ∧
    SolidCore.Solidity.MVP.SourceProgram.eval state program =
      mvpResult

def Stmt.SourceListToMVPCoreStmtCorrect
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmts : List Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  ∃ coreStmt : MVPCoreStmt,
    Stmt.listToMVPCoreUnchecked? context stmts = some coreStmt ∧
    Stmt.evalList sourceFuel context runtime stmts =
      some sourceResult ∧
    SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
      mvpResult

def Stmt.SourceToMVPCoreStmtCorrectRelated
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmt : Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  Stmt.SourceToMVPCoreStmtCorrect sourceFuel context runtime state
    stmt sourceResult mvpResult ∧
  Result.RelatesMVPCore context sourceResult mvpResult

def Stmt.SourceToMVPCoreProgramCorrectRelated
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmt : Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  Stmt.SourceToMVPCoreProgramCorrect sourceFuel context runtime state
    stmt sourceResult mvpResult ∧
  Result.RelatesMVPCore context sourceResult mvpResult

def Stmt.SourceListToMVPCoreStmtCorrectRelated
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmts : List Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  Stmt.SourceListToMVPCoreStmtCorrect sourceFuel context runtime state
    stmts sourceResult mvpResult ∧
  Result.RelatesMVPCore context sourceResult mvpResult

def Stmt.ToMVPCoreStmtCompiled (context : Context) (stmt : Stmt) : Prop :=
  ∃ coreStmt : MVPCoreStmt,
    stmt.toMVPCoreUnchecked? context = some coreStmt

def Stmt.ListToMVPCoreStmtCompiled
    (context : Context) (stmts : List Stmt) : Prop :=
  ∃ coreStmt : MVPCoreStmt,
    Stmt.listToMVPCoreUnchecked? context stmts = some coreStmt

def Stmt.SwitchCasesToMVPCoreCasesCompiled
    (context : Context) (cases : List (Word × Stmt)) : Prop :=
  ∃ casesCore : List (Word × MVPCoreStmt),
    Stmt.switchCasesToMVPCoreUnchecked? context cases =
      some casesCore

theorem Stmt.sourceToMVPCoreStmtCorrect_compiled
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      Stmt.SourceToMVPCoreStmtCorrect
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.ToMVPCoreStmtCompiled context stmt := by
  rcases hStmt with ⟨coreStmt, hCompile, _hSource, _hMVP⟩
  exact ⟨coreStmt, hCompile⟩

theorem Stmt.sourceListToMVPCoreStmtCorrect_compiled
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmts : List Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmts :
      Stmt.SourceListToMVPCoreStmtCorrect
        sourceFuel context runtime state stmts sourceResult mvpResult) :
    Stmt.ListToMVPCoreStmtCompiled context stmts := by
  rcases hStmts with ⟨coreStmt, hCompile, _hSource, _hMVP⟩
  exact ⟨coreStmt, hCompile⟩

theorem Stmt.sourceToMVPCoreStmtCorrect_toProgramCorrect
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      Stmt.SourceToMVPCoreStmtCorrect
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.SourceToMVPCoreProgramCorrect
      sourceFuel context runtime state stmt sourceResult mvpResult := by
  rcases hStmt with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  let program : MVPCoreProgram := { body := coreStmt }
  refine ⟨program, ?_, hSource, ?_⟩
  · simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile, program]
  · simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
      using hCoreEval

theorem Stmt.sourceToMVPCoreStmtCorrectRelated_toProgramCorrectRelated
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      Stmt.SourceToMVPCoreStmtCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.SourceToMVPCoreProgramCorrectRelated
      sourceFuel context runtime state stmt sourceResult mvpResult := by
  rcases hStmt with ⟨hCorrect, hRelated⟩
  exact
    ⟨Stmt.sourceToMVPCoreStmtCorrect_toProgramCorrect hCorrect,
      hRelated⟩

theorem Stmt.compile_sound_of_sourceToMVPCoreProgramCorrect
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hProgram :
      Stmt.SourceToMVPCoreProgramCorrect
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases hProgram with
    ⟨program, hElab, hSource, hMVP⟩
  rcases
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_correct_of_core_eval
        hElab state hMVP with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul,
      hAccepted⟩

theorem Stmt.compile_sound_of_sourceToMVPCoreProgramCorrectRelated
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hProgram :
      Stmt.SourceToMVPCoreProgramCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext ∧
      Result.RelatesMVPCore context sourceResult mvpResult := by
  rcases hProgram with ⟨hCorrect, hRelated⟩
  rcases
      Stmt.compile_sound_of_sourceToMVPCoreProgramCorrect
        hCorrect with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul,
      hAccepted, hRelated⟩

theorem Stmt.compile_sound_of_sourceToMVPCoreStmtCorrectRelated
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hStmt :
      Stmt.SourceToMVPCoreStmtCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext ∧
      Result.RelatesMVPCore context sourceResult mvpResult := by
  exact
    Stmt.compile_sound_of_sourceToMVPCoreProgramCorrectRelated
      (Stmt.sourceToMVPCoreStmtCorrectRelated_toProgramCorrectRelated
        hStmt)

def Stmt.acceptedMVPCoreSourceUnchecked?
    (context : Context) (stmt : Stmt) : Bool :=
  (stmt.toMVPCoreProgramUnchecked? context).isSome

theorem Stmt.acceptedMVPCoreSourceUnchecked?_eq_true_iff
    (context : Context) (stmt : Stmt) :
    stmt.acceptedMVPCoreSourceUnchecked? context = true ↔
      ∃ program, stmt.toMVPCoreProgramUnchecked? context = some program := by
  constructor
  · intro hAccepted
    unfold Stmt.acceptedMVPCoreSourceUnchecked? at hAccepted
    cases hProgram : stmt.toMVPCoreProgramUnchecked? context with
    | none =>
        simp [hProgram] at hAccepted
    | some program =>
        exact ⟨program, rfl⟩
  · intro hProgram
    rcases hProgram with ⟨program, hProgram⟩
    simp [Stmt.acceptedMVPCoreSourceUnchecked?, hProgram]

def Stmt.AcceptedSource (context : Context) (stmt : Stmt) : Prop :=
  stmt.acceptedMVPCoreSourceUnchecked? context = true

def Stmt.acceptedSource? (context : Context) (stmt : Stmt) : Bool :=
  stmt.acceptedMVPCoreSourceUnchecked? context

theorem Stmt.acceptedSource?_eq_true_iff
    (context : Context) (stmt : Stmt) :
    stmt.acceptedSource? context = true ↔
      Stmt.AcceptedSource context stmt := by
  rfl

theorem Stmt.acceptedSource?_eq_true_iff_elaborates_core
    (context : Context) (stmt : Stmt) :
    stmt.acceptedSource? context = true ↔
      ∃ program : MVPCoreProgram,
        stmt.toMVPCoreProgramUnchecked? context = some program := by
  simpa [Stmt.acceptedSource?] using
    Stmt.acceptedMVPCoreSourceUnchecked?_eq_true_iff context stmt

theorem Stmt.AcceptedSource.elaborates_core
    {context : Context} {stmt : Stmt}
    (hAccepted : Stmt.AcceptedSource context stmt) :
    ∃ program : MVPCoreProgram,
      stmt.toMVPCoreProgramUnchecked? context = some program := by
  exact
    (Stmt.acceptedSource?_eq_true_iff_elaborates_core
      context stmt).mp (by
        simpa [Stmt.acceptedSource?, Stmt.AcceptedSource] using hAccepted)

theorem Stmt.acceptedSource?_success_elaborates_core
    {context : Context} {stmt : Stmt}
    (hAccepted : stmt.acceptedSource? context = true) :
    ∃ program : MVPCoreProgram,
      stmt.toMVPCoreProgramUnchecked? context = some program := by
  exact
    (Stmt.acceptedSource?_eq_true_iff_elaborates_core
      context stmt).mp hAccepted

theorem Stmt.sourceToMVPCoreProgramCorrect_acceptedSource
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hProgram :
      Stmt.SourceToMVPCoreProgramCorrect
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.AcceptedSource context stmt := by
  rcases hProgram with ⟨program, hProgram, _hSource, _hMVP⟩
  simp [Stmt.AcceptedSource, Stmt.acceptedMVPCoreSourceUnchecked?,
    hProgram]

theorem Stmt.sourceToMVPCoreProgramCorrectRelated_acceptedSource
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hProgram :
      Stmt.SourceToMVPCoreProgramCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.AcceptedSource context stmt := by
  exact
    Stmt.sourceToMVPCoreProgramCorrect_acceptedSource
      hProgram.left

def Stmt.AcceptedSourceRunCorrectRelated
    (sourceFuel : Nat) (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State) (stmt : Stmt)
    (sourceResult : Result)
    (mvpResult : SolidCore.Solidity.MVP.Result) : Prop :=
  Stmt.SourceToMVPCoreProgramCorrectRelated sourceFuel context runtime
    state stmt sourceResult mvpResult

theorem Stmt.AcceptedSourceRunCorrectRelated.acceptedSource
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hRun :
      Stmt.AcceptedSourceRunCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    Stmt.AcceptedSource context stmt := by
  exact
    Stmt.sourceToMVPCoreProgramCorrectRelated_acceptedSource
      (by
        simpa [Stmt.AcceptedSourceRunCorrectRelated] using hRun)

theorem Stmt.acceptedMVPCoreSourceUnchecked?_correct_toFullYulVia
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      (Stmt.acceptedMVPCoreSourceUnchecked?_eq_true_iff
        context stmt).mp hAccepted with
    ⟨program, hProgram⟩
  let result := SolidCore.Solidity.MVP.SourceProgram.eval state program
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state (by rfl : SolidCore.Solidity.MVP.SourceProgram.eval
          state program = result) with
    ⟨yulStmt, fuel, hCompile, hFuel, hYul, hAcceptedYul⟩
  exact
    ⟨program, result, yulStmt, fuel, hProgram, rfl,
      hCompile, hFuel, hYul, hAcceptedYul⟩

theorem Stmt.acceptedMVPCoreSourceUnchecked?_correct_of_core
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.acceptedMVPCoreSourceUnchecked?_correct_toFullYulVia
        hAccepted state with
    ⟨program, result, yulStmt, fuel, hProgram, hEval,
      hCoreCompile, hFuel, hYul, hAcceptedYul⟩
  exact
    ⟨program, result, yulStmt, fuel, hProgram, hEval,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hYul, hAcceptedYul⟩

theorem Stmt.compile_complete_for_acceptedMVPCoreSourceUnchecked_via
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true) :
    ∃ program : MVPCoreProgram,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      (Stmt.acceptedMVPCoreSourceUnchecked?_eq_true_iff
        context stmt).mp hAccepted with
    ⟨program, hProgram⟩
  let yulStmt := SolidCore.Solidity.MVP.compileSourceProgramStmt program
  let fuel := SolidCore.Solidity.MVP.compileSourceProgramFuel program
  have hCoreCompile :
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt := by
    simp [Stmt.toFullYulViaMVPCoreUnchecked?, hProgram, yulStmt]
  exact
    ⟨program, yulStmt, fuel, hProgram, hCoreCompile,
      by simp [Stmt.toFullYulViaMVPCoreUncheckedFuel?, hProgram, fuel],
      by
        simpa [yulStmt, fuel] using
          SolidCore.Solidity.MVP.compileSourceProgram_accepted_currentSolidCore
            program⟩

theorem Stmt.compile_complete_for_acceptedMVPCoreSourceUnchecked
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true) :
    ∃ program : MVPCoreProgram,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.compile_complete_for_acceptedMVPCoreSourceUnchecked_via
        hAccepted with
    ⟨program, yulStmt, fuel, hProgram, hCoreCompile, hFuel,
      hAcceptedYul⟩
  exact
    ⟨program, yulStmt, fuel, hProgram,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hAcceptedYul⟩

theorem Stmt.compile_complete_for_acceptedSource_via
    {context : Context} {stmt : Stmt}
    (hAccepted : Stmt.AcceptedSource context stmt) :
    ∃ program : MVPCoreProgram,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.compile_complete_for_acceptedMVPCoreSourceUnchecked_via
      (by simpa [Stmt.AcceptedSource] using hAccepted)

theorem Stmt.compile_complete_for_acceptedSource
    {context : Context} {stmt : Stmt}
    (hAccepted : Stmt.AcceptedSource context stmt) :
    ∃ program : MVPCoreProgram,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.compile_complete_for_acceptedMVPCoreSourceUnchecked
      (by simpa [Stmt.AcceptedSource] using hAccepted)

theorem Stmt.compile_sound_for_acceptedMVPCoreSourceUnchecked_core
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact Stmt.acceptedMVPCoreSourceUnchecked?_correct_of_core
    hAccepted state

theorem Stmt.compile_sound_for_acceptedMVPCoreSourceUnchecked_via
    {context : Context} {stmt : Stmt}
    (hAccepted :
      stmt.acceptedMVPCoreSourceUnchecked? context = true)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.acceptedMVPCoreSourceUnchecked?_correct_toFullYulVia
      hAccepted state

theorem Stmt.compile_sound_for_acceptedSource
    {context : Context} {stmt : Stmt}
    (hAccepted : Stmt.AcceptedSource context stmt)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.compile_sound_for_acceptedMVPCoreSourceUnchecked_core
      (by simpa [Stmt.AcceptedSource] using hAccepted) state

theorem Stmt.compile_sound_for_acceptedSource_via
    {context : Context} {stmt : Stmt}
    (hAccepted : Stmt.AcceptedSource context stmt)
    (state : SolidCore.Solidity.MVP.State) :
    ∃ program : MVPCoreProgram,
    ∃ result : SolidCore.Solidity.MVP.Result,
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      stmt.toMVPCoreProgramUnchecked? context = some program ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program = result ∧
      stmt.toFullYulViaMVPCoreUnchecked? context = some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context = some fuel ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        result.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.compile_sound_for_acceptedMVPCoreSourceUnchecked_via
      (by simpa [Stmt.AcceptedSource] using hAccepted) state

theorem Stmt.compile_sound_for_acceptedSourceRunCorrectRelated
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State} {stmt : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hRun :
      Stmt.AcceptedSourceRunCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      Stmt.AcceptedSource context stmt ∧
      stmt.toFullYulSourceViaMVPCoreUnchecked? context =
        some yulStmt ∧
      stmt.toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval sourceFuel context runtime stmt =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext ∧
      Result.RelatesMVPCore context sourceResult mvpResult := by
  have hRelated :
      Stmt.SourceToMVPCoreProgramCorrectRelated
        sourceFuel context runtime state stmt sourceResult mvpResult := by
    simpa [Stmt.AcceptedSourceRunCorrectRelated] using hRun
  have hAccepted :
      Stmt.AcceptedSource context stmt :=
    Stmt.AcceptedSourceRunCorrectRelated.acceptedSource hRun
  rcases
      Stmt.compile_sound_of_sourceToMVPCoreProgramCorrectRelated
        hRelated with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul,
      hAcceptedYul, hResultRelated⟩
  exact
    ⟨yulStmt, yulFuel, hAccepted, hCompile, hFuel, hSource, hYul,
      hAcceptedYul, hResultRelated⟩

theorem Stmt.evalList_cons_of_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime} {stmt : Stmt}
    {rest : List Stmt} {result : Result}
    (hStmt :
      Stmt.eval fuel context runtime stmt =
        some (Result.normal runtime'))
    (hRest :
      Stmt.evalList fuel context runtime' rest =
        some result) :
    Stmt.evalList fuel context runtime (stmt :: rest) =
      some result := by
  simp [Stmt.evalList, hStmt, hRest]

theorem Stmt.evalList_cons_of_abrupt
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {stmt : Stmt}
    {rest : List Stmt} {result : Result}
    (hStmt :
      Stmt.eval fuel context runtime stmt = some result)
    (hAbrupt :
      ¬ ∃ runtime', result = Result.normal runtime') :
    Stmt.evalList fuel context runtime (stmt :: rest) =
      some result := by
  cases result <;> simp [Stmt.evalList, hStmt] at hAbrupt ⊢

theorem Stmt.block_eval_of_evalList
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {body : List Stmt} {result : Result}
    (hBody :
      Stmt.evalList fuel context runtime.pushScope body =
        some result) :
    Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
      some (result.mapRuntime Runtime.popScope) := by
  simp [Stmt.eval, hBody]

theorem Stmt.MVPCore_seq_eval_of_normal
    {state state' : SolidCore.Solidity.MVP.State}
    {first second : MVPCoreStmt}
    {result : SolidCore.Solidity.MVP.Result}
    (hFirst :
      SolidCore.Solidity.MVP.Stmt.eval state first =
        SolidCore.Solidity.MVP.Result.normal state')
    (hSecond :
      SolidCore.Solidity.MVP.Stmt.eval state' second = result) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.seq first second) =
      result := by
  simp [SolidCore.Solidity.MVP.Stmt.eval, hFirst, hSecond]

theorem Stmt.MVPCore_seq_eval_of_returned
    {state state' : SolidCore.Solidity.MVP.State}
    {first second : MVPCoreStmt}
    (hFirst :
      SolidCore.Solidity.MVP.Stmt.eval state first =
        SolidCore.Solidity.MVP.Result.returned state') :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.seq first second) =
      SolidCore.Solidity.MVP.Result.returned state' := by
  simp [SolidCore.Solidity.MVP.Stmt.eval, hFirst]

theorem Stmt.MVPCore_seq_eval_of_reverted
    {state state' : SolidCore.Solidity.MVP.State}
    {first second : MVPCoreStmt}
    (hFirst :
      SolidCore.Solidity.MVP.Stmt.eval state first =
        SolidCore.Solidity.MVP.Result.reverted state') :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.seq first second) =
      SolidCore.Solidity.MVP.Result.reverted state' := by
  simp [SolidCore.Solidity.MVP.Stmt.eval, hFirst]

theorem Stmt.MVPCore_seq2_eval_of_normal_returned
    {state state' state'' : SolidCore.Solidity.MVP.State}
    {first second : MVPCoreStmt}
    (hFirst :
      SolidCore.Solidity.MVP.Stmt.eval state first =
        SolidCore.Solidity.MVP.Result.normal state')
    (hSecond :
      SolidCore.Solidity.MVP.Stmt.eval state' second =
        SolidCore.Solidity.MVP.Result.returned state'') :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.seq first
          (SolidCore.Solidity.MVP.Stmt.seq second
            SolidCore.Solidity.MVP.Stmt.skip)) =
      SolidCore.Solidity.MVP.Result.returned state'' := by
  simp [SolidCore.Solidity.MVP.Stmt.eval, hFirst, hSecond]

theorem Stmt.listToMVPCoreUnchecked?_nil
    (context : Context) :
    Stmt.listToMVPCoreUnchecked? context [] =
      some SolidCore.Solidity.MVP.Stmt.skip := by
  simp [Stmt.listToMVPCoreUnchecked?]

theorem Stmt.listToMVPCoreUnchecked?_cons_of_compile
    {context : Context} {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    (hFirst :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRest :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore) :
    Stmt.listToMVPCoreUnchecked? context (first :: rest) =
      some (SolidCore.Solidity.MVP.Stmt.seq firstCore restCore) := by
  simp [Stmt.listToMVPCoreUnchecked?, hFirst, hRest]

theorem Stmt.listToMVPCoreStmtCompiled_nil
    (context : Context) :
    Stmt.ListToMVPCoreStmtCompiled context [] := by
  exact ⟨SolidCore.Solidity.MVP.Stmt.skip,
    Stmt.listToMVPCoreUnchecked?_nil context⟩

theorem Stmt.listToMVPCoreStmtCompiled_cons
    {context : Context} {first : Stmt} {rest : List Stmt}
    (hFirst : Stmt.ToMVPCoreStmtCompiled context first)
    (hRest : Stmt.ListToMVPCoreStmtCompiled context rest) :
    Stmt.ListToMVPCoreStmtCompiled context (first :: rest) := by
  rcases hFirst with ⟨firstCore, hFirstCompile⟩
  rcases hRest with ⟨restCore, hRestCompile⟩
  exact
    ⟨SolidCore.Solidity.MVP.Stmt.seq firstCore restCore,
      Stmt.listToMVPCoreUnchecked?_cons_of_compile
        hFirstCompile hRestCompile⟩

theorem Stmt.toMVPCoreUnchecked?_block_of_list_compile
    {context : Context} {body : List Stmt} {bodyCore : MVPCoreStmt}
    (hBody :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore) :
    (Stmt.block body).toMVPCoreUnchecked? context = some bodyCore := by
  simp [Stmt.toMVPCoreUnchecked?, hBody]

theorem Stmt.skip_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {state : SolidCore.Solidity.MVP.State} :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      Stmt.skip (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  exact
    ⟨SolidCore.Solidity.MVP.Stmt.skip,
      by simp [Stmt.toMVPCoreUnchecked?],
      by simp [Stmt.eval],
      by simp [SolidCore.Solidity.MVP.Stmt.eval]⟩

theorem Stmt.skip_sourceToMVPCoreStmtCorrect_related
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      Stmt.skip (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) ∧
    Result.RelatesMVPCore context
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  exact
    ⟨Stmt.skip_sourceToMVPCoreStmtCorrect,
      ⟨returnValue, hRelated⟩⟩

theorem Stmt.skip_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state Stmt.skip (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  simpa [Stmt.SourceToMVPCoreStmtCorrectRelated] using
    Stmt.skip_sourceToMVPCoreStmtCorrect_related
      (fuel := fuel) hRelated

theorem Stmt.listNil_sourceToMVPCore_correct
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {state : SolidCore.Solidity.MVP.State} :
    ∃ coreStmt : MVPCoreStmt,
      Stmt.listToMVPCoreUnchecked? context [] =
        some coreStmt ∧
      Stmt.evalList fuel context runtime [] =
        some (Result.normal runtime) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal state := by
  exact
    ⟨SolidCore.Solidity.MVP.Stmt.skip,
      by simp [Stmt.listToMVPCoreUnchecked?],
      by simp [Stmt.evalList],
      by simp [SolidCore.Solidity.MVP.Stmt.eval]⟩

theorem Stmt.listNil_sourceToMVPCoreListCorrect
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {state : SolidCore.Solidity.MVP.State} :
    Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime state []
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  simpa [Stmt.SourceListToMVPCoreStmtCorrect] using
    (Stmt.listNil_sourceToMVPCore_correct
      (fuel := fuel) (context := context)
      (runtime := runtime) (state := state))

theorem Stmt.listNil_sourceToMVPCoreListCorrectRelated
    {fuel : Nat} {context : Context}
    {runtime : Runtime} {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context runtime state []
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  exact
    ⟨Stmt.listNil_sourceToMVPCoreListCorrect,
      ⟨returnValue, hRelated⟩⟩

theorem Stmt.listCons_sourceToMVPCore_correct_of_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime first =
        some (Result.normal runtime'))
    (hRestSource :
      Stmt.evalList fuel context runtime' rest =
        some sourceResult)
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.normal state')
    (hRestMVP :
      SolidCore.Solidity.MVP.Stmt.eval state' restCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt ∧
      Stmt.evalList fuel context runtime (first :: rest) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.seq firstCore restCore
  have hCompile :
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.listToMVPCoreUnchecked?_cons_of_compile
        hFirstCompile hRestCompile
  have hSource :
      Stmt.evalList fuel context runtime (first :: rest) =
        some sourceResult :=
    Stmt.evalList_cons_of_normal hFirstSource hRestSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_seq_eval_of_normal hFirstMVP hRestMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.listCons_sourceToMVPCoreListCorrect_of_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state first
        (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state'))
    (hRest :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime' state' rest
        sourceResult mvpResult) :
    Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime state
      (first :: rest) sourceResult mvpResult := by
  rcases hFirst with
    ⟨firstCore, hFirstCompile, hFirstSource, hFirstMVP⟩
  rcases hRest with
    ⟨restCore, hRestCompile, hRestSource, hRestMVP⟩
  simpa [Stmt.SourceListToMVPCoreStmtCorrect] using
    Stmt.listCons_sourceToMVPCore_correct_of_normal
      hFirstCompile hRestCompile hFirstSource hRestSource
      hFirstMVP hRestMVP

theorem Stmt.listCons_sourceToMVPCoreListCorrectRelated_of_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        first (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state'))
    (hRest :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context runtime'
        state' rest sourceResult mvpResult) :
    Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context runtime state
      (first :: rest) sourceResult mvpResult := by
  rcases hFirst with ⟨hFirstCorrect, _hFirstRelated⟩
  rcases hRest with ⟨hRestCorrect, hRestRelated⟩
  exact
    ⟨Stmt.listCons_sourceToMVPCoreListCorrect_of_normal
        hFirstCorrect hRestCorrect,
      hRestRelated⟩

theorem Stmt.listCons_sourceToMVPCore_correct_of_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    {values : List Value}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime first =
        some (Result.returned runtime' values))
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    ∃ coreStmt : MVPCoreStmt,
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt ∧
      Stmt.evalList fuel context runtime (first :: rest) =
        some (Result.returned runtime' values) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.returned state' := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.seq firstCore restCore
  have hCompile :
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.listToMVPCoreUnchecked?_cons_of_compile
        hFirstCompile hRestCompile
  have hSource :
      Stmt.evalList fuel context runtime (first :: rest) =
        some (Result.returned runtime' values) := by
    simp [Stmt.evalList, hFirstSource]
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.returned state' := by
    simpa [coreStmt] using
      Stmt.MVPCore_seq_eval_of_returned hFirstMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.listCons_sourceToMVPCoreListCorrect_of_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {values : List Value}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state first
        (Result.returned runtime' values)
        (SolidCore.Solidity.MVP.Result.returned state'))
    (hRestCompile :
      Stmt.ListToMVPCoreStmtCompiled context rest) :
    Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime state
      (first :: rest) (Result.returned runtime' values)
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hFirst with
    ⟨firstCore, hFirstCompile, hFirstSource, hFirstMVP⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  simpa [Stmt.SourceListToMVPCoreStmtCorrect] using
    Stmt.listCons_sourceToMVPCore_correct_of_returned
      hFirstCompile hRestCompile hFirstSource hFirstMVP

theorem Stmt.listCons_sourceToMVPCoreListCorrectRelated_of_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {values : List Value}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        first (Result.returned runtime' values)
        (SolidCore.Solidity.MVP.Result.returned state'))
    (hRestCompile :
      Stmt.ListToMVPCoreStmtCompiled context rest) :
    Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context runtime state
      (first :: rest) (Result.returned runtime' values)
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hFirst with ⟨hFirstCorrect, hFirstRelated⟩
  exact
    ⟨Stmt.listCons_sourceToMVPCoreListCorrect_of_returned
        hFirstCorrect hRestCompile,
      hFirstRelated⟩

theorem Stmt.listCons_sourceToMVPCore_correct_of_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    {data : RevertData}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime first =
        some (Result.reverted runtime' data))
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.reverted state') :
    ∃ coreStmt : MVPCoreStmt,
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt ∧
      Stmt.evalList fuel context runtime (first :: rest) =
        some (Result.reverted runtime' data) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.reverted state' := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.seq firstCore restCore
  have hCompile :
      Stmt.listToMVPCoreUnchecked? context (first :: rest) =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.listToMVPCoreUnchecked?_cons_of_compile
        hFirstCompile hRestCompile
  have hSource :
      Stmt.evalList fuel context runtime (first :: rest) =
        some (Result.reverted runtime' data) := by
    simp [Stmt.evalList, hFirstSource]
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.reverted state' := by
    simpa [coreStmt] using
      Stmt.MVPCore_seq_eval_of_reverted hFirstMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.listCons_sourceToMVPCoreListCorrect_of_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {data : RevertData}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state first
        (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state'))
    (hRestCompile :
      Stmt.ListToMVPCoreStmtCompiled context rest) :
    Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime state
      (first :: rest) (Result.reverted runtime' data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hFirst with
    ⟨firstCore, hFirstCompile, hFirstSource, hFirstMVP⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  simpa [Stmt.SourceListToMVPCoreStmtCorrect] using
    Stmt.listCons_sourceToMVPCore_correct_of_reverted
      hFirstCompile hRestCompile hFirstSource hFirstMVP

theorem Stmt.listCons_sourceToMVPCoreListCorrectRelated_of_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {data : RevertData}
    (hFirst :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        first (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state'))
    (hRestCompile :
      Stmt.ListToMVPCoreStmtCompiled context rest) :
    Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context runtime state
      (first :: rest) (Result.reverted runtime' data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hFirst with ⟨hFirstCorrect, hFirstRelated⟩
  exact
    ⟨Stmt.listCons_sourceToMVPCoreListCorrect_of_reverted
        hFirstCorrect hRestCompile,
      hFirstRelated⟩

theorem Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.normal runtime'))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.normal state') :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.normal (Runtime.popScope runtime')) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal state' := by
  let coreStmt := bodyCore
  have hCompile :
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_block_of_list_compile
        hBodyCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.normal (Runtime.popScope runtime')) := by
    simpa [Result.mapRuntime] using
      Stmt.block_eval_of_evalList hBodySource
  exact ⟨coreStmt, hCompile, hSource, by simpa [coreStmt] using hBodyMVP⟩

theorem Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {values : List Value}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.returned runtime' values))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.returned (Runtime.popScope runtime') values) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.returned state' := by
  let coreStmt := bodyCore
  have hCompile :
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_block_of_list_compile
        hBodyCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.returned (Runtime.popScope runtime') values) := by
    simpa [Result.mapRuntime] using
      Stmt.block_eval_of_evalList hBodySource
  exact ⟨coreStmt, hCompile, hSource, by simpa [coreStmt] using hBodyMVP⟩

theorem Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {data : RevertData}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.reverted runtime' data))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.reverted state') :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.reverted (Runtime.popScope runtime') data) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.reverted state' := by
  let coreStmt := bodyCore
  have hCompile :
      (Stmt.block body).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_block_of_list_compile
        hBodyCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
        some (Result.reverted (Runtime.popScope runtime') data) := by
    simpa [Result.mapRuntime] using
      Stmt.block_eval_of_evalList hBodySource
  exact ⟨coreStmt, hCompile, hSource, by simpa [coreStmt] using hBodyMVP⟩

theorem Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state')) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.block body) (Result.normal (Runtime.popScope runtime'))
      (SolidCore.Solidity.MVP.Result.normal state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_normal
      hBodyCompile hBodySource hBodyMVP

theorem Stmt.block_sourceToMVPCoreStmtCorrectRelated_of_listCorrect_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body) (Result.normal (Runtime.popScope runtime'))
      (SolidCore.Solidity.MVP.Result.normal state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_normal
        hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.popScope⟩⟩

theorem Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {values : List Value}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.returned runtime' values)
        (SolidCore.Solidity.MVP.Result.returned state')) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.block body)
      (Result.returned (Runtime.popScope runtime') values)
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_returned
      hBodyCompile hBodySource hBodyMVP

theorem Stmt.block_sourceToMVPCoreStmtCorrectRelated_of_listCorrect_returnedWord
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {value : Word}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body
        (Result.returned runtime' [Value.word value])
        (SolidCore.Solidity.MVP.Result.returned state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body)
      (Result.returned (Runtime.popScope runtime') [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_returned
        hBodyCorrect,
      hBodyRelated.popScope⟩

theorem Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {data : RevertData}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state')) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.block body)
      (Result.reverted (Runtime.popScope runtime') data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_reverted
      hBodyCompile hBodySource hBodyMVP

theorem Stmt.block_sourceToMVPCoreStmtCorrectRelated_of_listCorrect_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {data : RevertData}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body
        (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body)
      (Result.reverted (Runtime.popScope runtime') data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreStmtCorrect_of_listCorrect_reverted
        hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.popScope⟩⟩

theorem Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.normal runtime'))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.normal state') :
    (Stmt.block body).toMVPCoreProgramUnchecked? context =
      some ({ body := bodyCore } : MVPCoreProgram) ∧
    Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
      some (Result.normal (Runtime.popScope runtime')) ∧
    SolidCore.Solidity.MVP.SourceProgram.eval state
        ({ body := bodyCore } : MVPCoreProgram) =
      SolidCore.Solidity.MVP.Result.normal state' := by
  rcases
      Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_normal
        hBodyCompile hBodySource hBodyMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  have hCoreEq : coreStmt = bodyCore := by
    rw [Stmt.toMVPCoreUnchecked?_block_of_list_compile hBodyCompile]
      at hCoreCompile
    injection hCoreCompile with hEq
    exact hEq.symm
  subst coreStmt
  exact
    ⟨by simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile],
      hSource,
      by
        simpa [SolidCore.Solidity.MVP.SourceProgram.eval]
          using hCoreEval⟩

theorem Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {values : List Value}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.returned runtime' values))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    (Stmt.block body).toMVPCoreProgramUnchecked? context =
      some ({ body := bodyCore } : MVPCoreProgram) ∧
    Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
      some (Result.returned (Runtime.popScope runtime') values) ∧
    SolidCore.Solidity.MVP.SourceProgram.eval state
        ({ body := bodyCore } : MVPCoreProgram) =
      SolidCore.Solidity.MVP.Result.returned state' := by
  rcases
      Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  have hCoreEq : coreStmt = bodyCore := by
    rw [Stmt.toMVPCoreUnchecked?_block_of_list_compile hBodyCompile]
      at hCoreCompile
    injection hCoreCompile with hEq
    exact hEq.symm
  subst coreStmt
  exact
    ⟨by simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile],
      hSource,
      by
        simpa [SolidCore.Solidity.MVP.SourceProgram.eval]
          using hCoreEval⟩

theorem Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {data : RevertData}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList fuel context runtime.pushScope body =
        some (Result.reverted runtime' data))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.reverted state') :
    (Stmt.block body).toMVPCoreProgramUnchecked? context =
      some ({ body := bodyCore } : MVPCoreProgram) ∧
    Stmt.eval (fuel + 1) context runtime (Stmt.block body) =
      some (Result.reverted (Runtime.popScope runtime') data) ∧
    SolidCore.Solidity.MVP.SourceProgram.eval state
        ({ body := bodyCore } : MVPCoreProgram) =
      SolidCore.Solidity.MVP.Result.reverted state' := by
  rcases
      Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_reverted
        hBodyCompile hBodySource hBodyMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  have hCoreEq : coreStmt = bodyCore := by
    rw [Stmt.toMVPCoreUnchecked?_block_of_list_compile hBodyCompile]
      at hCoreCompile
    injection hCoreCompile with hEq
    exact hEq.symm
  subst coreStmt
  exact
    ⟨by simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile],
      hSource,
      by
        simpa [SolidCore.Solidity.MVP.SourceProgram.eval]
          using hCoreEval⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state')) :
    Stmt.SourceToMVPCoreProgramCorrect (fuel + 1) context runtime state
      (Stmt.block body) (Result.normal (Runtime.popScope runtime'))
      (SolidCore.Solidity.MVP.Result.normal state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  rcases
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_normal
        hBodyCompile hBodySource hBodyMVP with
    ⟨hProgram, hSource, hMVP⟩
  exact ⟨{ body := bodyCore }, hProgram, hSource, hMVP⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrectRelated_of_listCorrect_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state')) :
    Stmt.SourceToMVPCoreProgramCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body) (Result.normal (Runtime.popScope runtime'))
      (SolidCore.Solidity.MVP.Result.normal state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_normal
        hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.popScope⟩⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {values : List Value}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.returned runtime' values)
        (SolidCore.Solidity.MVP.Result.returned state')) :
    Stmt.SourceToMVPCoreProgramCorrect (fuel + 1) context runtime state
      (Stmt.block body)
      (Result.returned (Runtime.popScope runtime') values)
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  rcases
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP with
    ⟨hProgram, hSource, hMVP⟩
  exact ⟨{ body := bodyCore }, hProgram, hSource, hMVP⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrectRelated_of_listCorrect_returnedWord
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {value : Word}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body
        (Result.returned runtime' [Value.word value])
        (SolidCore.Solidity.MVP.Result.returned state')) :
    Stmt.SourceToMVPCoreProgramCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body)
      (Result.returned (Runtime.popScope runtime') [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_returned
        hBodyCorrect,
      hBodyRelated.popScope⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {data : RevertData}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrect fuel context runtime.pushScope
        state body (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state')) :
    Stmt.SourceToMVPCoreProgramCorrect (fuel + 1) context runtime state
      (Stmt.block body)
      (Result.reverted (Runtime.popScope runtime') data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  rcases
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_reverted
        hBodyCompile hBodySource hBodyMVP with
    ⟨hProgram, hSource, hMVP⟩
  exact ⟨{ body := bodyCore }, hProgram, hSource, hMVP⟩

theorem Stmt.block_sourceToMVPCoreProgramCorrectRelated_of_listCorrect_reverted
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {data : RevertData}
    (hBody :
      Stmt.SourceListToMVPCoreStmtCorrectRelated fuel context
        runtime.pushScope state body
        (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state')) :
    Stmt.SourceToMVPCoreProgramCorrectRelated (fuel + 1) context runtime
      state (Stmt.block body)
      (Result.reverted (Runtime.popScope runtime') data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.block_sourceToMVPCoreProgramCorrect_of_listCorrect_reverted
        hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.popScope⟩⟩

theorem Stmt.blockCons_sourceToMVPCoreProgram_correct_of_normal_normal
    {fuel : Nat} {context : Context}
    {runtime runtime' runtime'' : Runtime}
    {state state' state'' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime.pushScope first =
        some (Result.normal runtime'))
    (hRestSource :
      Stmt.evalList fuel context runtime' rest =
        some (Result.normal runtime''))
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.normal state')
    (hRestMVP :
      SolidCore.Solidity.MVP.Stmt.eval state' restCore =
        SolidCore.Solidity.MVP.Result.normal state'') :
    ∃ program : MVPCoreProgram,
      (Stmt.block (first :: rest)).toMVPCoreProgramUnchecked? context =
        some program ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.block (first :: rest)) =
        some (Result.normal (Runtime.popScope runtime'')) ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.normal state'' := by
  rcases
      Stmt.listCons_sourceToMVPCore_correct_of_normal
        hFirstCompile hRestCompile hFirstSource hRestSource
        hFirstMVP hRestMVP with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  exact
    ⟨{ body := bodyCore },
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_normal
        hBodyCompile hBodySource hBodyMVP⟩

theorem Stmt.blockCons_sourceToMVPCoreProgram_correct_of_normal_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' runtime'' : Runtime}
    {state state' state'' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    {values : List Value}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime.pushScope first =
        some (Result.normal runtime'))
    (hRestSource :
      Stmt.evalList fuel context runtime' rest =
        some (Result.returned runtime'' values))
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.normal state')
    (hRestMVP :
      SolidCore.Solidity.MVP.Stmt.eval state' restCore =
        SolidCore.Solidity.MVP.Result.returned state'') :
    ∃ program : MVPCoreProgram,
      (Stmt.block (first :: rest)).toMVPCoreProgramUnchecked? context =
        some program ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.block (first :: rest)) =
        some (Result.returned (Runtime.popScope runtime'') values) ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.returned state'' := by
  rcases
      Stmt.listCons_sourceToMVPCore_correct_of_normal
        hFirstCompile hRestCompile hFirstSource hRestSource
        hFirstMVP hRestMVP with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  exact
    ⟨{ body := bodyCore },
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP⟩

theorem Stmt.blockCons_sourceToMVPCoreProgram_correct_of_returned
    {fuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {first : Stmt} {rest : List Stmt}
    {firstCore restCore : MVPCoreStmt}
    {values : List Value}
    (hFirstCompile :
      first.toMVPCoreUnchecked? context = some firstCore)
    (hRestCompile :
      Stmt.listToMVPCoreUnchecked? context rest = some restCore)
    (hFirstSource :
      Stmt.eval fuel context runtime.pushScope first =
        some (Result.returned runtime' values))
    (hFirstMVP :
      SolidCore.Solidity.MVP.Stmt.eval state firstCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    ∃ program : MVPCoreProgram,
      (Stmt.block (first :: rest)).toMVPCoreProgramUnchecked? context =
        some program ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.block (first :: rest)) =
        some (Result.returned (Runtime.popScope runtime') values) ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.returned state' := by
  rcases
      Stmt.listCons_sourceToMVPCore_correct_of_returned
        hFirstCompile hRestCompile hFirstSource hFirstMVP with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  exact
    ⟨{ body := bodyCore },
      Stmt.block_sourceToMVPCoreProgram_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP⟩

theorem Stmt.block_toFullYulViaMVPCore_correct_of_evalList_normal
    {sourceFuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList sourceFuel context runtime.pushScope body =
        some (Result.normal runtime'))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.normal state') :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.block body).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.block body).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.block body) =
        some (Result.normal (Runtime.popScope runtime')) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.normal state').toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
      (Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_normal
        hBodyCompile hBodySource hBodyMVP)

theorem Stmt.block_toFullYulViaMVPCore_correct_of_evalList_returned
    {sourceFuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {values : List Value}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList sourceFuel context runtime.pushScope body =
        some (Result.returned runtime' values))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.block body).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.block body).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.block body) =
        some (Result.returned (Runtime.popScope runtime') values) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned state').toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
      (Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP)

theorem Stmt.block_toFullYulSourceViaMVPCore_correct_of_evalList_normal
    {sourceFuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList sourceFuel context runtime.pushScope body =
        some (Result.normal runtime'))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.normal state') :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.block body).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.block body).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.block body) =
        some (Result.normal (Runtime.popScope runtime')) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.normal state').toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
      (Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_normal
        hBodyCompile hBodySource hBodyMVP)

theorem Stmt.block_toFullYulSourceViaMVPCore_correct_of_evalList_returned
    {sourceFuel : Nat} {context : Context}
    {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : List Stmt} {bodyCore : MVPCoreStmt}
    {values : List Value}
    (hBodyCompile :
      Stmt.listToMVPCoreUnchecked? context body = some bodyCore)
    (hBodySource :
      Stmt.evalList sourceFuel context runtime.pushScope body =
        some (Result.returned runtime' values))
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore =
        SolidCore.Solidity.MVP.Result.returned state') :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.block body).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.block body).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.block body) =
        some (Result.returned (Runtime.popScope runtime') values) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned state').toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
      (Stmt.block_sourceToMVPCoreStmt_correct_of_evalList_returned
        hBodyCompile hBodySource hBodyMVP)

theorem Stmt.toMVPCoreUnchecked?_ifElse_of_compile
    {context : Context} {thenBranch elseBranch : Stmt}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenCore elseCore : MVPCoreStmt}
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hThen : thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElse : elseBranch.toMVPCoreUnchecked? context = some elseCore) :
    (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreUnchecked?
        context =
      some
        (SolidCore.Solidity.MVP.Stmt.switchCases condLegacy
          [(0, elseCore)] thenCore) := by
  simp [Stmt.toMVPCoreUnchecked?, hCond, hThen, hElse]

theorem Stmt.ifElse_eval_then_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {sourceResult : Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThen :
      Stmt.eval fuel context runtime thenBranch =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.ifElse condExpr thenBranch elseBranch) =
      some sourceResult := by
  have hCondEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hCond runtime
  have hTruthy :
      wordTruthy (SolidCoreYulCore.norm condLegacy.eval) = true := by
    simp [wordTruthy, hNonzero, norm_norm]
  simp [Stmt.eval, hCondEval, Value.expectWord, hTruthy, hThen]

theorem Stmt.ifElse_eval_else_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {sourceResult : Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hElse :
      Stmt.eval fuel context runtime elseBranch =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.ifElse condExpr thenBranch elseBranch) =
      some sourceResult := by
  have hCondEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hCond runtime
  have hTruthy :
      wordTruthy (SolidCoreYulCore.norm condLegacy.eval) = false := by
    simp [wordTruthy, hZero, norm_norm, norm_zero]
  simp [Stmt.eval, hCondEval, Value.expectWord, hTruthy, hElse]

theorem Stmt.MVPCore_ifElse_eval_then_of_legacy
    {state : SolidCore.Solidity.MVP.State}
    {condLegacy : LegacyExpr} {thenCore elseCore : MVPCoreStmt}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThen :
      SolidCore.Solidity.MVP.Stmt.eval state thenCore = mvpResult) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.switchCases condLegacy
          [(0, elseCore)] thenCore) =
      mvpResult := by
  have hNotEq :
      ¬ SolidCoreYulCore.norm condLegacy.eval =
        SolidCoreYulCore.norm 0 := by
    simpa using hNonzero
  simp [SolidCore.Solidity.MVP.Stmt.switchCases,
    SolidCore.Solidity.MVP.Stmt.eval, hNotEq, hThen]

theorem Stmt.MVPCore_ifElse_eval_else_of_legacy
    {state : SolidCore.Solidity.MVP.State}
    {condLegacy : LegacyExpr} {thenCore elseCore : MVPCoreStmt}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hElse :
      SolidCore.Solidity.MVP.Stmt.eval state elseCore = mvpResult) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.switchCases condLegacy
          [(0, elseCore)] thenCore) =
      mvpResult := by
  have hEq :
      SolidCoreYulCore.norm condLegacy.eval =
        SolidCoreYulCore.norm 0 := by
    simpa using hZero
  simp [SolidCore.Solidity.MVP.Stmt.switchCases,
    SolidCore.Solidity.MVP.Stmt.eval, hEq, hElse]

theorem Stmt.ifElseThen_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hThenSource :
      Stmt.eval fuel context runtime thenBranch =
        some sourceResult)
    (hThenMVP :
      SolidCore.Solidity.MVP.Stmt.eval state thenCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases condLegacy
      [(0, elseCore)] thenCore
  have hCompile :
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_ifElse_of_compile
        hCond hThenCompile hElseCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult :=
    Stmt.ifElse_eval_then_of_legacy
      hChecked hCond hNonzero hThenSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_ifElse_eval_then_of_legacy
        hNonzero hThenMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.ifElseElse_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hElseSource :
      Stmt.eval fuel context runtime elseBranch =
        some sourceResult)
    (hElseMVP :
      SolidCore.Solidity.MVP.Stmt.eval state elseCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases condLegacy
      [(0, elseCore)] thenCore
  have hCompile :
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_ifElse_of_compile
        hCond hThenCompile hElseCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult :=
    Stmt.ifElse_eval_else_of_legacy
      hChecked hCond hZero hElseSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_ifElse_eval_else_of_legacy
        hZero hElseMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.ifElseThen_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThen :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state
        thenBranch sourceResult mvpResult)
    (hElseCompile :
      ∃ elseCore : MVPCoreStmt,
        elseBranch.toMVPCoreUnchecked? context = some elseCore) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.ifElse condExpr thenBranch elseBranch)
      sourceResult mvpResult := by
  rcases hThen with
    ⟨thenCore, hThenCompile, hThenSource, hThenMVP⟩
  rcases hElseCompile with
    ⟨elseCore, hElseCompile⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.ifElseThen_sourceToMVPCoreStmt_correct
      hChecked hCond hNonzero hThenCompile hElseCompile
      hThenSource hThenMVP

theorem Stmt.ifElseThen_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThen :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        thenBranch sourceResult mvpResult)
    (hElseCompile :
      Stmt.ToMVPCoreStmtCompiled context elseBranch) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.ifElse condExpr thenBranch elseBranch)
      sourceResult mvpResult := by
  rcases hThen with ⟨hThenCorrect, hThenRelated⟩
  exact
    ⟨Stmt.ifElseThen_sourceToMVPCoreStmtCorrect
        hChecked hCond hNonzero hThenCorrect hElseCompile,
      hThenRelated⟩

theorem Stmt.ifElseElse_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hThenCompile :
      ∃ thenCore : MVPCoreStmt,
        thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElse :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state
        elseBranch sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.ifElse condExpr thenBranch elseBranch)
      sourceResult mvpResult := by
  rcases hThenCompile with
    ⟨thenCore, hThenCompile⟩
  rcases hElse with
    ⟨elseCore, hElseCompile, hElseSource, hElseMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.ifElseElse_sourceToMVPCoreStmt_correct
      hChecked hCond hZero hThenCompile hElseCompile
      hElseSource hElseMVP

theorem Stmt.ifElseElse_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hThenCompile :
      Stmt.ToMVPCoreStmtCompiled context thenBranch)
    (hElse :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        elseBranch sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.ifElse condExpr thenBranch elseBranch)
      sourceResult mvpResult := by
  rcases hElse with ⟨hElseCorrect, hElseRelated⟩
  exact
    ⟨Stmt.ifElseElse_sourceToMVPCoreStmtCorrect
        hChecked hCond hZero hThenCompile hElseCorrect,
      hElseRelated⟩

theorem Stmt.ifElseThen_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hThenSource :
      Stmt.eval sourceFuel context runtime thenBranch =
        some sourceResult)
    (hThenMVP :
      SolidCore.Solidity.MVP.Stmt.eval state thenCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.ifElseThen_sourceToMVPCoreStmt_correct
        hChecked hCond hNonzero hThenCompile hElseCompile
        hThenSource hThenMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  let program : MVPCoreProgram := { body := coreStmt }
  have hProgram :
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreProgramUnchecked?
          context =
        some program := by
    simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile, program]
  have hProgramEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        mvpResult := by
    simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
      using hCoreEval
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state hProgramEval with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.ifElseElse_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hElseSource :
      Stmt.eval sourceFuel context runtime elseBranch =
        some sourceResult)
    (hElseMVP :
      SolidCore.Solidity.MVP.Stmt.eval state elseCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.ifElseElse_sourceToMVPCoreStmt_correct
        hChecked hCond hZero hThenCompile hElseCompile
        hElseSource hElseMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  let program : MVPCoreProgram := { body := coreStmt }
  have hProgram :
      (Stmt.ifElse condExpr thenBranch elseBranch).toMVPCoreProgramUnchecked?
          context =
        some program := by
    simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile, program]
  have hProgramEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        mvpResult := by
    simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
      using hCoreEval
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state hProgramEval with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.ifElseThen_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hNonzero : SolidCoreYulCore.norm condLegacy.eval ≠ 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hThenSource :
      Stmt.eval sourceFuel context runtime thenBranch =
        some sourceResult)
    (hThenMVP :
      SolidCore.Solidity.MVP.Stmt.eval state thenCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.ifElseThen_toFullYulViaMVPCore_correct
        hChecked hCond hNonzero hThenCompile hElseCompile
        hThenSource hThenMVP with
    ⟨yulStmt, yulFuel, hCoreCompile, hFuel, hSource, hYul,
      hAccepted⟩
  exact
    ⟨yulStmt, yulFuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.ifElseElse_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {condExpr : Expr} {condLegacy : LegacyExpr}
    {thenBranch elseBranch : Stmt} {thenCore elseCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hCond : condExpr.toLegacyUnchecked? = some condLegacy)
    (hZero : SolidCoreYulCore.norm condLegacy.eval = 0)
    (hThenCompile :
      thenBranch.toMVPCoreUnchecked? context = some thenCore)
    (hElseCompile :
      elseBranch.toMVPCoreUnchecked? context = some elseCore)
    (hElseSource :
      Stmt.eval sourceFuel context runtime elseBranch =
        some sourceResult)
    (hElseMVP :
      SolidCore.Solidity.MVP.Stmt.eval state elseCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.ifElse condExpr thenBranch elseBranch).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.ifElse condExpr thenBranch elseBranch) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.ifElseElse_toFullYulViaMVPCore_correct
        hChecked hCond hZero hThenCompile hElseCompile
        hElseSource hElseMVP with
    ⟨yulStmt, yulFuel, hCoreCompile, hFuel, hSource, hYul,
      hAccepted⟩
  exact
    ⟨yulStmt, yulFuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.toMVPCoreUnchecked?_switchNil_of_compile
    {context : Context} {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt} {defaultCore : MVPCoreStmt}
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefault :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore) :
    (Stmt.switch discr [] (some defaultBranch)).toMVPCoreUnchecked?
        context =
      some
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          [] defaultCore) := by
  simp [Stmt.toMVPCoreUnchecked?, Stmt.switchCasesToMVPCoreUnchecked?,
    Stmt.optionalToMVPCoreUnchecked?, hDiscr, hDefault]

theorem Stmt.toMVPCoreUnchecked?_switchNilNone_of_compile
    {context : Context} {discr : Expr} {discrLegacy : LegacyExpr}
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy) :
    (Stmt.switch discr [] none).toMVPCoreUnchecked? context =
      some
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          [] SolidCore.Solidity.MVP.Stmt.skip) := by
  simp [Stmt.toMVPCoreUnchecked?, Stmt.switchCasesToMVPCoreUnchecked?,
    Stmt.optionalToMVPCoreUnchecked?, hDiscr]

theorem Stmt.toMVPCoreUnchecked?_switchCons_of_compile
    {context : Context} {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hBranch : branch.toMVPCoreUnchecked? context = some branchCore)
    (hRest :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefault :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore) :
    (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toMVPCoreUnchecked?
        context =
      some
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          ((label, branchCore) :: restCore) defaultCore) := by
  simp [Stmt.toMVPCoreUnchecked?, Stmt.switchCasesToMVPCoreUnchecked?,
    Stmt.optionalToMVPCoreUnchecked?, hDiscr, hBranch, hRest,
    hDefault]

theorem Stmt.toMVPCoreUnchecked?_switchConsNone_of_compile
    {context : Context} {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hBranch : branch.toMVPCoreUnchecked? context = some branchCore)
    (hRest :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore) :
    (Stmt.switch discr ((label, branch) :: rest) none).toMVPCoreUnchecked?
        context =
      some
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          ((label, branchCore) :: restCore)
          SolidCore.Solidity.MVP.Stmt.skip) := by
  simp [Stmt.toMVPCoreUnchecked?, Stmt.switchCasesToMVPCoreUnchecked?,
    Stmt.optionalToMVPCoreUnchecked?, hDiscr, hBranch, hRest]

theorem Stmt.switchCasesToMVPCoreCasesCompiled_nil
    (context : Context) :
    Stmt.SwitchCasesToMVPCoreCasesCompiled context [] := by
  exact
    ⟨[],
      by simp [Stmt.switchCasesToMVPCoreUnchecked?]⟩

theorem Stmt.switchCasesToMVPCoreCasesCompiled_cons
    {context : Context} {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    (hBranch : Stmt.ToMVPCoreStmtCompiled context branch)
    (hRest :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest) :
    Stmt.SwitchCasesToMVPCoreCasesCompiled
      context ((label, branch) :: rest) := by
  rcases hBranch with ⟨branchCore, hBranch⟩
  rcases hRest with ⟨restCore, hRest⟩
  exact
    ⟨(label, branchCore) :: restCore,
      by
        simp [Stmt.switchCasesToMVPCoreUnchecked?, hBranch, hRest]⟩

theorem Stmt.switchNil_eval_default_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt} {sourceResult : Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefault :
      Stmt.eval fuel context runtime defaultBranch =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr [] (some defaultBranch)) =
      some sourceResult := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  simp [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?, hDefault]

theorem Stmt.switchNilNone_eval_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr [] none) =
      some (Result.normal runtime) := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  simp [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?]

theorem Stmt.switchCons_eval_match_head_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.eval fuel context runtime branch =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
      some sourceResult := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  have hWordEq :
      wordEq label (SolidCoreYulCore.norm discrLegacy.eval) = true := by
    unfold wordEq
    simp [hMatch.symm, norm_norm]
  simp [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?, hWordEq, hBranch]

theorem Stmt.switchConsNone_eval_match_head_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.eval fuel context runtime branch =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr ((label, branch) :: rest) none) =
      some sourceResult := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  have hWordEq :
      wordEq label (SolidCoreYulCore.norm discrLegacy.eval) = true := by
    unfold wordEq
    simp [hMatch.symm, norm_norm]
  simp [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?, hWordEq, hBranch]

theorem Stmt.switchCons_eval_tail_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hTail :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr rest (some defaultBranch)) =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
      some sourceResult := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  have hWordEq :
      wordEq label (SolidCoreYulCore.norm discrLegacy.eval) = false := by
    unfold wordEq
    have hNoMatch' :
        ¬ SolidCoreYulCore.norm label =
          SolidCoreYulCore.norm (SolidCoreYulCore.norm discrLegacy.eval) := by
      intro hContr
      apply hNoMatch
      simpa [norm_norm] using hContr.symm
    simp [hNoMatch']
  simpa [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?, hWordEq] using hTail

theorem Stmt.switchConsNone_eval_tail_of_legacy
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hTail :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr rest none) =
        some sourceResult) :
    Stmt.eval (fuel + 1) context runtime
        (Stmt.switch discr ((label, branch) :: rest) none) =
      some sourceResult := by
  have hDiscrEval :=
    Expr.toLegacyUnchecked?_eval_runtime_of_checked_false
      context hChecked hDiscr runtime
  have hWordEq :
      wordEq label (SolidCoreYulCore.norm discrLegacy.eval) = false := by
    unfold wordEq
    have hNoMatch' :
        ¬ SolidCoreYulCore.norm label =
          SolidCoreYulCore.norm (SolidCoreYulCore.norm discrLegacy.eval) := by
      intro hContr
      apply hNoMatch
      simpa [norm_norm] using hContr.symm
    simp [hNoMatch']
  simpa [Stmt.eval, hDiscrEval, Value.expectWord,
    Stmt.findSwitchBranch?, hWordEq] using hTail

theorem Stmt.MVPCore_switchNil_eval_default
    {state : SolidCore.Solidity.MVP.State}
    {discrLegacy : LegacyExpr} {defaultCore : MVPCoreStmt}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hDefault :
      SolidCore.Solidity.MVP.Stmt.eval state defaultCore = mvpResult) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          [] defaultCore) =
      mvpResult := by
  simpa [SolidCore.Solidity.MVP.Stmt.switchCases] using hDefault

theorem Stmt.MVPCore_switchCons_eval_match_head_of_legacy
    {state : SolidCore.Solidity.MVP.State}
    {discrLegacy : LegacyExpr} {label : Word}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      SolidCore.Solidity.MVP.Stmt.eval state branchCore = mvpResult) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          ((label, branchCore) :: restCore) defaultCore) =
      mvpResult := by
  simp [SolidCore.Solidity.MVP.Stmt.switchCases,
    SolidCore.Solidity.MVP.Stmt.eval, hMatch, hBranch]

theorem Stmt.MVPCore_switchCons_eval_tail_of_legacy
    {state : SolidCore.Solidity.MVP.State}
    {discrLegacy : LegacyExpr} {label : Word}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hTail :
      SolidCore.Solidity.MVP.Stmt.eval state
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore defaultCore) =
        mvpResult) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
          ((label, branchCore) :: restCore) defaultCore) =
      mvpResult := by
  simp [SolidCore.Solidity.MVP.Stmt.switchCases,
    SolidCore.Solidity.MVP.Stmt.eval, hNoMatch, hTail]

theorem Stmt.switchNil_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt} {defaultCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hDefaultSource :
      Stmt.eval fuel context runtime defaultBranch =
        some sourceResult)
    (hDefaultMVP :
      SolidCore.Solidity.MVP.Stmt.eval state defaultCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr [] (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr [] (some defaultBranch)) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      [] defaultCore
  have hCompile :
      (Stmt.switch discr [] (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchNil_of_compile
        hDiscr hDefaultCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr [] (some defaultBranch)) =
        some sourceResult :=
    Stmt.switchNil_eval_default_of_legacy
      hChecked hDiscr hDefaultSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_switchNil_eval_default
        hDefaultMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchNilNone_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr [] none).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr [] none) =
        some (Result.normal runtime) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal state := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      [] SolidCore.Solidity.MVP.Stmt.skip
  have hCompile :
      (Stmt.switch discr [] none).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchNilNone_of_compile
        (context := context) hDiscr
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr [] none) =
        some (Result.normal runtime) :=
    Stmt.switchNilNone_eval_of_legacy hChecked hDiscr
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal state := by
    simpa [coreStmt, SolidCore.Solidity.MVP.Stmt.eval] using
      Stmt.MVPCore_switchNil_eval_default
        (state := state) (discrLegacy := discrLegacy)
        (defaultCore := SolidCore.Solidity.MVP.Stmt.skip)
        (mvpResult := SolidCore.Solidity.MVP.Result.normal state)
        (by simp [SolidCore.Solidity.MVP.Stmt.eval])
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchConsMatchHead_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hBranchSource :
      Stmt.eval fuel context runtime branch =
        some sourceResult)
    (hBranchMVP :
      SolidCore.Solidity.MVP.Stmt.eval state branchCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      ((label, branchCore) :: restCore) defaultCore
  have hCompile :
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchCons_of_compile
        hDiscr hBranchCompile hRestCompile hDefaultCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult :=
    Stmt.switchCons_eval_match_head_of_legacy
      hChecked hDiscr hMatch hBranchSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_switchCons_eval_match_head_of_legacy
        hMatch hBranchMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchConsNoneMatchHead_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hBranchSource :
      Stmt.eval fuel context runtime branch =
        some sourceResult)
    (hBranchMVP :
      SolidCore.Solidity.MVP.Stmt.eval state branchCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr ((label, branch) :: rest) none).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) none) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      ((label, branchCore) :: restCore)
      SolidCore.Solidity.MVP.Stmt.skip
  have hCompile :
      (Stmt.switch discr ((label, branch) :: rest) none).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchConsNone_of_compile
        hDiscr hBranchCompile hRestCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) none) =
        some sourceResult :=
    Stmt.switchConsNone_eval_match_head_of_legacy
      hChecked hDiscr hMatch hBranchSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_switchCons_eval_match_head_of_legacy
        (defaultCore := SolidCore.Solidity.MVP.Stmt.skip)
        hMatch hBranchMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchConsTail_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hTailSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr rest (some defaultBranch)) =
        some sourceResult)
    (hTailMVP :
      SolidCore.Solidity.MVP.Stmt.eval state
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore defaultCore) =
        mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      ((label, branchCore) :: restCore) defaultCore
  have hCompile :
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchCons_of_compile
        hDiscr hBranchCompile hRestCompile hDefaultCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult :=
    Stmt.switchCons_eval_tail_of_legacy
      hChecked hDiscr hNoMatch hTailSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_switchCons_eval_tail_of_legacy
        hNoMatch hTailMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchConsNoneTail_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hTailSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr rest none) =
        some sourceResult)
    (hTailMVP :
      SolidCore.Solidity.MVP.Stmt.eval state
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore SolidCore.Solidity.MVP.Stmt.skip) =
        mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.switch discr ((label, branch) :: rest) none).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) none) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
      ((label, branchCore) :: restCore)
      SolidCore.Solidity.MVP.Stmt.skip
  have hCompile :
      (Stmt.switch discr ((label, branch) :: rest) none).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_switchConsNone_of_compile
        hDiscr hBranchCompile hRestCompile
  have hSource :
      Stmt.eval (fuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) none) =
        some sourceResult :=
    Stmt.switchConsNone_eval_tail_of_legacy
      hChecked hDiscr hNoMatch hTailSource
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
    simpa [coreStmt] using
      Stmt.MVPCore_switchCons_eval_tail_of_legacy
        (defaultCore := SolidCore.Solidity.MVP.Stmt.skip)
        hNoMatch hTailMVP
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.switchNil_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefault :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state
        defaultBranch sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr [] (some defaultBranch))
      sourceResult mvpResult := by
  rcases hDefault with
    ⟨defaultCore, hDefaultCompile, hDefaultSource, hDefaultMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchNil_sourceToMVPCoreStmt_correct
      hChecked hDiscr hDefaultCompile hDefaultSource hDefaultMVP

theorem Stmt.switchNil_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefault :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        defaultBranch sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr [] (some defaultBranch))
      sourceResult mvpResult := by
  rcases hDefault with ⟨hDefaultCorrect, hDefaultRelated⟩
  exact
    ⟨Stmt.switchNil_sourceToMVPCoreStmtCorrect
        hChecked hDiscr hDefaultCorrect,
      hDefaultRelated⟩

theorem Stmt.switchNilNone_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr [] none)
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchNilNone_sourceToMVPCoreStmt_correct
      (fuel := fuel) (context := context) (runtime := runtime)
      (state := state) hChecked hDiscr

theorem Stmt.switchNilNone_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {discr : Expr} {discrLegacy : LegacyExpr}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr [] none)
      (Result.normal runtime)
      (SolidCore.Solidity.MVP.Result.normal state) := by
  exact
    ⟨Stmt.switchNilNone_sourceToMVPCoreStmtCorrect
        hChecked hDiscr,
      ⟨returnValue, hRelated⟩⟩

theorem Stmt.switchConsMatchHead_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state
        branch sourceResult mvpResult)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hDefaultCompile :
      Stmt.ToMVPCoreStmtCompiled context defaultBranch) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch))
      sourceResult mvpResult := by
  rcases hBranch with
    ⟨branchCore, hBranchCompile, hBranchSource, hBranchMVP⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  rcases hDefaultCompile with
    ⟨defaultCore, hDefaultCompile⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchConsMatchHead_sourceToMVPCoreStmt_correct
      hChecked hDiscr hMatch hBranchCompile hRestCompile
      hDefaultCompile hBranchSource hBranchMVP

theorem Stmt.switchConsMatchHead_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        branch sourceResult mvpResult)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hDefaultCompile :
      Stmt.ToMVPCoreStmtCompiled context defaultBranch) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch))
      sourceResult mvpResult := by
  rcases hBranch with ⟨hBranchCorrect, hBranchRelated⟩
  exact
    ⟨Stmt.switchConsMatchHead_sourceToMVPCoreStmtCorrect
        hChecked hDiscr hMatch hBranchCorrect hRestCompile
        hDefaultCompile,
      hBranchRelated⟩

theorem Stmt.switchConsNoneMatchHead_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.SourceToMVPCoreStmtCorrect fuel context runtime state
        branch sourceResult mvpResult)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) none)
      sourceResult mvpResult := by
  rcases hBranch with
    ⟨branchCore, hBranchCompile, hBranchSource, hBranchMVP⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchConsNoneMatchHead_sourceToMVPCoreStmt_correct
      hChecked hDiscr hMatch hBranchCompile hRestCompile
      hBranchSource hBranchMVP

theorem Stmt.switchConsNoneMatchHead_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranch :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel context runtime state
        branch sourceResult mvpResult)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) none)
      sourceResult mvpResult := by
  rcases hBranch with ⟨hBranchCorrect, hBranchRelated⟩
  exact
    ⟨Stmt.switchConsNoneMatchHead_sourceToMVPCoreStmtCorrect
        hChecked hDiscr hMatch hBranchCorrect hRestCompile,
      hBranchRelated⟩

theorem Stmt.switchConsTail_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      Stmt.ToMVPCoreStmtCompiled context branch)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hDefaultCompile :
      Stmt.ToMVPCoreStmtCompiled context defaultBranch)
    (hTail :
      Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
        (Stmt.switch discr rest (some defaultBranch))
        sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch))
      sourceResult mvpResult := by
  rcases hBranchCompile with
    ⟨branchCore, hBranchCompile⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  rcases hDefaultCompile with
    ⟨defaultCore, hDefaultCompile⟩
  rcases hTail with
    ⟨tailCore, hTailCompile, hTailSource, hTailMVP⟩
  have hTailCompileExpected :
      (Stmt.switch discr rest (some defaultBranch)).toMVPCoreUnchecked?
          context =
        some
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore defaultCore) := by
    simp [Stmt.toMVPCoreUnchecked?, Stmt.optionalToMVPCoreUnchecked?,
      hDiscr, hRestCompile, hDefaultCompile]
  rw [hTailCompileExpected] at hTailCompile
  injection hTailCompile with hTailCore
  subst tailCore
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchConsTail_sourceToMVPCoreStmt_correct
      hChecked hDiscr hNoMatch hBranchCompile hRestCompile
      hDefaultCompile hTailSource hTailMVP

theorem Stmt.switchConsTail_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      Stmt.ToMVPCoreStmtCompiled context branch)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hDefaultCompile :
      Stmt.ToMVPCoreStmtCompiled context defaultBranch)
    (hTail :
      Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
        (Stmt.switch discr rest (some defaultBranch))
        sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch))
      sourceResult mvpResult := by
  rcases hTail with ⟨hTailCorrect, hTailRelated⟩
  exact
    ⟨Stmt.switchConsTail_sourceToMVPCoreStmtCorrect
        hChecked hDiscr hNoMatch hBranchCompile hRestCompile
        hDefaultCompile hTailCorrect,
      hTailRelated⟩

theorem Stmt.switchConsNoneTail_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      Stmt.ToMVPCoreStmtCompiled context branch)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hTail :
      Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
        (Stmt.switch discr rest none)
        sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) none)
      sourceResult mvpResult := by
  rcases hBranchCompile with
    ⟨branchCore, hBranchCompile⟩
  rcases hRestCompile with
    ⟨restCore, hRestCompile⟩
  rcases hTail with
    ⟨tailCore, hTailCompile, hTailSource, hTailMVP⟩
  have hTailCompileExpected :
      (Stmt.switch discr rest none).toMVPCoreUnchecked?
          context =
        some
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore SolidCore.Solidity.MVP.Stmt.skip) := by
    simp [Stmt.toMVPCoreUnchecked?, Stmt.optionalToMVPCoreUnchecked?,
      hDiscr, hRestCompile]
  rw [hTailCompileExpected] at hTailCompile
  injection hTailCompile with hTailCore
  subst tailCore
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.switchConsNoneTail_sourceToMVPCoreStmt_correct
      hChecked hDiscr hNoMatch hBranchCompile hRestCompile
      hTailSource hTailMVP

theorem Stmt.switchConsNoneTail_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch : Stmt}
    {rest : List (Word × Stmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      Stmt.ToMVPCoreStmtCompiled context branch)
    (hRestCompile :
      Stmt.SwitchCasesToMVPCoreCasesCompiled context rest)
    (hTail :
      Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
        (Stmt.switch discr rest none)
        sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.switch discr ((label, branch) :: rest) none)
      sourceResult mvpResult := by
  rcases hTail with ⟨hTailCorrect, hTailRelated⟩
  exact
    ⟨Stmt.switchConsNoneTail_sourceToMVPCoreStmtCorrect
        hChecked hDiscr hNoMatch hBranchCompile hRestCompile
        hTailCorrect,
      hTailRelated⟩

theorem Stmt.switchNil_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt} {defaultCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hDefaultSource :
      Stmt.eval sourceFuel context runtime defaultBranch =
        some sourceResult)
    (hDefaultMVP :
      SolidCore.Solidity.MVP.Stmt.eval state defaultCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr [] (some defaultBranch)).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr [] (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr [] (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
      (Stmt.switchNil_sourceToMVPCoreStmt_correct
        hChecked hDiscr hDefaultCompile hDefaultSource hDefaultMVP)

theorem Stmt.switchConsMatchHead_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hBranchSource :
      Stmt.eval sourceFuel context runtime branch =
        some sourceResult)
    (hBranchMVP :
      SolidCore.Solidity.MVP.Stmt.eval state branchCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
      (Stmt.switchConsMatchHead_sourceToMVPCoreStmt_correct
        hChecked hDiscr hMatch hBranchCompile hRestCompile
        hDefaultCompile hBranchSource hBranchMVP)

theorem Stmt.switchConsTail_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hTailSource :
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr rest (some defaultBranch)) =
        some sourceResult)
    (hTailMVP :
      SolidCore.Solidity.MVP.Stmt.eval state
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore defaultCore) =
        mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulVia
      (Stmt.switchConsTail_sourceToMVPCoreStmt_correct
        hChecked hDiscr hNoMatch hBranchCompile hRestCompile
        hDefaultCompile hTailSource hTailMVP)

theorem Stmt.switchNil_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {defaultBranch : Stmt} {defaultCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hDefaultSource :
      Stmt.eval sourceFuel context runtime defaultBranch =
        some sourceResult)
    (hDefaultMVP :
      SolidCore.Solidity.MVP.Stmt.eval state defaultCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr [] (some defaultBranch)).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr [] (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr [] (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
      (Stmt.switchNil_sourceToMVPCoreStmt_correct
        hChecked hDiscr hDefaultCompile hDefaultSource hDefaultMVP)

theorem Stmt.switchConsMatchHead_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hMatch :
      SolidCoreYulCore.norm discrLegacy.eval =
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hBranchSource :
      Stmt.eval sourceFuel context runtime branch =
        some sourceResult)
    (hBranchMVP :
      SolidCore.Solidity.MVP.Stmt.eval state branchCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
      (Stmt.switchConsMatchHead_sourceToMVPCoreStmt_correct
        hChecked hDiscr hMatch hBranchCompile hRestCompile
        hDefaultCompile hBranchSource hBranchMVP)

theorem Stmt.switchConsTail_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {discr : Expr} {discrLegacy : LegacyExpr}
    {label : Word} {branch defaultBranch : Stmt}
    {rest : List (Word × Stmt)}
    {branchCore defaultCore : MVPCoreStmt}
    {restCore : List (Word × MVPCoreStmt)}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hChecked : context.checked = false)
    (hDiscr : discr.toLegacyUnchecked? = some discrLegacy)
    (hNoMatch :
      SolidCoreYulCore.norm discrLegacy.eval ≠
        SolidCoreYulCore.norm label)
    (hBranchCompile :
      branch.toMVPCoreUnchecked? context = some branchCore)
    (hRestCompile :
      Stmt.switchCasesToMVPCoreUnchecked? context rest =
        some restCore)
    (hDefaultCompile :
      defaultBranch.toMVPCoreUnchecked? context = some defaultCore)
    (hTailSource :
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr rest (some defaultBranch)) =
        some sourceResult)
    (hTailMVP :
      SolidCore.Solidity.MVP.Stmt.eval state
          (SolidCore.Solidity.MVP.Stmt.switchCases discrLegacy
            restCore defaultCore) =
        mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime
          (Stmt.switch discr ((label, branch) :: rest) (some defaultBranch)) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  exact
    Stmt.sourceToMVPCoreStmt_correct_toFullYulSourceVia
      (Stmt.switchConsTail_sourceToMVPCoreStmt_correct
        hChecked hDiscr hNoMatch hBranchCompile hRestCompile
        hDefaultCompile hTailSource hTailMVP)

theorem Stmt.toMVPCoreUnchecked?_unchecked_of_compile
    {context : Context} {body : Stmt} {coreStmt : MVPCoreStmt}
    (hBody :
      body.toMVPCoreUnchecked? { context with checked := false } =
        some coreStmt) :
    (Stmt.unchecked body).toMVPCoreUnchecked? context =
      some coreStmt := by
  simp [Stmt.toMVPCoreUnchecked?, hBody]

theorem Stmt.unchecked_eval_of_body
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {body : Stmt} {result : Result}
    (hBody :
      Stmt.eval fuel { context with checked := false } runtime body =
        some result) :
    Stmt.eval (fuel + 1) context runtime (Stmt.unchecked body) =
      some result := by
  simp [Stmt.eval, hBody]

theorem Stmt.unchecked_sourceToMVPCoreStmt_correct
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {body : Stmt} {bodyCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hBodyCompile :
      body.toMVPCoreUnchecked? { context with checked := false } =
        some bodyCore)
    (hBodySource :
      Stmt.eval fuel { context with checked := false } runtime body =
        some sourceResult)
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore = mvpResult) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.unchecked body).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval (fuel + 1) context runtime (Stmt.unchecked body) =
        some sourceResult ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt = mvpResult := by
  exact
    ⟨bodyCore,
      Stmt.toMVPCoreUnchecked?_unchecked_of_compile hBodyCompile,
      Stmt.unchecked_eval_of_body hBodySource,
      hBodyMVP⟩

theorem Stmt.unchecked_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {body : Stmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hBody :
      Stmt.SourceToMVPCoreStmtCorrect fuel { context with checked := false }
        runtime state body sourceResult mvpResult) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.unchecked body) sourceResult mvpResult := by
  rcases hBody with
    ⟨bodyCore, hBodyCompile, hBodySource, hBodyMVP⟩
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.unchecked_sourceToMVPCoreStmt_correct
      hBodyCompile hBodySource hBodyMVP

theorem Stmt.unchecked_sourceToMVPCoreStmtCorrectRelated_of_normal
    {fuel : Nat} {context : Context} {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : Stmt}
    (hBody :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel
        { context with checked := false } runtime state body
        (Result.normal runtime')
        (SolidCore.Solidity.MVP.Result.normal state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.unchecked body) (Result.normal runtime')
      (SolidCore.Solidity.MVP.Result.normal state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.unchecked_sourceToMVPCoreStmtCorrect hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.ofUncheckedContext⟩⟩

theorem Stmt.unchecked_sourceToMVPCoreStmtCorrectRelated_of_returnedWord
    {fuel : Nat} {context : Context} {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : Stmt} {value : Word}
    (hBody :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel
        { context with checked := false } runtime state body
        (Result.returned runtime' [Value.word value])
        (SolidCore.Solidity.MVP.Result.returned state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.unchecked body)
      (Result.returned runtime' [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  exact
    ⟨Stmt.unchecked_sourceToMVPCoreStmtCorrect hBodyCorrect,
      hBodyRelated.ofUncheckedContext⟩

theorem Stmt.unchecked_sourceToMVPCoreStmtCorrectRelated_of_reverted
    {fuel : Nat} {context : Context} {runtime runtime' : Runtime}
    {state state' : SolidCore.Solidity.MVP.State}
    {body : Stmt} {data : RevertData}
    (hBody :
      Stmt.SourceToMVPCoreStmtCorrectRelated fuel
        { context with checked := false } runtime state body
        (Result.reverted runtime' data)
        (SolidCore.Solidity.MVP.Result.reverted state')) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime
      state (Stmt.unchecked body)
      (Result.reverted runtime' data)
      (SolidCore.Solidity.MVP.Result.reverted state') := by
  rcases hBody with ⟨hBodyCorrect, hBodyRelated⟩
  rcases hBodyRelated with ⟨returnValue, hRuntimeRelated⟩
  exact
    ⟨Stmt.unchecked_sourceToMVPCoreStmtCorrect hBodyCorrect,
      ⟨returnValue, hRuntimeRelated.ofUncheckedContext⟩⟩

theorem Stmt.unchecked_toFullYulViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {body : Stmt} {bodyCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hBodyCompile :
      body.toMVPCoreUnchecked? { context with checked := false } =
        some bodyCore)
    (hBodySource :
      Stmt.eval sourceFuel { context with checked := false } runtime body =
        some sourceResult)
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.unchecked body).toFullYulViaMVPCoreUnchecked? context =
        some yulStmt ∧
      (Stmt.unchecked body).toFullYulViaMVPCoreUncheckedFuel? context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.unchecked body) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.unchecked_sourceToMVPCoreStmt_correct
        hBodyCompile hBodySource hBodyMVP with
    ⟨coreStmt, hCoreCompile, hSource, hCoreEval⟩
  let program : MVPCoreProgram := { body := coreStmt }
  have hProgram :
      (Stmt.unchecked body).toMVPCoreProgramUnchecked? context =
        some program := by
    simp [Stmt.toMVPCoreProgramUnchecked?, hCoreCompile, program]
  have hProgramEval :
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        mvpResult := by
    simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
      using hCoreEval
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state hProgramEval with
    ⟨yulStmt, yulFuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, yulFuel, hCompile, hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.unchecked_toFullYulSourceViaMVPCore_correct
    {sourceFuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {body : Stmt} {bodyCore : MVPCoreStmt}
    {sourceResult : Result}
    {mvpResult : SolidCore.Solidity.MVP.Result}
    (hBodyCompile :
      body.toMVPCoreUnchecked? { context with checked := false } =
        some bodyCore)
    (hBodySource :
      Stmt.eval sourceFuel { context with checked := false } runtime body =
        some sourceResult)
    (hBodyMVP :
      SolidCore.Solidity.MVP.Stmt.eval state bodyCore = mvpResult) :
    ∃ yulStmt : YulStmt, ∃ yulFuel : Nat,
      (Stmt.unchecked body).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.unchecked body).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some yulFuel ∧
      Stmt.eval (sourceFuel + 1) context runtime (Stmt.unchecked body) =
        some sourceResult ∧
      SolidCoreYulCore.SymYul.evalStmtFuel yulFuel
          state.toConfig yulStmt =
        mvpResult.toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        yulFuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.unchecked_toFullYulViaMVPCore_correct
        hBodyCompile hBodySource hBodyMVP with
    ⟨yulStmt, yulFuel, hCoreCompile, hFuel, hSource, hYul,
      hAccepted⟩
  exact
    ⟨yulStmt, yulFuel,
      Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
        hCoreCompile,
      hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.toMVPCoreUnchecked?_revert_of_compile
    {context : Context} {name : String} {exprs : List Expr}
    {legacies : List LegacyExpr}
    (hArgs :
      Expr.listToLegacyUnchecked? exprs = some legacies) :
    (Stmt.revert name exprs).toMVPCoreUnchecked? context =
      some SolidCore.Solidity.MVP.Stmt.revert := by
  simp [Stmt.toMVPCoreUnchecked?, hArgs]

theorem Stmt.revert_sourceToMVPCoreStmtCorrect
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {name : String} {exprs : List Expr}
    {legacies : List LegacyExpr} {values : List Value}
    (hArgs :
      Expr.listToLegacyUnchecked? exprs = some legacies)
    (hSourceArgs :
      Expr.evalList context runtime exprs = Except.ok values) :
    Stmt.SourceToMVPCoreStmtCorrect (fuel + 1) context runtime state
      (Stmt.revert name exprs)
      (Result.reverted runtime (RevertData.custom name values))
      (SolidCore.Solidity.MVP.Result.reverted state) := by
  exact
    ⟨SolidCore.Solidity.MVP.Stmt.revert,
      Stmt.toMVPCoreUnchecked?_revert_of_compile hArgs,
      by
        simp [Stmt.eval, hSourceArgs, Bind.bind, Except.bind],
      by simp [SolidCore.Solidity.MVP.Stmt.eval]⟩

theorem Stmt.revert_sourceToMVPCoreStmtCorrectRelated
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {name : String} {exprs : List Expr}
    {legacies : List LegacyExpr} {values : List Value}
    (hArgs :
      Expr.listToLegacyUnchecked? exprs = some legacies)
    (hSourceArgs :
      Expr.evalList context runtime exprs = Except.ok values)
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    Stmt.SourceToMVPCoreStmtCorrectRelated (fuel + 1) context runtime state
      (Stmt.revert name exprs)
      (Result.reverted runtime (RevertData.custom name values))
      (SolidCore.Solidity.MVP.Result.reverted state) := by
  exact
    ⟨Stmt.revert_sourceToMVPCoreStmtCorrect
        hArgs hSourceArgs,
      Result.RelatesMVPCore.reverted_of_related hRelated⟩

theorem Stmt.revert_sourceToMVPCoreStmtCorrectRelated_of_checked_false
    {fuel : Nat} {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {name : String} {exprs : List Expr}
    {legacies : List LegacyExpr}
    (hChecked : context.checked = false)
    (hArgs :
      Expr.listToLegacyUnchecked? exprs = some legacies)
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state) :
    ∃ values : List Value,
      Stmt.SourceToMVPCoreStmtCorrectRelated
        (fuel + 1) context runtime state
        (Stmt.revert name exprs)
        (Result.reverted runtime (RevertData.custom name values))
        (SolidCore.Solidity.MVP.Result.reverted state) := by
  obtain ⟨values, hSourceArgs⟩ :=
    Expr.listToLegacyUnchecked?_evalList_runtime_of_checked_false
      context hChecked runtime hArgs
  exact
    ⟨values,
      Stmt.revert_sourceToMVPCoreStmtCorrectRelated
        hArgs hSourceArgs hRelated⟩

theorem Stmt.toMVPCoreUnchecked?_returnStateExpr_of_expr
    (context : Context)
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr) :
    (Stmt.returnValues [expr]).toMVPCoreUnchecked? context =
      some (SolidCore.Solidity.MVP.Stmt.returnStateExpr stateExpr) := by
  simp [Stmt.toMVPCoreUnchecked?, hExpr]

theorem Stmt.returnStateExpr_sourceToMVPCoreStmt_correct_of_expr
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.returnValues [expr]).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value)) := by
  let coreStmt :=
    SolidCore.Solidity.MVP.Stmt.returnStateExpr stateExpr
  have hCompile :
      (Stmt.returnValues [expr]).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_returnStateExpr_of_expr
        context hExpr
  have hSource :
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) := by
    simp [Stmt.eval, Expr.evalList, hSourceExpr, Bind.bind, Except.bind]
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value)) := by
    simp [coreStmt, SolidCore.Solidity.MVP.Stmt.eval,
      SolidCore.Solidity.MVP.State.withReturn, hMVPExpr]
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.returnStateExpr_sourceToMVPCoreStmtCorrect_of_expr
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    Stmt.SourceToMVPCoreStmtCorrect 1 context runtime state
      (Stmt.returnValues [expr])
      (Result.returned runtime [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned
        (state.withReturn
          (SolidCoreYulCore.FullYul.Value.word value))) := by
  simpa [Stmt.SourceToMVPCoreStmtCorrect] using
    Stmt.returnStateExpr_sourceToMVPCoreStmt_correct_of_expr
      context runtime state hExpr hSourceExpr hMVPExpr

theorem Stmt.returnStateExpr_sourceToMVPCoreStmtCorrect_of_expr_related
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    Stmt.SourceToMVPCoreStmtCorrect 1 context runtime state
      (Stmt.returnValues [expr])
      (Result.returned runtime [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned
        (state.withReturn
          (SolidCoreYulCore.FullYul.Value.word value))) ∧
    Result.RelatesMVPCore context
      (Result.returned runtime [Value.word value])
      (SolidCore.Solidity.MVP.Result.returned
        (state.withReturn
          (SolidCoreYulCore.FullYul.Value.word value))) := by
  exact
    ⟨Stmt.returnStateExpr_sourceToMVPCoreStmtCorrect_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr,
      Result.RelatesMVPCore.returnedWord_of_related
        hRelated.withReturn⟩

theorem Stmt.returnStateExpr_sourceToMVPCoreStmtCorrectRelated
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {returnValue : SolidCoreYulCore.FullYul.Value}
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word,
      Stmt.SourceToMVPCoreStmtCorrectRelated 1 context runtime state
        (Stmt.returnValues [expr])
        (Result.returned runtime [Value.word value])
        (SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value))) := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  have hRelatedOriginal :
      Runtime.MVPStateRelated context runtime returnValue state :=
    ⟨hReturn, hStorage⟩
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage_norm
        hChecked hStorage hExpr with
    ⟨value, hSourceExpr, _hValueNorm, hMVPExpr⟩
  exact
    ⟨value,
      Stmt.returnStateExpr_sourceToMVPCoreStmtCorrect_of_expr_related
        context runtime state hRelatedOriginal hExpr hSourceExpr
        hMVPExpr⟩

theorem Stmt.returnStateExpr_sourceToMVPCore_correct_of_expr
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    ∃ program : MVPCoreProgram,
      (Stmt.returnValues [expr]).toMVPCoreProgramUnchecked? context =
        some program ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value)) := by
  rcases
      Stmt.returnStateExpr_sourceToMVPCoreStmt_correct_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr with
    ⟨coreStmt, hCoreStmt, hSource, hCore⟩
  let program : MVPCoreProgram := { body := coreStmt }
  have hProgram :
      (Stmt.returnValues [expr]).toMVPCoreProgramUnchecked? context =
        some program := by
    simp [Stmt.toMVPCoreProgramUnchecked?, hCoreStmt, program]
  have hMVP :
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value)) := by
    simpa [program, SolidCore.Solidity.MVP.SourceProgram.eval]
        using hCore
  exact ⟨program, hProgram, hSource, hMVP⟩

theorem Stmt.returnStateExpr_sourceToMVPCore_correct_of_storage
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word, ∃ program : MVPCoreProgram,
      (Stmt.returnValues [expr]).toMVPCoreProgramUnchecked? context =
        some program ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCore.Solidity.MVP.SourceProgram.eval state program =
        SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value)) := by
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
        hChecked hStorage hExpr with
    ⟨value, hSourceExpr, hMVPExpr⟩
  rcases
      Stmt.returnStateExpr_sourceToMVPCore_correct_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr with
    ⟨program, hProgram, hSource, hMVP⟩
  exact ⟨value, program, hProgram, hSource, hMVP⟩

theorem Stmt.returnStateExpr_toFullYulViaMVPCore_correct_of_expr
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUnchecked? context =
        some yulStmt ∧
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some fuel ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value))).toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.returnStateExpr_sourceToMVPCore_correct_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr with
    ⟨program, hProgram, hSource, hMVP⟩
  rcases
      Stmt.toFullYulViaMVPCoreUnchecked?_correct_of_core_eval
        hProgram state hMVP with
    ⟨yulStmt, fuel, hCompile, hFuel, hYul, hAccepted⟩
  exact
    ⟨yulStmt, fuel, hCompile, hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.returnStateExpr_toFullYulSourceViaMVPCore_correct_of_expr
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    {expr : Expr} {stateExpr : MVPStateExpr} {value : Word}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr)
    (hSourceExpr :
      expr.eval context runtime = Except.ok (Value.word value))
    (hMVPExpr :
      SolidCore.Solidity.MVP.StateExpr.eval state stateExpr =
        SolidCoreYulCore.FullYul.Value.word value) :
    ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      (Stmt.returnValues [expr]).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some fuel ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value))).toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.returnStateExpr_toFullYulViaMVPCore_correct_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr with
    ⟨yulStmt, fuel, hCoreCompile, hFuel, hSource, hYul, hAccepted⟩
  exact
    ⟨yulStmt, fuel,
        Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
          hCoreCompile,
        hFuel, hSource, hYul, hAccepted⟩

theorem Stmt.returnStateExpr_toFullYulViaMVPCore_correct_of_storage
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word, ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUnchecked? context =
        some yulStmt ∧
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some fuel ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value))).toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
        hChecked hStorage hExpr with
    ⟨value, hSourceExpr, hMVPExpr⟩
  rcases
      Stmt.returnStateExpr_toFullYulViaMVPCore_correct_of_expr
        context runtime state hExpr hSourceExpr hMVPExpr with
    ⟨yulStmt, fuel, hCompile, hFuel, hSource, hYul, hAccepted⟩
  exact
    ⟨value, yulStmt, fuel, hCompile, hFuel, hSource, hYul,
      hAccepted⟩

theorem Stmt.returnStateExpr_toFullYulSourceViaMVPCore_correct_of_storage
    {context : Context} {runtime : Runtime}
    {state : SolidCore.Solidity.MVP.State}
    (hChecked : context.checked = false)
    (hStorage :
      ∀ {name : String} {slot : Word},
        context.storageSlot? name = some slot ->
        SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
          SolidCoreYulCore.FullYul.Value.word
            (runtime.state.loadSlot slot))
    {expr : Expr} {stateExpr : MVPStateExpr}
    (hExpr :
      expr.toMVPStateUnchecked? context = some stateExpr) :
    ∃ value : Word, ∃ yulStmt : YulStmt, ∃ fuel : Nat,
      (Stmt.returnValues [expr]).toFullYulSourceViaMVPCoreUnchecked?
          context =
        some yulStmt ∧
      (Stmt.returnValues [expr]).toFullYulViaMVPCoreUncheckedFuel?
          context =
        some fuel ∧
      Stmt.eval 1 context runtime (Stmt.returnValues [expr]) =
        some (Result.returned runtime [Value.word value]) ∧
      SolidCoreYulCore.SymYul.evalStmtFuel fuel
          state.toConfig yulStmt =
        (SolidCore.Solidity.MVP.Result.returned
          (state.withReturn
            (SolidCoreYulCore.FullYul.Value.word value))).toSymYulResults ∧
      SolidCoreYulCore.FullYul.CompilerAcceptedStmt
        SolidCoreYulCore.FullYul.CompilerProfile.currentSolidCore
        fuel SolidCore.Solidity.MVP.initialStaticContext false true
        yulStmt SolidCore.Solidity.MVP.initialStaticContext := by
  rcases
      Stmt.returnStateExpr_toFullYulViaMVPCore_correct_of_storage
        hChecked hStorage hExpr with
    ⟨value, yulStmt, fuel, hCoreCompile, hFuel, hSource, hYul,
      hAccepted⟩
  exact
    ⟨value, yulStmt, fuel,
        Stmt.toFullYulSourceViaMVPCoreUnchecked?_eq_core_of_core
          hCoreCompile,
        hFuel, hSource, hYul, hAccepted⟩

def Stmt.storageAssignMVPCoreStmt
    (slot : Word) (rhs : MVPStateExpr) : MVPCoreStmt :=
  SolidCore.Solidity.MVP.Stmt.storeStateExpr
    (SolidCore.Solidity.Expr.lit slot) rhs

theorem Stmt.toMVPCoreUnchecked?_storageAssign
    (context : Context) (name : String) (slot : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState) :
    (Stmt.assign (LValue.storage name) rhs).toMVPCoreUnchecked? context =
      some (Stmt.storageAssignMVPCoreStmt slot rhsState) := by
  simp [Stmt.toMVPCoreUnchecked?, hSlot, hRhs,
    Stmt.storageAssignMVPCoreStmt]

theorem Stmt.storageAssign_eval_of_rhs
    (context : Context) (runtime : Runtime)
    (name : String) (slot assignedValue : Word)
    {rhs : Expr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhsEval :
      rhs.eval context runtime =
        Except.ok (Value.word assignedValue)) :
    Stmt.eval 1 context runtime
        (Stmt.assign (LValue.storage name) rhs) =
      some
        (Result.normal
          { runtime with
            state :=
              runtime.state.storeSlot slot
                (SolidCoreYulCore.norm assignedValue) }) := by
  simp [Stmt.eval, LValue.write, Runtime.storeStorageField,
    Value.expectWord, hRhsEval, hSlot, State.storeSlot,
    WordMap.insertLoop, norm_norm, Bind.bind, Except.bind]

theorem Stmt.storageAssignMVPCoreStmt_eval_of_rhs
    (slot : Word) (assignedValue : SolidCoreYulCore.FullYul.Value)
    (rhsState : MVPStateExpr)
    (state : SolidCore.Solidity.MVP.State)
    (hRhsEval :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsState =
        assignedValue) :
    SolidCore.Solidity.MVP.Stmt.eval state
        (Stmt.storageAssignMVPCoreStmt slot rhsState) =
      SolidCore.Solidity.MVP.Result.normal
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot) assignedValue) := by
  simp [Stmt.storageAssignMVPCoreStmt,
    SolidCore.Solidity.MVP.Stmt.eval, hRhsEval]

theorem Stmt.toMVPCoreUnchecked?_storageAssignOp
    (context : Context) (name : String) (slot : Word)
    {op : BinaryOp} {rhs : Expr}
    {rhsState : MVPStateExpr}
    {mk : MVPStateExpr -> MVPStateExpr -> MVPStateExpr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState)
    (hOp : op.toMVPStateExpr? = some mk) :
    (Stmt.assignOp (LValue.storage name) op rhs).toMVPCoreUnchecked?
        context =
      some
        (Stmt.storageAssignMVPCoreStmt slot
          (mk
            (SolidCore.Solidity.MVP.StateExpr.load
              (SolidCore.Solidity.Expr.lit slot))
            rhsState)) := by
  simp [Stmt.toMVPCoreUnchecked?, hSlot, hRhs, hOp,
    Stmt.storageAssignMVPCoreStmt]

theorem Stmt.storageAssignOp_eval_of_rhs
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (name : String) (slot rhsValue : Word)
    {op : BinaryOp} {rhs : Expr}
    {eval : Word -> Word -> Word}
    (hSlot : context.storageSlot? name = some slot)
    (hRhsEval :
      rhs.eval context runtime =
        Except.ok (Value.word rhsValue))
    (hEval : op.evalMVPWord? = some eval) :
    Stmt.eval 1 context runtime
        (Stmt.assignOp (LValue.storage name) op rhs) =
      some
        (Result.normal
          { runtime with
            state :=
              runtime.state.storeSlot slot
                (eval (runtime.state.loadSlot slot) rhsValue) }) := by
  have hApply :
      BinaryOp.apply false op
          (Value.word (runtime.state.loadSlot slot))
          (Value.word rhsValue) =
        Except.ok
          (Value.word
            (eval (runtime.state.loadSlot slot) rhsValue)) :=
    BinaryOp.apply_evalMVPWord? hEval
      (runtime.state.loadSlot slot) rhsValue
  simp [Stmt.eval, LValue.read, LValue.write,
    Runtime.loadStorageField, Runtime.storeStorageField,
    Value.expectWord, hSlot, hRhsEval, hChecked, hApply,
    State.storeSlot_norm_value, Bind.bind, Except.bind]

theorem Stmt.storageAssignOp_sourceToMVPCore_correct_of_rhs
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (name : String) (slot rhsValue : Word)
    {op : BinaryOp} {rhs : Expr}
    {rhsState : MVPStateExpr}
    {mk : MVPStateExpr -> MVPStateExpr -> MVPStateExpr}
    {eval : Word -> Word -> Word}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState)
    (hOp : op.toMVPStateExpr? = some mk)
    (hEval : op.evalMVPWord? = some eval)
    (hSourceRhs :
      rhs.eval context runtime =
        Except.ok (Value.word rhsValue))
    (hMVPLhs :
      SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
        SolidCoreYulCore.FullYul.Value.word
          (runtime.state.loadSlot slot))
    (hMVPRhs :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsState =
        SolidCoreYulCore.FullYul.Value.word rhsValue) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.assignOp (LValue.storage name) op rhs).toMVPCoreUnchecked?
          context =
        some coreStmt ∧
      Stmt.eval 1 context runtime
          (Stmt.assignOp (LValue.storage name) op rhs) =
        some
          (Result.normal
            { runtime with
              state :=
                runtime.state.storeSlot slot
                  (eval (runtime.state.loadSlot slot) rhsValue) }) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word
              (eval (runtime.state.loadSlot slot) rhsValue))) := by
  let rhsCore :=
    mk
      (SolidCore.Solidity.MVP.StateExpr.load
        (SolidCore.Solidity.Expr.lit slot))
      rhsState
  let coreStmt := Stmt.storageAssignMVPCoreStmt slot rhsCore
  have hCompile :
      (Stmt.assignOp (LValue.storage name) op rhs).toMVPCoreUnchecked?
          context =
        some coreStmt := by
    simpa [coreStmt, rhsCore] using
      Stmt.toMVPCoreUnchecked?_storageAssignOp
        context name slot hSlot hRhs hOp
  have hSource :
      Stmt.eval 1 context runtime
          (Stmt.assignOp (LValue.storage name) op rhs) =
        some
          (Result.normal
            { runtime with
              state :=
                runtime.state.storeSlot slot
                  (eval (runtime.state.loadSlot slot) rhsValue) }) :=
    Stmt.storageAssignOp_eval_of_rhs
      context hChecked runtime name slot rhsValue
      hSlot hSourceRhs hEval
  have hRhsCore :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsCore =
        SolidCoreYulCore.FullYul.Value.word
          (eval (runtime.state.loadSlot slot) rhsValue) := by
    simpa [rhsCore] using
      BinaryOp.toMVPStateExpr?_evalMVPWord?_eval
        hOp hEval state hMVPLhs hMVPRhs
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word
              (eval (runtime.state.loadSlot slot) rhsValue))) := by
    simpa [coreStmt] using
      Stmt.storageAssignMVPCoreStmt_eval_of_rhs
        slot
        (SolidCoreYulCore.FullYul.Value.word
          (eval (runtime.state.loadSlot slot) rhsValue))
        rhsCore state hRhsCore
  exact ⟨coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.storageAssignOp_sourceToMVPCoreStmtCorrectRelated
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {op : BinaryOp} {rhs : Expr}
    {rhsState : MVPStateExpr}
    {mk : MVPStateExpr -> MVPStateExpr -> MVPStateExpr}
    {eval : Word -> Word -> Word}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState)
    (hOp : op.toMVPStateExpr? = some mk)
    (hEval : op.evalMVPWord? = some eval) :
    ∃ rhsValue assignedValue : Word,
      assignedValue = eval (runtime.state.loadSlot slot) rhsValue ∧
      SolidCoreYulCore.norm assignedValue = assignedValue ∧
      Stmt.SourceToMVPCoreStmtCorrectRelated 1 context runtime state
        (Stmt.assignOp (LValue.storage name) op rhs)
        (Result.normal
          { runtime with
            state := runtime.state.storeSlot slot assignedValue })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  have hRelatedOriginal :
      Runtime.MVPStateRelated context runtime returnValue state :=
    ⟨hReturn, hStorage⟩
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage
        hChecked hStorage hRhs with
    ⟨rhsValue, hSourceRhs, hMVPRhs⟩
  let assignedValue := eval (runtime.state.loadSlot slot) rhsValue
  have hAssignedNorm :
      SolidCoreYulCore.norm assignedValue = assignedValue := by
    simpa [assignedValue] using
      (BinaryOp.evalMVPWord?_norm_result hEval
        (runtime.state.loadSlot slot) rhsValue).symm
  have hMVPLhs :
      SolidCore.Solidity.MVP.StateExpr.eval state
          (SolidCore.Solidity.MVP.StateExpr.load
            (SolidCore.Solidity.Expr.lit slot)) =
        SolidCoreYulCore.FullYul.Value.word
          (runtime.state.loadSlot slot) :=
    hStorage hSlot
  have hCorrect :=
    Stmt.storageAssignOp_sourceToMVPCore_correct_of_rhs
      context hChecked runtime state name slot rhsValue
      hSlot hRhs hOp hEval hSourceRhs hMVPLhs hMVPRhs
  have hRelatedAfter :
      Runtime.MVPStateRelated context
        { runtime with
          state := runtime.state.storeSlot slot assignedValue }
        returnValue
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot)
          (SolidCoreYulCore.FullYul.Value.word assignedValue)) :=
    hRelatedOriginal.storeSlot_storeValue
      (slot := slot) (value := assignedValue) hAssignedNorm
  exact
    ⟨rhsValue, assignedValue, rfl, hAssignedNorm,
      ⟨by
          simpa [Stmt.SourceToMVPCoreStmtCorrect,
          assignedValue] using hCorrect,
        ⟨returnValue, hRelatedAfter⟩⟩⟩

theorem Stmt.storageAssignOp_sourceToMVPCoreStmtCorrectRelated_of_op
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {op : BinaryOp} {rhs : Expr}
    {rhsState : MVPStateExpr}
    {mk : MVPStateExpr -> MVPStateExpr -> MVPStateExpr}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState)
    (hOp : op.toMVPStateExpr? = some mk) :
    ∃ eval : Word -> Word -> Word,
    ∃ rhsValue assignedValue : Word,
      op.evalMVPWord? = some eval ∧
      assignedValue = eval (runtime.state.loadSlot slot) rhsValue ∧
      SolidCoreYulCore.norm assignedValue = assignedValue ∧
      Stmt.SourceToMVPCoreStmtCorrectRelated 1 context runtime state
        (Stmt.assignOp (LValue.storage name) op rhs)
        (Result.normal
          { runtime with
            state := runtime.state.storeSlot slot assignedValue })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) := by
  have hEvalExists :
      ∃ eval, op.evalMVPWord? = some eval :=
    (BinaryOp.toMVPStateExpr?_eq_some_iff_evalMVPWord?
      (op := op)).mp ⟨mk, hOp⟩
  rcases hEvalExists with ⟨eval, hEval⟩
  rcases
      Stmt.storageAssignOp_sourceToMVPCoreStmtCorrectRelated
        context hChecked runtime state returnValue name slot
        hRelated hSlot hRhs hOp hEval with
    ⟨rhsValue, assignedValue, hAssigned, hAssignedNorm, hCorrect⟩
  exact
    ⟨eval, rhsValue, assignedValue, hEval, hAssigned,
      hAssignedNorm, hCorrect⟩

theorem Stmt.storageAssign_sourceToMVPCore_correct_of_rhs
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (name : String) (slot assignedValue : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs :
      rhs.toMVPStateUnchecked? context = some rhsState)
    (hSourceRhs :
      rhs.eval context runtime =
        Except.ok (Value.word assignedValue))
    (hMVPRhs :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsState =
        storageWordValue assignedValue) :
    ∃ coreStmt : MVPCoreStmt,
      (Stmt.assign (LValue.storage name) rhs).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval 1 context runtime
          (Stmt.assign (LValue.storage name) rhs) =
        some
          (Result.normal
            { runtime with
              state :=
                runtime.state.storeSlot slot
                  (SolidCoreYulCore.norm assignedValue) }) ∧
      SolidCore.Solidity.MVP.Stmt.eval state coreStmt =
        SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (storageWordValue assignedValue)) := by
  let coreStmt := Stmt.storageAssignMVPCoreStmt slot rhsState
  exact
    ⟨coreStmt,
      by
        simpa [coreStmt] using
          Stmt.toMVPCoreUnchecked?_storageAssign
            context name slot hSlot hRhs,
      Stmt.storageAssign_eval_of_rhs
        context runtime name slot assignedValue hSlot hSourceRhs,
      by
        simpa [coreStmt] using
          Stmt.storageAssignMVPCoreStmt_eval_of_rhs
            slot (storageWordValue assignedValue)
            rhsState state hMVPRhs⟩

theorem Stmt.storageAssign_sourceToMVPCoreStmtCorrect_of_rhs_related
    (context : Context) (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot assignedValue : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hSlot : context.storageSlot? name = some slot)
    (hRhs :
      rhs.toMVPStateUnchecked? context = some rhsState)
    (hSourceRhs :
      rhs.eval context runtime =
        Except.ok (Value.word assignedValue))
    (hMVPRhs :
      SolidCore.Solidity.MVP.StateExpr.eval state rhsState =
        storageWordValue assignedValue) :
    Stmt.SourceToMVPCoreStmtCorrect 1 context runtime state
      (Stmt.assign (LValue.storage name) rhs)
      (Result.normal
        { runtime with
          state :=
            runtime.state.storeSlot slot
              (SolidCoreYulCore.norm assignedValue) })
      (SolidCore.Solidity.MVP.Result.normal
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot)
          (storageWordValue assignedValue))) ∧
    Result.RelatesMVPCore context
      (Result.normal
        { runtime with
          state :=
            runtime.state.storeSlot slot
              (SolidCoreYulCore.norm assignedValue) })
      (SolidCore.Solidity.MVP.Result.normal
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot)
          (storageWordValue assignedValue))) := by
  have hCorrect :=
    Stmt.storageAssign_sourceToMVPCore_correct_of_rhs
      context runtime state name slot assignedValue
      hSlot hRhs hSourceRhs hMVPRhs
  have hRelatedAfter :
      Runtime.MVPStateRelated context
        { runtime with
          state :=
            runtime.state.storeSlot slot
              (SolidCoreYulCore.norm assignedValue) }
        returnValue
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot)
          (storageWordValue assignedValue)) :=
    hRelated.storeSlot_storeValue
      (slot := slot) (value := SolidCoreYulCore.norm assignedValue)
      (norm_norm assignedValue)
  exact
    ⟨by simpa [Stmt.SourceToMVPCoreStmtCorrect] using hCorrect,
      ⟨returnValue, hRelatedAfter⟩⟩

theorem Stmt.storageAssign_sourceToMVPCoreStmtCorrect_related
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hSlot : context.storageSlot? name = some slot)
    (hRhs :
      rhs.toMVPStateUnchecked? context = some rhsState) :
    ∃ assignedValue : Word,
      SolidCoreYulCore.norm assignedValue = assignedValue ∧
      Stmt.SourceToMVPCoreStmtCorrect 1 context runtime state
        (Stmt.assign (LValue.storage name) rhs)
        (Result.normal
          { runtime with
            state := runtime.state.storeSlot slot assignedValue })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) ∧
      Result.RelatesMVPCore context
        (Result.normal
          { runtime with
            state := runtime.state.storeSlot slot assignedValue })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) := by
  rcases hRelated with ⟨hReturn, hStorage⟩
  have hRelatedOriginal :
      Runtime.MVPStateRelated context runtime returnValue state :=
    ⟨hReturn, hStorage⟩
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_of_storage_norm
        hChecked hStorage hRhs with
    ⟨assignedValue, hSourceRhs, hAssignedNorm, hMVPRhs⟩
  have hCorrect :=
    Stmt.storageAssign_sourceToMVPCore_correct_of_rhs
      context runtime state name slot assignedValue
      hSlot hRhs hSourceRhs
      (by simpa [storageWordValue, hAssignedNorm] using hMVPRhs)
  have hRelatedAfter :
      Runtime.MVPStateRelated context
        { runtime with
          state := runtime.state.storeSlot slot assignedValue }
        returnValue
        (SolidCore.Solidity.MVP.State.storeValue state
          (SolidCore.Solidity.Expr.lit slot)
          (SolidCoreYulCore.FullYul.Value.word assignedValue)) :=
    hRelatedOriginal.storeSlot_storeValue
      (slot := slot) (value := assignedValue) hAssignedNorm
  exact
    ⟨assignedValue, hAssignedNorm,
      by
        simpa [Stmt.SourceToMVPCoreStmtCorrect, hAssignedNorm,
          storageWordValue] using hCorrect,
      ⟨returnValue, hRelatedAfter⟩⟩

theorem Stmt.storageAssign_sourceToMVPCoreStmtCorrectRelated
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (state : SolidCore.Solidity.MVP.State)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hRelated :
      Runtime.MVPStateRelated context runtime returnValue state)
    (hSlot : context.storageSlot? name = some slot)
    (hRhs :
      rhs.toMVPStateUnchecked? context = some rhsState) :
    ∃ assignedValue : Word,
      SolidCoreYulCore.norm assignedValue = assignedValue ∧
      Stmt.SourceToMVPCoreStmtCorrectRelated 1 context runtime state
        (Stmt.assign (LValue.storage name) rhs)
        (Result.normal
          { runtime with
            state := runtime.state.storeSlot slot assignedValue })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue state
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) := by
  rcases
      Stmt.storageAssign_sourceToMVPCoreStmtCorrect_related
        context hChecked runtime state returnValue name slot
        hRelated hSlot hRhs with
    ⟨assignedValue, hNorm, hCorrect, hRelatedResult⟩
  exact ⟨assignedValue, hNorm, hCorrect, hRelatedResult⟩

theorem Stmt.storageAssign_sourceToMVPCore_correct
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState) :
    ∃ assignedValue : Word, ∃ coreStmt : MVPCoreStmt,
      (Stmt.assign (LValue.storage name) rhs).toMVPCoreUnchecked? context =
        some coreStmt ∧
      Stmt.eval 1 context runtime
          (Stmt.assign (LValue.storage name) rhs) =
        some
          (Result.normal
            { runtime with
              state :=
                runtime.state.storeSlot slot
                  (SolidCoreYulCore.norm assignedValue) }) ∧
      SolidCore.Solidity.MVP.Stmt.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          coreStmt =
        SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue
            (Runtime.toMVPStateWithContext context runtime returnValue)
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue)) := by
  rcases
      Expr.toMVPStateUnchecked?_eval_runtime_toMVPStateWithContext
        context hChecked runtime returnValue hRhs with
    ⟨assignedValue, hSourceRhs, hMVPRhs⟩
  let coreStmt := Stmt.storageAssignMVPCoreStmt slot rhsState
  have hCompile :
      (Stmt.assign (LValue.storage name) rhs).toMVPCoreUnchecked? context =
        some coreStmt := by
    simpa [coreStmt] using
      Stmt.toMVPCoreUnchecked?_storageAssign
        context name slot hSlot hRhs
  have hSource :
      Stmt.eval 1 context runtime
          (Stmt.assign (LValue.storage name) rhs) =
        some
          (Result.normal
            { runtime with
              state :=
                runtime.state.storeSlot slot
                  (SolidCoreYulCore.norm assignedValue) }) :=
    Stmt.storageAssign_eval_of_rhs
      context runtime name slot assignedValue hSlot hSourceRhs
  have hMVP :
      SolidCore.Solidity.MVP.Stmt.eval
          (Runtime.toMVPStateWithContext context runtime returnValue)
          coreStmt =
        SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue
            (Runtime.toMVPStateWithContext context runtime returnValue)
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue)) := by
    simpa [coreStmt] using
      Stmt.storageAssignMVPCoreStmt_eval_of_rhs
        slot (SolidCoreYulCore.FullYul.Value.word assignedValue)
        rhsState
        (Runtime.toMVPStateWithContext context runtime returnValue)
        hMVPRhs
  exact ⟨assignedValue, coreStmt, hCompile, hSource, hMVP⟩

theorem Stmt.storageAssign_sourceToMVPCoreStmtCorrect
    (context : Context) (hChecked : context.checked = false)
    (runtime : Runtime)
    (returnValue : SolidCoreYulCore.FullYul.Value)
    (name : String) (slot : Word)
    {rhs : Expr} {rhsState : MVPStateExpr}
    (hSlot : context.storageSlot? name = some slot)
    (hRhs : rhs.toMVPStateUnchecked? context = some rhsState) :
    ∃ assignedValue : Word,
      Stmt.SourceToMVPCoreStmtCorrect 1 context runtime
        (Runtime.toMVPStateWithContext context runtime returnValue)
        (Stmt.assign (LValue.storage name) rhs)
        (Result.normal
          { runtime with
            state :=
              runtime.state.storeSlot slot
                (SolidCoreYulCore.norm assignedValue) })
        (SolidCore.Solidity.MVP.Result.normal
          (SolidCore.Solidity.MVP.State.storeValue
            (Runtime.toMVPStateWithContext context runtime returnValue)
            (SolidCore.Solidity.Expr.lit slot)
            (SolidCoreYulCore.FullYul.Value.word assignedValue))) := by
  rcases
      Stmt.storageAssign_sourceToMVPCore_correct
        context hChecked runtime returnValue name slot hSlot hRhs with
    ⟨assignedValue, coreStmt, hCompile, hSource, hMVP⟩
  exact
    ⟨assignedValue, coreStmt, hCompile, hSource, hMVP⟩

end Source
end Solidity
end SolidCore

import SolidCore.Spine.L02_AbstractYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P02_ValidSolidityToAbstractYul

structure Artifact where
  program : L02_AbstractYul.Program
  wf : L02_AbstractYul.WF program

structure CheckedExpr (source : L01_ValidSolidity.Expr) where
  expr : L02_AbstractYul.Expr
  core_eq : expr.toCore? = source.toCore?
  eval_eq : expr.eval? = source.eval?

def compileExprChecked? :
    (source : L01_ValidSolidity.Expr) -> Option (CheckedExpr source)
  | L01_ValidSolidity.Expr.literal
      L01_ValidSolidity.Ty.bool
      (L01_ValidSolidity.Literal.bool value) =>
      some
        { expr := L02_AbstractYul.Expr.bool value
          core_eq := by rfl
          eval_eq := by cases value <;> rfl }
  | L01_ValidSolidity.Expr.literal
      (L01_ValidSolidity.Ty.uint 256)
      (L01_ValidSolidity.Literal.word value) =>
      some
        { expr := L02_AbstractYul.Expr.word value
          core_eq := by rfl
          eval_eq := by rfl }
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.add lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.add
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.add,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.add,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.sub lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.sub
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.sub,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.sub,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.mul lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.mul
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.mul,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.mul,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.bitAnd lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.bitAnd
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.bitAnd,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.bitAnd,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.lt lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.ltOp
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.ltOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.ltOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.gt lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.gtOp
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.gtOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.gtOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.eq lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          some
            { expr :=
                L02_AbstractYul.Expr.eqOp
                  lhsChecked.expr rhsChecked.expr
              core_eq := by
                simp [L02_AbstractYul.Expr.eqOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq]
              eval_eq := by
                simp [L02_AbstractYul.Expr.eval?,
                  L01_ValidSolidity.Expr.eval?,
                  L02_AbstractYul.Expr.eqOp,
                  L02_AbstractYul.Expr.toCore?,
                  L02_AbstractYul.BinaryOp.toCore?,
                  L01_ValidSolidity.Expr.toCore?,
                  L01_ValidSolidity.BinaryOp.toCore?,
                  lhsChecked.core_eq, rhsChecked.core_eq] }
      | _, _ => none
  | _ => none

def compileExpr? (source : L01_ValidSolidity.Expr) :
    Option L02_AbstractYul.Expr :=
  match compileExprChecked? source with
  | some checked => some checked.expr
  | none => none

structure CheckedStmt (source : L01_ValidSolidity.Stmt) where
  stmt : L02_AbstractYul.Stmt
  sourceExpr : L01_ValidSolidity.Expr
  targetExpr : L02_AbstractYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : stmt.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def checkedIfElse
    (condition : L01_ValidSolidity.Expr)
    (thenBranch elseBranch : L01_ValidSolidity.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (conditionValue : L01_ValidSolidity.Word)
    (hConditionEval : condition.eval? = some conditionValue) :
    CheckedStmt
      (L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch) :=
  if hCondition :
      SolidCore.Solidity.Source.wordTruthy conditionValue then
    { stmt :=
        L02_AbstractYul.Stmt.ifElse conditionChecked.expr
          thenChecked.stmt elseChecked.stmt
      sourceExpr := thenChecked.sourceExpr
      targetExpr := thenChecked.targetExpr
      sourceReturned := by
        simp [L01_ValidSolidity.Stmt.returnedExpr?,
          hConditionEval, hCondition,
          thenChecked.sourceReturned]
      targetReturned := by
        have hTargetEval :
            conditionChecked.expr.eval? =
              some conditionValue := by
          rw [conditionChecked.eval_eq, hConditionEval]
        simp [L02_AbstractYul.Stmt.returnedExpr?,
          hTargetEval, hCondition,
          thenChecked.targetReturned]
      eval_eq := thenChecked.eval_eq }
  else
    { stmt :=
        L02_AbstractYul.Stmt.ifElse conditionChecked.expr
          thenChecked.stmt elseChecked.stmt
      sourceExpr := elseChecked.sourceExpr
      targetExpr := elseChecked.targetExpr
      sourceReturned := by
        simp [L01_ValidSolidity.Stmt.returnedExpr?,
          hConditionEval, hCondition,
          elseChecked.sourceReturned]
      targetReturned := by
        have hTargetEval :
            conditionChecked.expr.eval? =
              some conditionValue := by
          rw [conditionChecked.eval_eq, hConditionEval]
        simp [L02_AbstractYul.Stmt.returnedExpr?,
          hTargetEval, hCondition,
          elseChecked.targetReturned]
      eval_eq := elseChecked.eval_eq }

def checkedIfElseOfEvalSome
    (condition : L01_ValidSolidity.Expr)
    (thenBranch elseBranch : L01_ValidSolidity.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (hConditionEvalSome : condition.eval?.isSome = true) :
    CheckedStmt
      (L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch) :=
  match hConditionEval : condition.eval? with
  | some conditionValue =>
      checkedIfElse condition thenBranch elseBranch
        conditionChecked thenChecked elseChecked
        conditionValue hConditionEval
  | none => by
      simp [hConditionEval] at hConditionEvalSome

theorem checkedIfElseOfEvalSome_stmt
    (condition : L01_ValidSolidity.Expr)
    (thenBranch elseBranch : L01_ValidSolidity.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (hConditionEvalSome : condition.eval?.isSome = true) :
    (checkedIfElseOfEvalSome condition thenBranch elseBranch
      conditionChecked thenChecked elseChecked
      hConditionEvalSome).stmt =
      L02_AbstractYul.Stmt.ifElse
        conditionChecked.expr thenChecked.stmt elseChecked.stmt := by
  unfold checkedIfElseOfEvalSome
  split
  · rename_i conditionValue hConditionEval
    by_cases hTruth :
        SolidCore.Solidity.Source.wordTruthy conditionValue = true
    · simp [checkedIfElse, hTruth]
    · simp [checkedIfElse, hTruth]
  · rename_i hConditionEval
    simp [hConditionEval] at hConditionEvalSome

def compileStmtChecked? :
    (source : L01_ValidSolidity.Stmt) -> Option (CheckedStmt source)
  | L01_ValidSolidity.Stmt.returnValues [sourceExpr] =>
      if sourceExpr.resultTyIsUint256 then
        match compileExprChecked? sourceExpr with
        | some checked =>
            some
              { stmt := L02_AbstractYul.Stmt.returnExpr checked.expr
                sourceExpr := sourceExpr
                targetExpr := checked.expr
                sourceReturned := by rfl
                targetReturned := by rfl
                eval_eq := checked.eval_eq }
        | none => none
      else
        none
  | L01_ValidSolidity.Stmt.block [] [sourceStmt] =>
      match compileStmtChecked? sourceStmt with
      | some checked =>
          some
            { stmt := L02_AbstractYul.Stmt.block [checked.stmt]
              sourceExpr := checked.sourceExpr
              targetExpr := checked.targetExpr
              sourceReturned := by
                simp [L01_ValidSolidity.Stmt.returnedExpr?,
                  checked.sourceReturned]
              targetReturned := by
                simp [L02_AbstractYul.Stmt.returnedExpr?,
                  checked.targetReturned]
              eval_eq := checked.eval_eq }
      | none => none
  | L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch =>
      if condition.resultTyIsBool then
        match compileExprChecked? condition,
            compileStmtChecked? thenBranch,
            compileStmtChecked? elseBranch with
        | some conditionChecked, some thenChecked, some elseChecked =>
            if hConditionEvalSome : condition.eval?.isSome = true then
              some
                (checkedIfElseOfEvalSome condition thenBranch elseBranch
                  conditionChecked thenChecked elseChecked
                  hConditionEvalSome)
            else
              none
        | _, _, _ => none
      else
        none
  | _ => none

structure CheckedFunction (source : L01_ValidSolidity.FunctionDecl) where
  entry : L02_AbstractYul.Entry
  sourceExpr : L01_ValidSolidity.Expr
  targetExpr : L02_AbstractYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : entry.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def compileFunctionChecked? :
    (fn : L01_ValidSolidity.FunctionDecl) ->
      Option (CheckedFunction fn)
  | { id := id
      params := []
      returns := [ret]
      visibility := L01_ValidSolidity.Visibility.public_
      mutability := L01_ValidSolidity.StateMutability.pure
      modifiers := []
      body := some body
      .. } =>
      if hRet : ret.isUint256 then
        match compileStmtChecked? body with
        | some checked =>
            some
              { entry :=
                  L02_AbstractYul.Entry.withSourceBody id
                    checked.stmt
                sourceExpr := checked.sourceExpr
                targetExpr := checked.targetExpr
                sourceReturned := by
                  simp [L01_ValidSolidity.FunctionDecl.returnedExpr?,
                    hRet, checked.sourceReturned]
                targetReturned := by
                  simp [L02_AbstractYul.Entry.withSourceBody,
                    L02_AbstractYul.Entry.returnedExpr?,
                    checked.targetReturned]
                eval_eq := checked.eval_eq }
        | none => none
      else
        none
  | _ => none

structure CheckedContract (source : L01_ValidSolidity.ContractDecl) where
  entry : L02_AbstractYul.Entry
  sourceExpr : L01_ValidSolidity.Expr
  targetExpr : L02_AbstractYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : entry.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def compileContractChecked? :
    (contract : L01_ValidSolidity.ContractDecl) ->
      Option (CheckedContract contract)
  | { bases := []
      linearizedBases := []
      storage := []
      functions := [fn]
      modifiers := []
      events := []
      errors := []
      structs := []
      enums := []
      .. } =>
      match compileFunctionChecked? fn with
      | some checked =>
          some
            { entry := checked.entry
              sourceExpr := checked.sourceExpr
              targetExpr := checked.targetExpr
              sourceReturned := by
                simp [L01_ValidSolidity.ContractDecl.returnedExpr?,
                  checked.sourceReturned]
              targetReturned := checked.targetReturned
              eval_eq := checked.eval_eq }
      | none => none
  | _ => none

structure CheckedProgram (source : L01_ValidSolidity.Program) where
  program : L02_AbstractYul.Program
  wf : L02_AbstractYul.WF program
  sourceExpr : L01_ValidSolidity.Expr
  targetExpr : L02_AbstractYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : program.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def compileProgramChecked? :
    (program : L01_ValidSolidity.Program) ->
      Option (CheckedProgram program)
  | { contracts := [contract], entryContract := some entry } =>
      if hEntry : entry.value == contract.id.value then
        match compileContractChecked? contract with
        | some checked =>
            some
              { program := L02_AbstractYul.Program.withEntry checked.entry
                wf := by exact {}
                sourceExpr := checked.sourceExpr
                targetExpr := checked.targetExpr
                sourceReturned := by
                  simp [L01_ValidSolidity.Program.returnedExpr?,
                    hEntry, checked.sourceReturned]
                targetReturned := by
                  simp [L02_AbstractYul.Program.withEntry,
                    L02_AbstractYul.Program.returnedExpr?,
                    checked.targetReturned]
                eval_eq := checked.eval_eq }
        | none => none
      else
        none
  | _ => none

def structuralExprTarget? :
    L01_ValidSolidity.Expr -> Option L02_AbstractYul.Expr
  | L01_ValidSolidity.Expr.literal
      L01_ValidSolidity.Ty.bool
      (L01_ValidSolidity.Literal.bool value) =>
      some (L02_AbstractYul.Expr.bool value)
  | L01_ValidSolidity.Expr.literal
      (L01_ValidSolidity.Ty.uint 256)
      (L01_ValidSolidity.Literal.word value) =>
      some (L02_AbstractYul.Expr.word value)
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.add lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.add lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.sub lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.sub lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.mul lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.mul lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.bitAnd lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.bitAnd lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.lt lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.ltOp lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.gt lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.gtOp lhsTarget rhsTarget)
      | _, _ => none
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.eq lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          some (L02_AbstractYul.Expr.eqOp lhsTarget rhsTarget)
      | _, _ => none
  | _ => none

def structuralExprAccepted? (expr : L01_ValidSolidity.Expr) : Bool :=
  (structuralExprTarget? expr).isSome

def structuralStmtTarget? :
    L01_ValidSolidity.Stmt -> Option L02_AbstractYul.Stmt
  | L01_ValidSolidity.Stmt.returnValues [sourceExpr] =>
      if sourceExpr.resultTyIsUint256 then
        match structuralExprTarget? sourceExpr with
        | some targetExpr =>
            some (L02_AbstractYul.Stmt.returnExpr targetExpr)
        | none => none
      else
        none
  | L01_ValidSolidity.Stmt.block [] [sourceStmt] =>
      match structuralStmtTarget? sourceStmt with
      | some targetStmt =>
          some (L02_AbstractYul.Stmt.block [targetStmt])
      | none => none
  | L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch =>
      if condition.resultTyIsBool then
        match structuralExprTarget? condition,
            structuralStmtTarget? thenBranch,
            structuralStmtTarget? elseBranch with
        | some targetCondition, some targetThen, some targetElse =>
            match condition.eval? with
            | some _ =>
                some
                  (L02_AbstractYul.Stmt.ifElse targetCondition
                    targetThen targetElse)
            | none => none
        | _, _, _ => none
      else
        none
  | _ => none

def structuralStmtAccepted? (stmt : L01_ValidSolidity.Stmt) : Bool :=
  (structuralStmtTarget? stmt).isSome

def structuralFunctionTarget? :
    L01_ValidSolidity.FunctionDecl -> Option L02_AbstractYul.Entry
  | { id := id
      params := []
      returns := [ret]
      visibility := L01_ValidSolidity.Visibility.public_
      mutability := L01_ValidSolidity.StateMutability.pure
      modifiers := []
      body := some body
      .. } =>
      if ret.isUint256 then
        match structuralStmtTarget? body with
        | some targetBody =>
            some (L02_AbstractYul.Entry.withSourceBody id targetBody)
        | none => none
      else
        none
  | _ => none

def structuralFunctionAccepted? (fn : L01_ValidSolidity.FunctionDecl) : Bool :=
  (structuralFunctionTarget? fn).isSome

def structuralContractTarget? :
    L01_ValidSolidity.ContractDecl -> Option L02_AbstractYul.Entry
  | { bases := []
      linearizedBases := []
      storage := []
      functions := [fn]
      modifiers := []
      events := []
      errors := []
      structs := []
      enums := []
      .. } =>
      structuralFunctionTarget? fn
  | _ => none

def structuralContractAccepted?
    (contract : L01_ValidSolidity.ContractDecl) : Bool :=
  (structuralContractTarget? contract).isSome

def structuralProgramTarget? :
    L01_ValidSolidity.Program -> Option L02_AbstractYul.Program
  | { contracts := [contract], entryContract := some entry } =>
      if entry.value == contract.id.value then
        match structuralContractTarget? contract with
        | some targetEntry =>
            some (L02_AbstractYul.Program.withEntry targetEntry)
        | none => none
      else
        none
  | _ => none

def programEmptyShape? (program : L01_ValidSolidity.Program) : Bool :=
  match program.contracts, program.entryContract with
  | [], none => true
  | _, _ => false

def accepted? (program : L01_ValidSolidity.Program) : Bool :=
  if programEmptyShape? program then
    true
  else
    (structuralProgramTarget? program).isSome

def Accepted (program : L01_ValidSolidity.Program) : Prop :=
  accepted? program = true

theorem accepted?_eq_true_iff (program : L01_ValidSolidity.Program) :
    accepted? program = true ↔ Accepted program := by
  rfl

theorem compileExprChecked?_structuralExprTarget? :
    ∀ {source : L01_ValidSolidity.Expr}
      {checked : CheckedExpr source},
      compileExprChecked? source = some checked ->
        structuralExprTarget? source = some checked.expr
  | L01_ValidSolidity.Expr.literal ty lit, checked, hCompile => by
      cases ty <;> try simp [compileExprChecked?] at hCompile
      case bool =>
        cases lit <;> try simp [compileExprChecked?] at hCompile
        case bool value =>
          cases hCompile
          simp [structuralExprTarget?]
      case uint bits =>
        cases lit <;> try simp [compileExprChecked?] at hCompile
        case word value =>
          by_cases hBits : bits = 256
          · subst bits
            simp [compileExprChecked?] at hCompile
            cases hCompile
            simp [structuralExprTarget?]
          · simp [compileExprChecked?, hBits] at hCompile
  | L01_ValidSolidity.Expr.binary ty op lhs rhs, checked, hCompile => by
      cases ty <;> try simp [compileExprChecked?] at hCompile
      case bool =>
        cases op <;> try simp [compileExprChecked?] at hCompile
        case lt =>
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
              | some rhsChecked =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
                  cases hCompile
                  have hLhsStructural :
                      structuralExprTarget? lhs =
                        some lhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hLhs
                  have hRhsStructural :
                      structuralExprTarget? rhs =
                        some rhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hRhs
                  simp [structuralExprTarget?, hLhsStructural,
                    hRhsStructural]
        case gt =>
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
              | some rhsChecked =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
                  cases hCompile
                  have hLhsStructural :
                      structuralExprTarget? lhs =
                        some lhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hLhs
                  have hRhsStructural :
                      structuralExprTarget? rhs =
                        some rhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hRhs
                  simp [structuralExprTarget?, hLhsStructural,
                    hRhsStructural]
        case eq =>
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
              | some rhsChecked =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
                  cases hCompile
                  have hLhsStructural :
                      structuralExprTarget? lhs =
                        some lhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hLhs
                  have hRhsStructural :
                      structuralExprTarget? rhs =
                        some rhsChecked.expr :=
                    compileExprChecked?_structuralExprTarget? hRhs
                  simp [structuralExprTarget?, hLhsStructural,
                    hRhsStructural]
      case uint bits =>
        cases op <;> try simp [compileExprChecked?] at hCompile
        case add =>
          by_cases hBits : bits = 256
          · subst bits
            cases hLhs : compileExprChecked? lhs with
            | none =>
                simp [compileExprChecked?, hLhs] at hCompile
            | some lhsChecked =>
                cases hRhs : compileExprChecked? rhs with
                | none =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                | some rhsChecked =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                    cases hCompile
                    have hLhsStructural :
                        structuralExprTarget? lhs =
                          some lhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hLhs
                    have hRhsStructural :
                        structuralExprTarget? rhs =
                          some rhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hRhs
                    simp [structuralExprTarget?, hLhsStructural,
                      hRhsStructural]
          · simp [compileExprChecked?, hBits] at hCompile
        case sub =>
          by_cases hBits : bits = 256
          · subst bits
            cases hLhs : compileExprChecked? lhs with
            | none =>
                simp [compileExprChecked?, hLhs] at hCompile
            | some lhsChecked =>
                cases hRhs : compileExprChecked? rhs with
                | none =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                | some rhsChecked =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                    cases hCompile
                    have hLhsStructural :
                        structuralExprTarget? lhs =
                          some lhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hLhs
                    have hRhsStructural :
                        structuralExprTarget? rhs =
                          some rhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hRhs
                    simp [structuralExprTarget?, hLhsStructural,
                      hRhsStructural]
          · simp [compileExprChecked?, hBits] at hCompile
        case mul =>
          by_cases hBits : bits = 256
          · subst bits
            cases hLhs : compileExprChecked? lhs with
            | none =>
                simp [compileExprChecked?, hLhs] at hCompile
            | some lhsChecked =>
                cases hRhs : compileExprChecked? rhs with
                | none =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                | some rhsChecked =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                    cases hCompile
                    have hLhsStructural :
                        structuralExprTarget? lhs =
                          some lhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hLhs
                    have hRhsStructural :
                        structuralExprTarget? rhs =
                          some rhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hRhs
                    simp [structuralExprTarget?, hLhsStructural,
                      hRhsStructural]
          · simp [compileExprChecked?, hBits] at hCompile
        case bitAnd =>
          by_cases hBits : bits = 256
          · subst bits
            cases hLhs : compileExprChecked? lhs with
            | none =>
                simp [compileExprChecked?, hLhs] at hCompile
            | some lhsChecked =>
                cases hRhs : compileExprChecked? rhs with
                | none =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                | some rhsChecked =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                    cases hCompile
                    have hLhsStructural :
                        structuralExprTarget? lhs =
                          some lhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hLhs
                    have hRhsStructural :
                        structuralExprTarget? rhs =
                          some rhsChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hRhs
                    simp [structuralExprTarget?, hLhsStructural,
                      hRhsStructural]
          · simp [compileExprChecked?, hBits] at hCompile
  | L01_ValidSolidity.Expr.read _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.functionRef _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.eventRef _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.errorRef _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.unary _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.ternary _ _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.tuple _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.array _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.call _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.callWithValue _ _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.memberValue _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L01_ValidSolidity.Expr.assignment _ _ _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile

theorem compileStmtChecked?_structuralStmtTarget? :
    ∀ {source : L01_ValidSolidity.Stmt}
      {checked : CheckedStmt source},
      compileStmtChecked? source = some checked ->
        structuralStmtTarget? source = some checked.stmt
  | L01_ValidSolidity.Stmt.returnValues exprs, checked, hCompile => by
      cases exprs with
      | nil =>
          simp [compileStmtChecked?] at hCompile
      | cons sourceExpr rest =>
          cases rest with
          | nil =>
              by_cases hTy :
                  sourceExpr.resultTyIsUint256 = true
              · cases hExpr : compileExprChecked? sourceExpr with
                | none =>
                    simp [compileStmtChecked?, hTy, hExpr] at hCompile
                | some exprChecked =>
                    simp [compileStmtChecked?, hTy, hExpr] at hCompile
                    cases hCompile
                    have hExprStructural :
                        structuralExprTarget? sourceExpr =
                          some exprChecked.expr :=
                      compileExprChecked?_structuralExprTarget? hExpr
                    simp [structuralStmtTarget?, hTy, hExprStructural]
              · simp [compileStmtChecked?, hTy] at hCompile
          | cons _ _ =>
              simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.block locals stmts, checked, hCompile => by
      cases locals with
      | cons _ _ =>
          simp [compileStmtChecked?] at hCompile
      | nil =>
          cases stmts with
          | nil =>
              simp [compileStmtChecked?] at hCompile
          | cons sourceStmt rest =>
              cases rest with
              | nil =>
                  cases hStmt : compileStmtChecked? sourceStmt with
                  | none =>
                      simp [compileStmtChecked?, hStmt] at hCompile
                  | some stmtChecked =>
                      simp [compileStmtChecked?, hStmt] at hCompile
                      cases hCompile
                      have hStmtStructural :
                          structuralStmtTarget? sourceStmt =
                            some stmtChecked.stmt :=
                        compileStmtChecked?_structuralStmtTarget? hStmt
                      simp [structuralStmtTarget?, hStmtStructural]
              | cons _ _ =>
                  simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch, checked,
      hCompile => by
      by_cases hTy : condition.resultTyIsBool = true
      · cases hCondition :
            compileExprChecked? condition with
        | none =>
            simp [compileStmtChecked?, hTy, hCondition] at hCompile
        | some conditionChecked =>
            cases hThen :
                compileStmtChecked? thenBranch with
            | none =>
                simp [compileStmtChecked?, hTy, hCondition, hThen]
                  at hCompile
            | some thenChecked =>
                cases hElse :
                    compileStmtChecked? elseBranch with
                | none =>
                    simp [compileStmtChecked?, hTy, hCondition, hThen,
                      hElse] at hCompile
                | some elseChecked =>
                    by_cases hConditionEvalSome :
                        condition.eval?.isSome = true
                    · simp [compileStmtChecked?, hTy, hCondition, hThen,
                        hElse, hConditionEvalSome] at hCompile
                      cases hCompile
                      have hConditionStructural :
                          structuralExprTarget? condition =
                            some conditionChecked.expr :=
                        compileExprChecked?_structuralExprTarget? hCondition
                      have hThenStructural :
                          structuralStmtTarget? thenBranch =
                            some thenChecked.stmt :=
                        compileStmtChecked?_structuralStmtTarget? hThen
                      have hElseStructural :
                          structuralStmtTarget? elseBranch =
                            some elseChecked.stmt :=
                        compileStmtChecked?_structuralStmtTarget? hElse
                      have hConditionEvalExists :
                          ∃ conditionValue,
                            condition.eval? = some conditionValue := by
                        cases hConditionEval : condition.eval? with
                        | none =>
                            simp [hConditionEval] at hConditionEvalSome
                        | some conditionValue =>
                            exact ⟨conditionValue, rfl⟩
                      rcases hConditionEvalExists with
                        ⟨conditionValue, hConditionEval⟩
                      have hCheckedStmt :
                          (checkedIfElseOfEvalSome condition thenBranch
                              elseBranch conditionChecked thenChecked
                              elseChecked hConditionEvalSome).stmt =
                            L02_AbstractYul.Stmt.ifElse
                              conditionChecked.expr thenChecked.stmt
                              elseChecked.stmt := by
                        exact
                          checkedIfElseOfEvalSome_stmt
                            condition thenBranch elseBranch
                            conditionChecked thenChecked elseChecked
                            hConditionEvalSome
                      simp [structuralStmtTarget?, hTy,
                        hConditionStructural, hThenStructural,
                        hElseStructural, hConditionEval,
                        hCheckedStmt]
                    · simp [compileStmtChecked?, hTy, hCondition, hThen,
                        hElse, hConditionEvalSome] at hCompile
      · simp [compileStmtChecked?, hTy] at hCompile
  | L01_ValidSolidity.Stmt.skip, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.expr _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.assign _ _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.whileLoop _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.doWhile _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.forLoop _ _ _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.tryCatch _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.emitEvent _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.revert _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.«break», checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.«continue», checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.unchecked _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L01_ValidSolidity.Stmt.modifierPlaceholder, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile

theorem compileFunctionChecked?_structuralFunctionTarget?
    {source : L01_ValidSolidity.FunctionDecl}
    {checked : CheckedFunction source}
    (hCompile : compileFunctionChecked? source = some checked) :
    structuralFunctionTarget? source = some checked.entry := by
  cases source with
  | mk id sourceName contract params returns visibility mutability
      modifiers body virtual overrides =>
      cases params with
      | cons _ _ =>
          simp [compileFunctionChecked?] at hCompile
      | nil =>
          cases returns with
          | nil =>
              simp [compileFunctionChecked?] at hCompile
          | cons ret returnRest =>
              cases returnRest with
              | cons _ _ =>
                  simp [compileFunctionChecked?] at hCompile
              | nil =>
                  cases visibility <;>
                    try simp [compileFunctionChecked?] at hCompile
                  case public_ =>
                    cases mutability <;>
                      try simp [compileFunctionChecked?] at hCompile
                    case pure =>
                      cases modifiers with
                      | cons _ _ =>
                          simp [compileFunctionChecked?] at hCompile
                      | nil =>
                          cases body with
                          | none =>
                              simp [compileFunctionChecked?] at hCompile
                          | some bodyStmt =>
                              cases hRet : ret.isUint256 with
                              | false =>
                                  simp [compileFunctionChecked?, hRet]
                                    at hCompile
                              | true =>
                                  cases hStmt :
                                      compileStmtChecked? bodyStmt with
                                  | none =>
                                      simp [compileFunctionChecked?,
                                        hRet, hStmt] at hCompile
                                  | some stmtChecked =>
                                      simp [compileFunctionChecked?,
                                        hRet, hStmt] at hCompile
                                      cases hCompile
                                      have hStmtStructural :
                                          structuralStmtTarget? bodyStmt =
                                            some stmtChecked.stmt :=
                                        compileStmtChecked?_structuralStmtTarget?
                                          hStmt
                                      simp [structuralFunctionTarget?,
                                        hRet, hStmtStructural]

theorem compileContractChecked?_structuralContractTarget?
    {source : L01_ValidSolidity.ContractDecl}
    {checked : CheckedContract source}
    (hCompile : compileContractChecked? source = some checked) :
    structuralContractTarget? source = some checked.entry := by
  cases source with
  | mk id sourceName bases linearizedBases storage functions
      modifiers events errors structs enums =>
      cases bases with
      | cons _ _ =>
          simp [compileContractChecked?] at hCompile
      | nil =>
          cases linearizedBases with
          | cons _ _ =>
              simp [compileContractChecked?] at hCompile
          | nil =>
              cases storage with
              | cons _ _ =>
                  simp [compileContractChecked?] at hCompile
              | nil =>
                  cases functions with
                  | nil =>
                      simp [compileContractChecked?] at hCompile
                  | cons fn functionRest =>
                      cases functionRest with
                      | cons _ _ =>
                          simp [compileContractChecked?] at hCompile
                      | nil =>
                          cases modifiers with
                          | cons _ _ =>
                              simp [compileContractChecked?] at hCompile
                          | nil =>
                              cases events with
                              | cons _ _ =>
                                  simp [compileContractChecked?] at hCompile
                              | nil =>
                                  cases errors with
                                  | cons _ _ =>
                                      simp [compileContractChecked?]
                                        at hCompile
                                  | nil =>
                                      cases structs with
                                      | cons _ _ =>
                                          simp [compileContractChecked?]
                                            at hCompile
                                      | nil =>
                                          cases enums with
                                          | cons _ _ =>
                                              simp [compileContractChecked?]
                                                at hCompile
                                          | nil =>
                                              cases hFn :
                                                  compileFunctionChecked? fn with
                                              | none =>
                                                  simp [compileContractChecked?,
                                                    hFn] at hCompile
                                              | some fnChecked =>
                                                  simp [compileContractChecked?,
                                                    hFn] at hCompile
                                                  cases hCompile
                                                  have hFnStructural :
                                                      structuralFunctionTarget? fn =
                                                        some fnChecked.entry :=
                                                    compileFunctionChecked?_structuralFunctionTarget?
                                                      hFn
                                                  simp [structuralContractTarget?,
                                                    hFnStructural]

theorem compileProgramChecked?_structuralProgramTarget?
    {source : L01_ValidSolidity.Program}
    {checked : CheckedProgram source}
    (hCompile : compileProgramChecked? source = some checked) :
    structuralProgramTarget? source = some checked.program := by
  cases source with
  | mk contracts entryContract =>
      cases contracts with
      | nil =>
          simp [compileProgramChecked?] at hCompile
      | cons contract contractRest =>
          cases contractRest with
          | cons _ _ =>
              simp [compileProgramChecked?] at hCompile
          | nil =>
              cases entryContract with
              | none =>
                  simp [compileProgramChecked?] at hCompile
              | some entry =>
                  cases hEntry : entry.value == contract.id.value with
                  | false =>
                      simp [compileProgramChecked?, hEntry] at hCompile
                  | true =>
                      cases hContract :
                          compileContractChecked? contract with
                      | none =>
                          simp [compileProgramChecked?, hEntry, hContract]
                            at hCompile
                      | some contractChecked =>
                          simp [compileProgramChecked?, hEntry, hContract]
                            at hCompile
                          cases hCompile
                          have hContractStructural :
                              structuralContractTarget? contract =
                                some contractChecked.entry :=
                            compileContractChecked?_structuralContractTarget?
                              hContract
                          simp [structuralProgramTarget?, hEntry,
                            hContractStructural]

theorem structuralExprTarget?_compileExprChecked?_exists :
    ∀ {source : L01_ValidSolidity.Expr}
      {target : L02_AbstractYul.Expr},
      structuralExprTarget? source = some target ->
        ∃ checked : CheckedExpr source,
          compileExprChecked? source = some checked
  | L01_ValidSolidity.Expr.literal ty lit, target, hStructural => by
      cases ty <;> try simp [structuralExprTarget?] at hStructural
      case bool =>
        cases lit <;> try simp [structuralExprTarget?] at hStructural
        case bool value =>
          exact
            ⟨{ expr := L02_AbstractYul.Expr.bool value
               core_eq := by rfl
               eval_eq := by cases value <;> rfl },
              by rfl⟩
      case uint bits =>
        cases lit <;> try simp [structuralExprTarget?] at hStructural
        case word value =>
          by_cases hBits : bits = 256
          · subst bits
            exact
              ⟨{ expr := L02_AbstractYul.Expr.word value
                 core_eq := by rfl
                 eval_eq := by rfl },
                by rfl⟩
          · simp [structuralExprTarget?, hBits] at hStructural
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.add lhs rhs,
      target, hStructural => by
      cases hLhs : structuralExprTarget? lhs with
      | none =>
          simp [structuralExprTarget?, hLhs] at hStructural
      | some lhsTarget =>
          cases hRhs : structuralExprTarget? rhs with
          | none =>
              simp [structuralExprTarget?, hLhs, hRhs] at hStructural
          | some rhsTarget =>
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hLhs with
                ⟨lhsChecked, hLhsCompile⟩
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hRhs with
                ⟨rhsChecked, hRhsCompile⟩
              cases hCompile :
                  compileExprChecked?
                    (L01_ValidSolidity.Expr.binary
                      (L01_ValidSolidity.Ty.uint 256)
                      L01_ValidSolidity.BinaryOp.add lhs rhs) with
              | none =>
                  simp [compileExprChecked?, hLhsCompile,
                    hRhsCompile] at hCompile
              | some checked =>
                  exact ⟨checked, rfl⟩
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.sub lhs rhs,
      target, hStructural => by
      cases hLhs : structuralExprTarget? lhs with
      | none =>
          simp [structuralExprTarget?, hLhs] at hStructural
      | some lhsTarget =>
          cases hRhs : structuralExprTarget? rhs with
          | none =>
              simp [structuralExprTarget?, hLhs, hRhs] at hStructural
          | some rhsTarget =>
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hLhs with
                ⟨lhsChecked, hLhsCompile⟩
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hRhs with
                ⟨rhsChecked, hRhsCompile⟩
              cases hCompile :
                  compileExprChecked?
                    (L01_ValidSolidity.Expr.binary
                      (L01_ValidSolidity.Ty.uint 256)
                      L01_ValidSolidity.BinaryOp.sub lhs rhs) with
              | none =>
                  simp [compileExprChecked?, hLhsCompile,
                    hRhsCompile] at hCompile
              | some checked =>
                  exact ⟨checked, rfl⟩
  | L01_ValidSolidity.Expr.binary
      (L01_ValidSolidity.Ty.uint 256)
      L01_ValidSolidity.BinaryOp.mul lhs rhs,
      target, hStructural => by
      cases hLhs : structuralExprTarget? lhs with
      | none =>
          simp [structuralExprTarget?, hLhs] at hStructural
      | some lhsTarget =>
          cases hRhs : structuralExprTarget? rhs with
          | none =>
              simp [structuralExprTarget?, hLhs, hRhs] at hStructural
          | some rhsTarget =>
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hLhs with
                ⟨lhsChecked, hLhsCompile⟩
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hRhs with
                ⟨rhsChecked, hRhsCompile⟩
              cases hCompile :
                  compileExprChecked?
                    (L01_ValidSolidity.Expr.binary
                      (L01_ValidSolidity.Ty.uint 256)
                      L01_ValidSolidity.BinaryOp.mul lhs rhs) with
              | none =>
                  simp [compileExprChecked?, hLhsCompile,
                    hRhsCompile] at hCompile
              | some checked =>
                  exact ⟨checked, rfl⟩
  | L01_ValidSolidity.Expr.binary
      L01_ValidSolidity.Ty.bool
      L01_ValidSolidity.BinaryOp.eq lhs rhs,
      target, hStructural => by
      cases hLhs : structuralExprTarget? lhs with
      | none =>
          simp [structuralExprTarget?, hLhs] at hStructural
      | some lhsTarget =>
          cases hRhs : structuralExprTarget? rhs with
          | none =>
              simp [structuralExprTarget?, hLhs, hRhs] at hStructural
          | some rhsTarget =>
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hLhs with
                ⟨lhsChecked, hLhsCompile⟩
              rcases
                structuralExprTarget?_compileExprChecked?_exists
                  hRhs with
                ⟨rhsChecked, hRhsCompile⟩
              cases hCompile :
                  compileExprChecked?
                    (L01_ValidSolidity.Expr.binary
                      L01_ValidSolidity.Ty.bool
                      L01_ValidSolidity.BinaryOp.eq lhs rhs) with
              | none =>
                  simp [compileExprChecked?, hLhsCompile,
                    hRhsCompile] at hCompile
              | some checked =>
                  exact ⟨checked, rfl⟩
  | L01_ValidSolidity.Expr.binary ty op lhs rhs, target, hStructural => by
      cases ty <;> try simp [structuralExprTarget?] at hStructural
      case bool =>
        cases op <;> try simp [structuralExprTarget?] at hStructural
        case lt =>
          cases hLhs : structuralExprTarget? lhs with
          | none =>
              simp [hLhs] at hStructural
          | some lhsTarget =>
              cases hRhs : structuralExprTarget? rhs with
              | none =>
                  simp [hLhs, hRhs] at hStructural
              | some rhsTarget =>
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile⟩
                  cases hCompile :
                      compileExprChecked?
                        (L01_ValidSolidity.Expr.binary
                          L01_ValidSolidity.Ty.bool
                          L01_ValidSolidity.BinaryOp.lt lhs rhs) with
                  | none =>
                      simp [compileExprChecked?, hLhsCompile,
                        hRhsCompile] at hCompile
                  | some checked =>
                      exact ⟨checked, rfl⟩
        case gt =>
          cases hLhs : structuralExprTarget? lhs with
          | none =>
              simp [hLhs] at hStructural
          | some lhsTarget =>
              cases hRhs : structuralExprTarget? rhs with
              | none =>
                  simp [hLhs, hRhs] at hStructural
              | some rhsTarget =>
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile⟩
                  cases hCompile :
                      compileExprChecked?
                        (L01_ValidSolidity.Expr.binary
                          L01_ValidSolidity.Ty.bool
                          L01_ValidSolidity.BinaryOp.gt lhs rhs) with
                  | none =>
                      simp [compileExprChecked?, hLhsCompile,
                        hRhsCompile] at hCompile
                  | some checked =>
                      exact ⟨checked, rfl⟩
        case eq =>
          cases hLhs : structuralExprTarget? lhs with
          | none =>
              simp [hLhs] at hStructural
          | some lhsTarget =>
              cases hRhs : structuralExprTarget? rhs with
              | none =>
                  simp [hLhs, hRhs] at hStructural
              | some rhsTarget =>
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile⟩
                  cases hCompile :
                      compileExprChecked?
                        (L01_ValidSolidity.Expr.binary
                          L01_ValidSolidity.Ty.bool
                          L01_ValidSolidity.BinaryOp.eq lhs rhs) with
                  | none =>
                      simp [compileExprChecked?, hLhsCompile,
                        hRhsCompile] at hCompile
                  | some checked =>
                      exact ⟨checked, rfl⟩
      case uint bits =>
        by_cases hBits : bits = 256
        · subst bits
          cases op <;> try simp [structuralExprTarget?] at hStructural
          case pos.add =>
            cases hLhs : structuralExprTarget? lhs with
            | none =>
                simp [hLhs] at hStructural
            | some lhsTarget =>
                cases hRhs : structuralExprTarget? rhs with
                | none =>
                    simp [hLhs, hRhs] at hStructural
                | some rhsTarget =>
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hLhs with
                      ⟨lhsChecked, hLhsCompile⟩
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hRhs with
                      ⟨rhsChecked, hRhsCompile⟩
                    cases hCompile :
                        compileExprChecked?
                          (L01_ValidSolidity.Expr.binary
                            (L01_ValidSolidity.Ty.uint 256)
                            L01_ValidSolidity.BinaryOp.add lhs rhs) with
                    | none =>
                        simp [compileExprChecked?, hLhsCompile,
                          hRhsCompile] at hCompile
                    | some checked =>
                        exact ⟨checked, rfl⟩
          case pos.sub =>
            cases hLhs : structuralExprTarget? lhs with
            | none =>
                simp [hLhs] at hStructural
            | some lhsTarget =>
                cases hRhs : structuralExprTarget? rhs with
                | none =>
                    simp [hLhs, hRhs] at hStructural
                | some rhsTarget =>
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hLhs with
                      ⟨lhsChecked, hLhsCompile⟩
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hRhs with
                      ⟨rhsChecked, hRhsCompile⟩
                    cases hCompile :
                        compileExprChecked?
                          (L01_ValidSolidity.Expr.binary
                            (L01_ValidSolidity.Ty.uint 256)
                            L01_ValidSolidity.BinaryOp.sub lhs rhs) with
                    | none =>
                        simp [compileExprChecked?, hLhsCompile,
                          hRhsCompile] at hCompile
                    | some checked =>
                        exact ⟨checked, rfl⟩
          case pos.mul =>
            cases hLhs : structuralExprTarget? lhs with
            | none =>
                simp [hLhs] at hStructural
            | some lhsTarget =>
                cases hRhs : structuralExprTarget? rhs with
                | none =>
                    simp [hLhs, hRhs] at hStructural
                | some rhsTarget =>
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hLhs with
                      ⟨lhsChecked, hLhsCompile⟩
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hRhs with
                      ⟨rhsChecked, hRhsCompile⟩
                    cases hCompile :
                        compileExprChecked?
                          (L01_ValidSolidity.Expr.binary
                            (L01_ValidSolidity.Ty.uint 256)
                            L01_ValidSolidity.BinaryOp.mul lhs rhs) with
                    | none =>
                        simp [compileExprChecked?, hLhsCompile,
                          hRhsCompile] at hCompile
                    | some checked =>
                        exact ⟨checked, rfl⟩
          case pos.bitAnd =>
            cases hLhs : structuralExprTarget? lhs with
            | none =>
                simp [hLhs] at hStructural
            | some lhsTarget =>
                cases hRhs : structuralExprTarget? rhs with
                | none =>
                    simp [hLhs, hRhs] at hStructural
                | some rhsTarget =>
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hLhs with
                      ⟨lhsChecked, hLhsCompile⟩
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hRhs with
                      ⟨rhsChecked, hRhsCompile⟩
                    cases hCompile :
                        compileExprChecked?
                          (L01_ValidSolidity.Expr.binary
                            (L01_ValidSolidity.Ty.uint 256)
                            L01_ValidSolidity.BinaryOp.bitAnd lhs rhs) with
                    | none =>
                        simp [compileExprChecked?, hLhsCompile,
                          hRhsCompile] at hCompile
                    | some checked =>
                        exact ⟨checked, rfl⟩
        · cases op <;> simp [structuralExprTarget?, hBits] at hStructural
  | L01_ValidSolidity.Expr.read _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.functionRef _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.eventRef _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.errorRef _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.unary _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.ternary _ _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.tuple _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.array _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.call _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.callWithValue _ _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.memberValue _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L01_ValidSolidity.Expr.assignment _ _ _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural

theorem structuralStmtTarget?_compileStmtChecked?_exists :
    ∀ {source : L01_ValidSolidity.Stmt}
      {target : L02_AbstractYul.Stmt},
      structuralStmtTarget? source = some target ->
        ∃ checked : CheckedStmt source,
          compileStmtChecked? source = some checked
  | L01_ValidSolidity.Stmt.returnValues exprs, target, hStructural => by
      cases exprs with
      | nil =>
          simp [structuralStmtTarget?] at hStructural
      | cons sourceExpr rest =>
          cases rest with
          | nil =>
              by_cases hTy :
                  sourceExpr.resultTyIsUint256 = true
              · cases hExpr : structuralExprTarget? sourceExpr with
                | none =>
                    simp [structuralStmtTarget?, hTy, hExpr]
                      at hStructural
                | some targetExpr =>
                    rcases
                      structuralExprTarget?_compileExprChecked?_exists
                        hExpr with
                      ⟨exprChecked, hExprCompile⟩
                    let checked :
                        CheckedStmt
                          (L01_ValidSolidity.Stmt.returnValues
                            [sourceExpr]) :=
                      { stmt := L02_AbstractYul.Stmt.returnExpr
                          exprChecked.expr
                        sourceExpr := sourceExpr
                        targetExpr := exprChecked.expr
                        sourceReturned := by rfl
                        targetReturned := by rfl
                        eval_eq := exprChecked.eval_eq }
                    exact
                      ⟨checked, by
                        simp [compileStmtChecked?, hTy, hExprCompile,
                          checked]⟩
              · simp [structuralStmtTarget?, hTy] at hStructural
          | cons _ _ =>
              simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.block decls stmts, target,
      hStructural => by
      cases decls with
      | nil =>
          cases stmts with
          | nil =>
              simp [structuralStmtTarget?] at hStructural
          | cons sourceStmt rest =>
              cases rest with
              | nil =>
                  cases hStmt : structuralStmtTarget? sourceStmt with
                  | none =>
                      simp [structuralStmtTarget?, hStmt] at hStructural
                  | some targetStmt =>
                      rcases
                        structuralStmtTarget?_compileStmtChecked?_exists
                          hStmt with
                        ⟨stmtChecked, hStmtCompile⟩
                      let checked :
                          CheckedStmt
                            (L01_ValidSolidity.Stmt.block []
                              [sourceStmt]) :=
                        { stmt := L02_AbstractYul.Stmt.block
                            [stmtChecked.stmt]
                          sourceExpr := stmtChecked.sourceExpr
                          targetExpr := stmtChecked.targetExpr
                          sourceReturned := by
                            simp [L01_ValidSolidity.Stmt.returnedExpr?,
                              stmtChecked.sourceReturned]
                          targetReturned := by
                            simp [L02_AbstractYul.Stmt.returnedExpr?,
                              stmtChecked.targetReturned]
                          eval_eq := stmtChecked.eval_eq }
                      exact
                        ⟨checked, by
                          simp [compileStmtChecked?, hStmtCompile,
                            checked]⟩
              | cons _ _ =>
                  simp [structuralStmtTarget?] at hStructural
      | cons _ _ =>
          simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.ifElse condition thenBranch elseBranch,
      target, hStructural => by
      by_cases hTy : condition.resultTyIsBool = true
      · cases hConditionTarget :
            structuralExprTarget? condition with
        | none =>
            simp [structuralStmtTarget?, hTy, hConditionTarget]
              at hStructural
        | some targetCondition =>
            cases hThenTarget :
                structuralStmtTarget? thenBranch with
            | none =>
                simp [structuralStmtTarget?, hTy, hConditionTarget,
                  hThenTarget] at hStructural
            | some targetThen =>
                cases hElseTarget :
                    structuralStmtTarget? elseBranch with
                | none =>
                    simp [structuralStmtTarget?, hTy, hConditionTarget,
                      hThenTarget, hElseTarget] at hStructural
                | some targetElse =>
                    cases hConditionEval : condition.eval? with
                    | none =>
                        simp [structuralStmtTarget?, hTy,
                          hConditionTarget, hThenTarget, hElseTarget,
                          hConditionEval] at hStructural
                    | some conditionValue =>
                        rcases
                          structuralExprTarget?_compileExprChecked?_exists
                            hConditionTarget with
                          ⟨conditionChecked, hConditionCompile⟩
                        rcases
                          structuralStmtTarget?_compileStmtChecked?_exists
                            hThenTarget with
                          ⟨thenChecked, hThenCompile⟩
                        rcases
                          structuralStmtTarget?_compileStmtChecked?_exists
                            hElseTarget with
                          ⟨elseChecked, hElseCompile⟩
                        have hCompileSome :
                            (compileStmtChecked?
                              (L01_ValidSolidity.Stmt.ifElse condition
                                thenBranch elseBranch)).isSome = true := by
                          simp [compileStmtChecked?, hTy,
                            hConditionCompile, hThenCompile,
                            hElseCompile, hConditionEval]
                        cases hCompile :
                            compileStmtChecked?
                              (L01_ValidSolidity.Stmt.ifElse condition
                                thenBranch elseBranch) with
                        | none =>
                            simp [hCompile] at hCompileSome
                        | some checked =>
                            exact ⟨checked, rfl⟩
      · simp [structuralStmtTarget?, hTy] at hStructural
  | L01_ValidSolidity.Stmt.skip, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.expr _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.assign _ _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.whileLoop _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.doWhile _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.forLoop _ _ _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.tryCatch _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.emitEvent _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.revert _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.«break», _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.«continue», _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.unchecked _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L01_ValidSolidity.Stmt.modifierPlaceholder, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural

theorem structuralFunctionTarget?_compileFunctionChecked?_exists
    {source : L01_ValidSolidity.FunctionDecl}
    {target : L02_AbstractYul.Entry}
    (hStructural : structuralFunctionTarget? source = some target) :
    ∃ checked : CheckedFunction source,
      compileFunctionChecked? source = some checked := by
  cases source with
  | mk id sourceName contract params returns visibility mutability
      modifiers body virtual overrides =>
      cases params with
      | cons _ _ =>
          simp [structuralFunctionTarget?] at hStructural
      | nil =>
          cases returns with
          | nil =>
              simp [structuralFunctionTarget?] at hStructural
          | cons ret returnRest =>
              cases returnRest with
              | cons _ _ =>
                  simp [structuralFunctionTarget?] at hStructural
              | nil =>
                  cases visibility <;>
                    try simp [structuralFunctionTarget?] at hStructural
                  case public_ =>
                    cases mutability <;>
                      try simp [structuralFunctionTarget?] at hStructural
                    case pure =>
                      cases modifiers with
                      | cons _ _ =>
                          simp [structuralFunctionTarget?] at hStructural
                      | nil =>
                          cases body with
                          | none =>
                              simp [structuralFunctionTarget?]
                                at hStructural
                          | some bodyStmt =>
                              cases hRet : ret.isUint256 with
                              | false =>
                                  simp [structuralFunctionTarget?, hRet]
                                    at hStructural
                              | true =>
                                  cases hStmt :
                                      structuralStmtTarget? bodyStmt with
                                  | none =>
                                      simp [structuralFunctionTarget?,
                                        hRet, hStmt] at hStructural
                                  | some targetStmt =>
                                      rcases
                                        structuralStmtTarget?_compileStmtChecked?_exists
                                          hStmt with
                                        ⟨stmtChecked, hStmtCompile⟩
                                      let checked :
                                          CheckedFunction
                                            ({ id := id
                                               sourceName := sourceName
                                               contract := contract
                                               params := []
                                               returns := [ret]
                                               visibility :=
                                                L01_ValidSolidity.Visibility.public_
                                               mutability :=
                                                L01_ValidSolidity.StateMutability.pure
                                               modifiers := []
                                               body := some bodyStmt
                                               virtual := virtual
                                               overrides := overrides } :
                                              L01_ValidSolidity.FunctionDecl) :=
                                        { entry :=
                                            L02_AbstractYul.Entry.withSourceBody
                                              id stmtChecked.stmt
                                          sourceExpr := stmtChecked.sourceExpr
                                          targetExpr := stmtChecked.targetExpr
                                          sourceReturned := by
                                            simp [L01_ValidSolidity.FunctionDecl.returnedExpr?,
                                              hRet, stmtChecked.sourceReturned]
                                          targetReturned := by
                                            simp [L02_AbstractYul.Entry.withSourceBody,
                                              L02_AbstractYul.Entry.returnedExpr?,
                                              stmtChecked.targetReturned]
                                          eval_eq := stmtChecked.eval_eq }
                                      exact
                                        ⟨checked, by
                                          simp [compileFunctionChecked?,
                                            hRet, hStmtCompile,
                                            checked]⟩

theorem structuralContractTarget?_compileContractChecked?_exists
    {source : L01_ValidSolidity.ContractDecl}
    {target : L02_AbstractYul.Entry}
    (hStructural : structuralContractTarget? source = some target) :
    ∃ checked : CheckedContract source,
      compileContractChecked? source = some checked := by
  cases source with
  | mk id sourceName bases linearizedBases storage functions
      modifiers events errors structs enums =>
      cases bases with
      | cons _ _ =>
          simp [structuralContractTarget?] at hStructural
      | nil =>
          cases linearizedBases with
          | cons _ _ =>
              simp [structuralContractTarget?] at hStructural
          | nil =>
              cases storage with
              | cons _ _ =>
                  simp [structuralContractTarget?] at hStructural
              | nil =>
                  cases functions with
                  | nil =>
                      simp [structuralContractTarget?] at hStructural
                  | cons fn functionRest =>
                      cases functionRest with
                      | cons _ _ =>
                          simp [structuralContractTarget?] at hStructural
                      | nil =>
                          cases modifiers with
                          | cons _ _ =>
                              simp [structuralContractTarget?]
                                at hStructural
                          | nil =>
                              cases events with
                              | cons _ _ =>
                                  simp [structuralContractTarget?]
                                    at hStructural
                              | nil =>
                                  cases errors with
                                  | cons _ _ =>
                                      simp [structuralContractTarget?]
                                        at hStructural
                                  | nil =>
                                      cases structs with
                                      | cons _ _ =>
                                          simp [structuralContractTarget?]
                                            at hStructural
                                      | nil =>
                                          cases enums with
                                          | cons _ _ =>
                                              simp [structuralContractTarget?]
                                                at hStructural
                                          | nil =>
                                              rcases
                                                structuralFunctionTarget?_compileFunctionChecked?_exists
                                                  hStructural with
                                                ⟨fnChecked, hFnCompile⟩
                                              let checked :
                                                  CheckedContract
                                                    ({ id := id
                                                       sourceName := sourceName
                                                       bases := []
                                                       linearizedBases := []
                                                       storage := []
                                                       functions := [fn]
                                                       modifiers := []
                                                       events := []
                                                       errors := []
                                                       structs := []
                                                       enums := [] } :
                                                      L01_ValidSolidity.ContractDecl) :=
                                                { entry := fnChecked.entry
                                                  sourceExpr := fnChecked.sourceExpr
                                                  targetExpr := fnChecked.targetExpr
                                                  sourceReturned := by
                                                    simp [L01_ValidSolidity.ContractDecl.returnedExpr?,
                                                      fnChecked.sourceReturned]
                                                  targetReturned :=
                                                    fnChecked.targetReturned
                                                  eval_eq := fnChecked.eval_eq }
                                              exact
                                                ⟨checked, by
                                                  simp [compileContractChecked?,
                                                    hFnCompile,
                                                    checked]⟩

theorem structuralProgramTarget?_compileProgramChecked?_exists
    {source : L01_ValidSolidity.Program}
    {target : L02_AbstractYul.Program}
    (hStructural : structuralProgramTarget? source = some target) :
    ∃ checked : CheckedProgram source,
      compileProgramChecked? source = some checked := by
  cases source with
  | mk contracts entryContract =>
      cases contracts with
      | nil =>
          simp [structuralProgramTarget?] at hStructural
      | cons contract contractRest =>
          cases contractRest with
          | cons _ _ =>
              simp [structuralProgramTarget?] at hStructural
          | nil =>
              cases entryContract with
              | none =>
                  simp [structuralProgramTarget?] at hStructural
              | some entry =>
                  cases hEntry : entry.value == contract.id.value with
                  | false =>
                      simp [structuralProgramTarget?, hEntry]
                        at hStructural
                  | true =>
                      cases hContract :
                          structuralContractTarget? contract with
                      | none =>
                          simp [structuralProgramTarget?, hEntry,
                            hContract] at hStructural
                      | some targetEntry =>
                          rcases
                            structuralContractTarget?_compileContractChecked?_exists
                              hContract with
                            ⟨contractChecked, hContractCompile⟩
                          let checked :
                              CheckedProgram
                                ({ contracts := [contract]
                                   entryContract := some entry } :
                                  L01_ValidSolidity.Program) :=
                            { program :=
                                L02_AbstractYul.Program.withEntry
                                  contractChecked.entry
                              wf := by exact {}
                              sourceExpr := contractChecked.sourceExpr
                              targetExpr := contractChecked.targetExpr
                              sourceReturned := by
                                simp [L01_ValidSolidity.Program.returnedExpr?,
                                  hEntry, contractChecked.sourceReturned]
                              targetReturned := by
                                simp [L02_AbstractYul.Program.withEntry,
                                  L02_AbstractYul.Program.returnedExpr?,
                                  contractChecked.targetReturned]
                              eval_eq := contractChecked.eval_eq }
                          exact
                            ⟨checked, by
                              simp [compileProgramChecked?, hEntry,
                                hContractCompile, checked]⟩

noncomputable def compile? (program : L01_ValidSolidity.Program) :
    Option Artifact := by
  classical
  exact
    if program = L01_ValidSolidity.Program.empty then
      some
        { program := L02_AbstractYul.Program.empty
          wf := L02_AbstractYul.Program.empty_wf }
    else
      match compileProgramChecked? program with
      | some checked =>
          some
            { program := checked.program
              wf := checked.wf }
      | none => none

theorem compile?_accepted
    {program : L01_ValidSolidity.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    Accepted program := by
  classical
  by_cases hEmpty : program = L01_ValidSolidity.Program.empty
  · subst program
    simp [Accepted, accepted?, programEmptyShape?,
      L01_ValidSolidity.Program.empty]
  · cases hChecked : compileProgramChecked? program with
    | none =>
        simp [compile?, hEmpty, hChecked] at hCompile
    | some checked =>
        simp [compile?, hEmpty, hChecked] at hCompile
        cases hCompile
        have hStructural :
            structuralProgramTarget? program = some checked.program :=
          compileProgramChecked?_structuralProgramTarget? hChecked
        have hShapeFalse : programEmptyShape? program = false := by
          cases hShape : programEmptyShape? program
          · rfl
          · have hProgramEmpty :
                program = L01_ValidSolidity.Program.empty := by
              cases program with
              | mk contracts entryContract =>
                  cases contracts <;> cases entryContract <;>
                    simp [programEmptyShape?,
                      L01_ValidSolidity.Program.empty] at hShape ⊢
            exact False.elim (hEmpty hProgramEmpty)
        simp [Accepted, accepted?, hShapeFalse, hStructural]

structure SoundnessBoundary
    (_program : L01_ValidSolidity.Program) (_artifact : Artifact) :
    Prop where
  preservesBehavior :
    ∀ {behavior : L01_ValidSolidity.Behavior},
    L01_ValidSolidity.Semantics _program
        behavior ->
      L02_AbstractYul.Semantics _artifact.program behavior

theorem compile?_sound
    {program : L01_ValidSolidity.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  classical
  by_cases hEmpty : program = L01_ValidSolidity.Program.empty
  · simp [compile?, hEmpty] at hCompile
    cases hCompile
    subst program
    exact
      { preservesBehavior := by
          intro behavior hSource
          cases hSource with
          | empty _ =>
              exact L02_AbstractYul.Program.empty_semantics
          | returnValue hReturn =>
              rcases hReturn with ⟨expr, hExpr, _hEval⟩
              simp [L01_ValidSolidity.Program.empty,
                L01_ValidSolidity.Program.returnedExpr?] at hExpr }
  · cases hChecked : compileProgramChecked? program with
    | none =>
        simp [compile?, hEmpty, hChecked] at hCompile
    | some checked =>
        simp [compile?, hEmpty, hChecked] at hCompile
        cases hCompile
        exact
          { preservesBehavior := by
              intro behavior hSource
              cases hSource with
              | empty hProgram =>
                  have hNone : program.returnedExpr? = none := by
                    rcases hProgram with ⟨hContracts, hEntry⟩
                    cases program with
                    | mk contracts entryContract =>
                        simp at hContracts hEntry
                        subst contracts
                        subst entryContract
                        rfl
                  have hReturned := checked.sourceReturned
                  rw [hNone] at hReturned
                  contradiction
              | returnValue hReturn =>
                  rcases hReturn with
                    ⟨sourceExpr, hSourceReturned, hSourceEval⟩
                  have hExprEq :
                      sourceExpr = checked.sourceExpr := by
                    have hSome :
                        some sourceExpr = some checked.sourceExpr := by
                      rw [← hSourceReturned, checked.sourceReturned]
                    cases hSome
                    rfl
                  subst sourceExpr
                  exact
                    L02_AbstractYul.Semantics.returnValue
                      ⟨checked.targetExpr, checked.targetReturned,
                        by
                          unfold L02_AbstractYul.Expr.Eval
                          unfold L01_ValidSolidity.Expr.Eval at hSourceEval
                          rw [checked.eval_eq, hSourceEval]⟩ }

theorem compile?_complete_for_empty
    {program : L01_ValidSolidity.Program}
    (hEmpty : program.IsEmpty) :
    ∃ artifact, compile? program = some artifact := by
  classical
  rcases hEmpty with ⟨hContracts, hEntry⟩
  cases program with
  | mk contracts entryContract =>
      simp at hContracts hEntry
      subst contracts
      subst entryContract
      exact
        ⟨{ program := L02_AbstractYul.Program.empty
           wf := L02_AbstractYul.Program.empty_wf },
          by
          simp [compile?, L01_ValidSolidity.Program.empty]⟩

theorem compile?_complete_for_accepted
    {program : L01_ValidSolidity.Program}
    (hAccepted : Accepted program) :
    ∃ artifact, compile? program = some artifact := by
  classical
  by_cases hProgramEmpty : program = L01_ValidSolidity.Program.empty
  · subst program
    exact
      ⟨{ program := L02_AbstractYul.Program.empty
         wf := L02_AbstractYul.Program.empty_wf },
        by simp [compile?, L01_ValidSolidity.Program.empty]⟩
  · have hShapeFalse : programEmptyShape? program = false := by
      cases hShape : programEmptyShape? program
      · rfl
      · have hEmpty : program = L01_ValidSolidity.Program.empty := by
          cases program with
          | mk contracts entryContract =>
              cases contracts <;> cases entryContract <;>
                simp [programEmptyShape?,
                  L01_ValidSolidity.Program.empty] at hShape ⊢
        exact False.elim (hProgramEmpty hEmpty)
    unfold Accepted accepted? at hAccepted
    simp [hShapeFalse] at hAccepted
    cases hTarget : structuralProgramTarget? program with
    | none =>
        simp [hTarget] at hAccepted
    | some target =>
        rcases
          structuralProgramTarget?_compileProgramChecked?_exists
            hTarget with
          ⟨checked, hChecked⟩
        exact
          ⟨{ program := checked.program
             wf := checked.wf },
            by simp [compile?, hProgramEmpty, hChecked]⟩

end P02_ValidSolidityToAbstractYul
end Passes
end Spine
end SolidCore

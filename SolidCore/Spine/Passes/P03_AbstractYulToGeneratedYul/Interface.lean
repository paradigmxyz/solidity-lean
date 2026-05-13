import SolidCore.Spine.L02_AbstractYul.Interface
import SolidCore.Spine.L03_GeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace Passes
namespace P03_AbstractYulToGeneratedYul

structure Artifact where
  program : L03_GeneratedYul.Program
  wf : L03_GeneratedYul.WF program

structure CheckedExpr (source : L02_AbstractYul.Expr) where
  expr : L03_GeneratedYul.Expr
  eval_eq : expr.eval? = source.eval?

def compileExprChecked? :
    (source : L02_AbstractYul.Expr) -> Option (CheckedExpr source)
  | L02_AbstractYul.Expr.word value =>
        some
          { expr := L03_GeneratedYul.Expr.word value
            eval_eq := by
              simp [L03_GeneratedYul.Expr.eval?,
                L03_GeneratedYul.Expr.evalWith?,
                L02_AbstractYul.Expr.eval?,
                L02_AbstractYul.Expr.toCore?,
                L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                L00_SourceSolidity.Executable.CoreExpr.evalWord?,
                L00_SourceSolidity.Executable.CoreValue.asWord?,
              SolidCore.Solidity.Source.Expr.eval,
              SolidCore.Solidity.Source.Value.asWord?,
              SolidCore.Solidity.Source.normWord,
              SharedSemantics.norm_norm] }
  | L02_AbstractYul.Expr.bool value =>
      some
        { expr :=
            L03_GeneratedYul.Expr.word
              (SolidCore.Solidity.Source.boolWord value)
          eval_eq := by
            cases value <;> rfl }
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.addChecked lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.addChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.add
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.subChecked lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.subChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.sub
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.mulChecked lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.mulChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.mul
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
        else
          none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.bitAnd lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.bitAnd lhs rhs
          let target :=
            L03_GeneratedYul.Expr.bitAnd
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.lt lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.lt lhs rhs
          let target :=
            L03_GeneratedYul.Expr.ltOp
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.gt lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.gt lhs rhs
          let target :=
            L03_GeneratedYul.Expr.gtOp
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.eq lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.eq lhs rhs
          let target :=
            L03_GeneratedYul.Expr.eqOp
              lhsChecked.expr rhsChecked.expr
          if hEval : target.eval? = source.eval? then
            some
              { expr := target
                eval_eq := hEval }
          else
            none
      | _, _ => none
  | _ => none

def compileExpr? (source : L02_AbstractYul.Expr) :
    Option L03_GeneratedYul.Expr :=
  match compileExprChecked? source with
  | some checked => some checked.expr
  | none => none

structure CheckedStmt (source : L02_AbstractYul.Stmt) where
  stmt : L03_GeneratedYul.Stmt
  sourceExpr : L02_AbstractYul.Expr
  targetExpr : L03_GeneratedYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : stmt.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def checkedIfElse
    (condition : L02_AbstractYul.Expr)
    (thenBranch elseBranch : L02_AbstractYul.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (conditionValue : L02_AbstractYul.Word)
    (hConditionEval : condition.eval? = some conditionValue) :
    CheckedStmt
      (L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch) :=
  if hCondition :
      SolidCore.Solidity.Source.wordTruthy conditionValue then
    { stmt :=
        L03_GeneratedYul.Stmt.switch
          conditionChecked.expr
          [(0, elseChecked.stmt)]
          (some thenChecked.stmt)
      sourceExpr := thenChecked.sourceExpr
      targetExpr := thenChecked.targetExpr
      sourceReturned := by
        simp [L02_AbstractYul.Stmt.returnedExpr?,
          hConditionEval, hCondition,
          thenChecked.sourceReturned]
      targetReturned := by
        have hTargetEval :
            conditionChecked.expr.eval? =
              some conditionValue := by
          rw [conditionChecked.eval_eq, hConditionEval]
        have hZeroFalse :
            (SharedSemantics.norm conditionValue == 0) =
              false := by
          cases hZero :
              (SharedSemantics.norm conditionValue == 0) <;>
            simp [SolidCore.Solidity.Source.wordTruthy,
              hZero] at hCondition ⊢
        simp [L03_GeneratedYul.Stmt.returnedExpr?,
          hTargetEval, hZeroFalse,
          thenChecked.targetReturned]
      eval_eq := thenChecked.eval_eq }
  else
    { stmt :=
        L03_GeneratedYul.Stmt.switch
          conditionChecked.expr
          [(0, elseChecked.stmt)]
          (some thenChecked.stmt)
      sourceExpr := elseChecked.sourceExpr
      targetExpr := elseChecked.targetExpr
      sourceReturned := by
        simp [L02_AbstractYul.Stmt.returnedExpr?,
          hConditionEval, hCondition,
          elseChecked.sourceReturned]
      targetReturned := by
        have hTargetEval :
            conditionChecked.expr.eval? =
              some conditionValue := by
          rw [conditionChecked.eval_eq, hConditionEval]
        have hZeroTrue :
            (SharedSemantics.norm conditionValue == 0) =
              true := by
          cases hZero :
              (SharedSemantics.norm conditionValue == 0) <;>
            simp [SolidCore.Solidity.Source.wordTruthy,
              hZero] at hCondition ⊢
        simp [L03_GeneratedYul.Stmt.returnedExpr?,
          hTargetEval, hZeroTrue,
          elseChecked.targetReturned]
      eval_eq := elseChecked.eval_eq }

def checkedIfElseOfEvalSome
    (condition : L02_AbstractYul.Expr)
    (thenBranch elseBranch : L02_AbstractYul.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (hConditionEvalSome : condition.eval?.isSome = true) :
    CheckedStmt
      (L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch) :=
  match hConditionEval : condition.eval? with
  | some conditionValue =>
      checkedIfElse condition thenBranch elseBranch
        conditionChecked thenChecked elseChecked
        conditionValue hConditionEval
  | none => by
      simp [hConditionEval] at hConditionEvalSome

theorem checkedIfElseOfEvalSome_stmt
    (condition : L02_AbstractYul.Expr)
    (thenBranch elseBranch : L02_AbstractYul.Stmt)
    (conditionChecked : CheckedExpr condition)
    (thenChecked : CheckedStmt thenBranch)
    (elseChecked : CheckedStmt elseBranch)
    (hConditionEvalSome : condition.eval?.isSome = true) :
    (checkedIfElseOfEvalSome condition thenBranch elseBranch
      conditionChecked thenChecked elseChecked
      hConditionEvalSome).stmt =
      L03_GeneratedYul.Stmt.switch
        conditionChecked.expr
        [(0, elseChecked.stmt)]
        (some thenChecked.stmt) := by
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
    (source : L02_AbstractYul.Stmt) -> Option (CheckedStmt source)
  | L02_AbstractYul.Stmt.complete
      (L02_AbstractYul.Completion.returnValues [sourceExpr]) =>
      if sourceExpr.resultTyIsWord then
        match compileExprChecked? sourceExpr with
        | some checked =>
            some
              { stmt := L03_GeneratedYul.Stmt.returnExpr checked.expr
                sourceExpr := sourceExpr
                targetExpr := checked.expr
                sourceReturned := by rfl
                targetReturned := by rfl
                eval_eq := checked.eval_eq }
        | none => none
      else
        none
  | L02_AbstractYul.Stmt.block [sourceStmt] =>
      match compileStmtChecked? sourceStmt with
      | some checked =>
          some
            { stmt := L03_GeneratedYul.Stmt.block [checked.stmt]
              sourceExpr := checked.sourceExpr
              targetExpr := checked.targetExpr
              sourceReturned := by
                simp [L02_AbstractYul.Stmt.returnedExpr?,
                  checked.sourceReturned]
              targetReturned := by
                simp [L03_GeneratedYul.Stmt.returnedExpr?,
                  L03_GeneratedYul.Stmt.returnedExprs?,
                  checked.targetReturned]
              eval_eq := checked.eval_eq }
      | none => none
  | L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch =>
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

structure CheckedEntry (source : L02_AbstractYul.Entry) where
  stmt : L03_GeneratedYul.Stmt
  sourceExpr : L02_AbstractYul.Expr
  targetExpr : L03_GeneratedYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : stmt.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def compileEntryChecked? :
    (source : L02_AbstractYul.Entry) -> Option (CheckedEntry source)
  | { params := [], body := body, .. } =>
      match compileStmtChecked? body with
      | some checked =>
          some
            { stmt := checked.stmt
              sourceExpr := checked.sourceExpr
              targetExpr := checked.targetExpr
              sourceReturned := by
                simp [L02_AbstractYul.Entry.returnedExpr?,
                  checked.sourceReturned]
              targetReturned := checked.targetReturned
              eval_eq := checked.eval_eq }
      | none => none
  | _ => none

structure CheckedProgram (source : L02_AbstractYul.Program) where
  program : L03_GeneratedYul.Program
  wf : L03_GeneratedYul.WF program
  sourceExpr : L02_AbstractYul.Expr
  targetExpr : L03_GeneratedYul.Expr
  sourceReturned : source.returnedExpr? = some sourceExpr
  targetReturned : program.returnedExpr? = some targetExpr
  eval_eq : targetExpr.eval? = sourceExpr.eval?

def compileProgramChecked? :
    (program : L02_AbstractYul.Program) ->
      Option (CheckedProgram program)
  | { entries := [entry], procs := [], init := none } =>
      match compileEntryChecked? entry with
      | some checked =>
          some
            { program := L03_GeneratedYul.Program.returnStmt checked.stmt
              wf := L03_GeneratedYul.Program.returnStmt_wf checked.stmt
              sourceExpr := checked.sourceExpr
              targetExpr := checked.targetExpr
              sourceReturned := by
                simp [L02_AbstractYul.Program.returnedExpr?,
                  checked.sourceReturned]
              targetReturned := by
                simp [L03_GeneratedYul.Program.returnStmt,
                  L03_GeneratedYul.Program.returnedExpr?,
                  L03_GeneratedYul.Object.returnStmt,
                  L03_GeneratedYul.Object.returnedExpr?,
                  L03_GeneratedYul.Profile.empty,
                  checked.targetReturned]
              eval_eq := checked.eval_eq }
      | none => none
  | _ => none

def structuralExprTarget? :
    L02_AbstractYul.Expr -> Option L03_GeneratedYul.Expr
  | L02_AbstractYul.Expr.word value =>
      some (L03_GeneratedYul.Expr.word value)
  | L02_AbstractYul.Expr.bool value =>
      some
        (L03_GeneratedYul.Expr.word
          (SolidCore.Solidity.Source.boolWord value))
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.addChecked lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.addChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.add lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.subChecked lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.subChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.sub lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.mulChecked lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.mulChecked lhs rhs
          let target :=
            L03_GeneratedYul.Expr.mul lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
        else
          none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.bitAnd lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.bitAnd lhs rhs
          let target :=
            L03_GeneratedYul.Expr.bitAnd lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.lt lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.lt lhs rhs
          let target :=
            L03_GeneratedYul.Expr.ltOp lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.gt lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.gt lhs rhs
          let target :=
            L03_GeneratedYul.Expr.gtOp lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | L02_AbstractYul.Expr.binary
      L02_AbstractYul.BinaryOp.eq lhs rhs =>
      match structuralExprTarget? lhs, structuralExprTarget? rhs with
      | some lhsTarget, some rhsTarget =>
          let source :=
            L02_AbstractYul.Expr.binary
              L02_AbstractYul.BinaryOp.eq lhs rhs
          let target :=
            L03_GeneratedYul.Expr.eqOp lhsTarget rhsTarget
          if target.eval? = source.eval? then
            some target
          else
            none
      | _, _ => none
  | _ => none

def structuralExprAccepted? (expr : L02_AbstractYul.Expr) : Bool :=
  (structuralExprTarget? expr).isSome

def structuralStmtTarget? :
    L02_AbstractYul.Stmt -> Option L03_GeneratedYul.Stmt
  | L02_AbstractYul.Stmt.complete
      (L02_AbstractYul.Completion.returnValues [sourceExpr]) =>
      if sourceExpr.resultTyIsWord then
        match structuralExprTarget? sourceExpr with
        | some targetExpr =>
            some (L03_GeneratedYul.Stmt.returnExpr targetExpr)
        | none => none
      else
        none
  | L02_AbstractYul.Stmt.block [sourceStmt] =>
      match structuralStmtTarget? sourceStmt with
      | some targetStmt =>
          some (L03_GeneratedYul.Stmt.block [targetStmt])
      | none => none
  | L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch =>
      if condition.resultTyIsBool then
        match structuralExprTarget? condition,
            structuralStmtTarget? thenBranch,
            structuralStmtTarget? elseBranch with
        | some targetCondition, some targetThen, some targetElse =>
            match condition.eval? with
            | some _ =>
                some
                  (L03_GeneratedYul.Stmt.switch targetCondition
                    [(0, targetElse)] (some targetThen))
            | none => none
        | _, _, _ => none
      else
        none
  | _ => none

def structuralStmtAccepted? (stmt : L02_AbstractYul.Stmt) : Bool :=
  (structuralStmtTarget? stmt).isSome

def structuralEntryTarget? :
    L02_AbstractYul.Entry -> Option L03_GeneratedYul.Stmt
  | { params := [], body := body, .. } =>
      structuralStmtTarget? body
  | _ => none

def structuralEntryAccepted? (entry : L02_AbstractYul.Entry) : Bool :=
  (structuralEntryTarget? entry).isSome

def structuralProgramTarget? :
    L02_AbstractYul.Program -> Option L03_GeneratedYul.Program
  | { entries := [entry], procs := [], init := none } =>
      match structuralEntryTarget? entry with
      | some targetStmt =>
          some (L03_GeneratedYul.Program.returnStmt targetStmt)
      | none => none
  | _ => none

def programEmptyShape? (program : L02_AbstractYul.Program) : Bool :=
  match program.entries, program.procs, program.init with
  | [], [], none => true
  | _, _, _ => false

def accepted? (program : L02_AbstractYul.Program) : Bool :=
  if programEmptyShape? program then
    true
  else
    (structuralProgramTarget? program).isSome

def Accepted (program : L02_AbstractYul.Program) : Prop :=
  accepted? program = true

theorem accepted?_eq_true_iff (program : L02_AbstractYul.Program) :
    accepted? program = true ↔ Accepted program := by
  rfl

theorem compileExprChecked?_structuralExprTarget? :
    ∀ {source : L02_AbstractYul.Expr}
      {checked : CheckedExpr source},
      compileExprChecked? source = some checked ->
        structuralExprTarget? source = some checked.expr
  | L02_AbstractYul.Expr.word value, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
      cases hCompile
      simp [structuralExprTarget?]
  | L02_AbstractYul.Expr.binary op lhs rhs, checked, hCompile => by
      cases op
      case addChecked =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.addChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.add
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case subChecked =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.subChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.sub
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case mulChecked =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.mulChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.mul
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case bitAnd =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.bitAnd lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.bitAnd
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case lt =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.lt lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.ltOp
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case gt =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.gt lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.gtOp
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      case eq =>
        cases hLhs : compileExprChecked? lhs with
        | none =>
            simp [compileExprChecked?, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs : compileExprChecked? rhs with
            | none =>
                simp [compileExprChecked?, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                let sourceExpr :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.eq lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.eqOp
                    lhsChecked.expr rhsChecked.expr
                by_cases hEval : targetExpr.eval? = sourceExpr.eval?
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
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
                    hRhsStructural, sourceExpr, targetExpr, hEval]
                · simp [compileExprChecked?, hLhs, hRhs, sourceExpr,
                    targetExpr, hEval] at hCompile
      all_goals simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.bool _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
      cases hCompile
      simp [structuralExprTarget?]
  | L02_AbstractYul.Expr.local _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.tuple _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.select _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.unary _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.env _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.storageRead _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.calldataRead _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.memoryRead _ _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L02_AbstractYul.Expr.keccak _, checked, hCompile => by
      simp [compileExprChecked?] at hCompile

theorem compileStmtChecked?_structuralStmtTarget? :
    ∀ {source : L02_AbstractYul.Stmt}
      {checked : CheckedStmt source},
      compileStmtChecked? source = some checked ->
        structuralStmtTarget? source = some checked.stmt
  | L02_AbstractYul.Stmt.complete completion, checked, hCompile => by
      cases completion
      · rename_i exprs
        cases exprs with
        | nil =>
            simp [compileStmtChecked?] at hCompile
        | cons sourceExpr rest =>
            cases rest with
            | nil =>
                by_cases hTy : sourceExpr.resultTyIsWord = true
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
      all_goals simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.block stmts, checked, hCompile => by
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
  | L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch, checked,
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
                            L03_GeneratedYul.Stmt.switch
                              conditionChecked.expr
                              [(0, elseChecked.stmt)]
                              (some thenChecked.stmt) := by
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
  | L02_AbstractYul.Stmt.skip, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.let1 _ _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.letMany _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.assign _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.assignMany _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.effect _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.switch _ _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | L02_AbstractYul.Stmt.loop _ _ _ _, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile

theorem compileEntryChecked?_structuralEntryTarget?
    {source : L02_AbstractYul.Entry}
    {checked : CheckedEntry source}
    (hCompile : compileEntryChecked? source = some checked) :
    structuralEntryTarget? source = some checked.stmt := by
  cases source with
  | mk id sourceFunction params body payable =>
      cases params with
      | nil =>
          cases hBody : compileStmtChecked? body with
          | none =>
              simp [compileEntryChecked?, hBody] at hCompile
          | some bodyChecked =>
              simp [compileEntryChecked?, hBody] at hCompile
              cases hCompile
              have hBodyStructural :
                  structuralStmtTarget? body =
                    some bodyChecked.stmt :=
                compileStmtChecked?_structuralStmtTarget? hBody
              simp [structuralEntryTarget?, hBodyStructural]
      | cons _ _ =>
          simp [compileEntryChecked?] at hCompile

theorem compileProgramChecked?_structuralProgramTarget?
    {source : L02_AbstractYul.Program}
    {checked : CheckedProgram source}
    (hCompile : compileProgramChecked? source = some checked) :
    structuralProgramTarget? source = some checked.program := by
  cases source with
  | mk entries procs init =>
      cases entries with
      | nil =>
          simp [compileProgramChecked?] at hCompile
      | cons entry entriesTail =>
          cases entriesTail with
          | nil =>
              cases procs with
              | nil =>
                  cases init with
                  | none =>
                      cases hEntry : compileEntryChecked? entry with
                      | none =>
                          simp [compileProgramChecked?, hEntry] at hCompile
                      | some entryChecked =>
                          simp [compileProgramChecked?, hEntry] at hCompile
                          cases hCompile
                          have hEntryStructural :
                              structuralEntryTarget? entry =
                                some entryChecked.stmt :=
                            compileEntryChecked?_structuralEntryTarget?
                              hEntry
                          simp [structuralProgramTarget?,
                            hEntryStructural]
                  | some _ =>
                      simp [compileProgramChecked?] at hCompile
              | cons _ _ =>
                  simp [compileProgramChecked?] at hCompile
          | cons _ _ =>
              simp [compileProgramChecked?] at hCompile

theorem structuralExprTarget?_compileExprChecked?_exists :
    ∀ {source : L02_AbstractYul.Expr}
      {target : L03_GeneratedYul.Expr},
      structuralExprTarget? source = some target ->
        ∃ checked : CheckedExpr source,
          compileExprChecked? source = some checked ∧
            checked.expr = target
  | L02_AbstractYul.Expr.word value, target, hStructural => by
      simp [structuralExprTarget?] at hStructural
      exact
        ⟨{ expr := L03_GeneratedYul.Expr.word value
           eval_eq := by
            simp [L03_GeneratedYul.Expr.eval?,
              L03_GeneratedYul.Expr.evalWith?,
              L02_AbstractYul.Expr.eval?,
              L02_AbstractYul.Expr.toCore?,
              L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
              L00_SourceSolidity.Executable.CoreExpr.evalWord?,
              L00_SourceSolidity.Executable.CoreValue.asWord?,
              SolidCore.Solidity.Source.Expr.eval,
              SolidCore.Solidity.Source.Value.asWord?,
              SolidCore.Solidity.Source.normWord,
              SharedSemantics.norm_norm] },
        by rfl, by
          simpa [structuralExprTarget?] using hStructural⟩
  | L02_AbstractYul.Expr.binary op lhs rhs, target, hStructural => by
      cases op
      case addChecked =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.addChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.add lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.add
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.addChecked lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.addChecked lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.add
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case subChecked =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.subChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.sub lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.sub
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.subChecked lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.subChecked lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.sub
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case mulChecked =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.mulChecked lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.mul lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.mul
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.mulChecked lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.mulChecked lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.mul
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case bitAnd =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.bitAnd lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.bitAnd lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.bitAnd
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.bitAnd lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.bitAnd lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.bitAnd
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case lt =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.lt lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.ltOp lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.ltOp
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.lt lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.lt lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.ltOp
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case gt =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.gt lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.gtOp lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.gtOp
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.gt lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.gt lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.gtOp
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      case eq =>
        cases hLhs : structuralExprTarget? lhs with
        | none =>
            simp [structuralExprTarget?, hLhs] at hStructural
        | some lhsTarget =>
            cases hRhs : structuralExprTarget? rhs with
            | none =>
                simp [structuralExprTarget?, hLhs, hRhs] at hStructural
            | some rhsTarget =>
                let source :=
                  L02_AbstractYul.Expr.binary
                    L02_AbstractYul.BinaryOp.eq lhs rhs
                let targetExpr :=
                  L03_GeneratedYul.Expr.eqOp lhsTarget rhsTarget
                by_cases hEval : targetExpr.eval? = source.eval?
                · have hTargetEq : target = targetExpr := by
                    simp [structuralExprTarget?, hLhs, hRhs, source,
                      targetExpr, hEval] at hStructural
                    cases hStructural
                    rfl
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hLhs with
                    ⟨lhsChecked, hLhsCompile, hLhsExpr⟩
                  rcases
                    structuralExprTarget?_compileExprChecked?_exists
                      hRhs with
                    ⟨rhsChecked, hRhsCompile, hRhsExpr⟩
                  have hEvalCompile :
                      (L03_GeneratedYul.Expr.eqOp
                            lhsChecked.expr rhsChecked.expr).eval? =
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.eq lhs rhs).eval? := by
                    simpa [source, targetExpr, hLhsExpr, hRhsExpr]
                      using hEval
                  let checked :
                      CheckedExpr
                        (L02_AbstractYul.Expr.binary
                          L02_AbstractYul.BinaryOp.eq lhs rhs) :=
                    { expr :=
                        L03_GeneratedYul.Expr.eqOp
                          lhsChecked.expr rhsChecked.expr
                      eval_eq := hEvalCompile }
                  refine ⟨checked, ?_, ?_⟩
                  · simp [compileExprChecked?, hLhsCompile, hRhsCompile,
                      hEvalCompile, checked]
                  · simp [checked, hTargetEq, targetExpr, hLhsExpr,
                      hRhsExpr]
                · simp [structuralExprTarget?, hLhs, hRhs, source,
                    targetExpr, hEval] at hStructural
      all_goals simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.bool value, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
      cases hStructural
      let checked : CheckedExpr (L02_AbstractYul.Expr.bool value) :=
        { expr :=
            L03_GeneratedYul.Expr.word
              (SolidCore.Solidity.Source.boolWord value)
          eval_eq := by
            cases value <;> rfl }
      exact
        ⟨checked,
          by simp [compileExprChecked?, checked],
          rfl⟩
  | L02_AbstractYul.Expr.local _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.tuple _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.select _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.unary _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.env _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.storageRead _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.calldataRead _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.memoryRead _ _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural
  | L02_AbstractYul.Expr.keccak _, _, hStructural => by
      simp [structuralExprTarget?] at hStructural

theorem structuralStmtTarget?_compileStmtChecked?_exists :
    ∀ {source : L02_AbstractYul.Stmt}
      {target : L03_GeneratedYul.Stmt},
      structuralStmtTarget? source = some target ->
        ∃ checked : CheckedStmt source,
          compileStmtChecked? source = some checked
  | L02_AbstractYul.Stmt.complete completion, target, hStructural => by
      cases completion with
      | returnValues exprs =>
          cases exprs with
          | nil =>
              simp [structuralStmtTarget?] at hStructural
          | cons sourceExpr rest =>
              cases rest with
              | nil =>
                  by_cases hTy :
                      sourceExpr.resultTyIsWord = true
                  · cases hExpr :
                        structuralExprTarget? sourceExpr with
                    | none =>
                        simp [structuralStmtTarget?, hTy, hExpr]
                          at hStructural
                    | some targetExpr =>
                        rcases
                          structuralExprTarget?_compileExprChecked?_exists
                            hExpr with
                          ⟨exprChecked, hExprCompile, _hExprTarget⟩
                        let checked :
                            CheckedStmt
                              (L02_AbstractYul.Stmt.complete
                                (L02_AbstractYul.Completion.returnValues
                                  [sourceExpr])) :=
                          { stmt :=
                              L03_GeneratedYul.Stmt.returnExpr
                                exprChecked.expr
                            sourceExpr := sourceExpr
                            targetExpr := exprChecked.expr
                            sourceReturned := by rfl
                            targetReturned := by rfl
                            eval_eq := exprChecked.eval_eq }
                        exact
                          ⟨checked, by
                            simp [compileStmtChecked?, hTy,
                              hExprCompile, checked]⟩
                  · simp [structuralStmtTarget?, hTy] at hStructural
              | cons _ _ =>
                  simp [structuralStmtTarget?] at hStructural
      | revertError _ _ =>
          simp [structuralStmtTarget?] at hStructural
      | panic _ =>
          simp [structuralStmtTarget?] at hStructural
      | rawReturn _ _ =>
          simp [structuralStmtTarget?] at hStructural
      | rawRevert _ _ =>
          simp [structuralStmtTarget?] at hStructural
      | «break» =>
          simp [structuralStmtTarget?] at hStructural
      | «continue» =>
          simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.block stmts, target, hStructural => by
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
                        (L02_AbstractYul.Stmt.block [sourceStmt]) :=
                    { stmt :=
                        L03_GeneratedYul.Stmt.block
                          [stmtChecked.stmt]
                      sourceExpr := stmtChecked.sourceExpr
                      targetExpr := stmtChecked.targetExpr
                      sourceReturned := by
                        simp [L02_AbstractYul.Stmt.returnedExpr?,
                          stmtChecked.sourceReturned]
                      targetReturned := by
                        simp [L03_GeneratedYul.Stmt.returnedExpr?,
                          L03_GeneratedYul.Stmt.returnedExprs?,
                          stmtChecked.targetReturned]
                      eval_eq := stmtChecked.eval_eq }
                  exact
                    ⟨checked, by
                      simp [compileStmtChecked?, hStmtCompile,
                        checked]⟩
          | cons _ _ =>
              simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.ifElse condition thenBranch elseBranch,
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
                          ⟨conditionChecked, hConditionCompile,
                            _hConditionExpr⟩
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
                              (L02_AbstractYul.Stmt.ifElse condition
                                thenBranch elseBranch)).isSome = true := by
                          simp [compileStmtChecked?, hTy,
                            hConditionCompile, hThenCompile,
                            hElseCompile, hConditionEval]
                        cases hCompile :
                            compileStmtChecked?
                              (L02_AbstractYul.Stmt.ifElse condition
                                thenBranch elseBranch) with
                        | none =>
                            simp [hCompile] at hCompileSome
                        | some checked =>
                            exact ⟨checked, rfl⟩
      · simp [structuralStmtTarget?, hTy] at hStructural
  | L02_AbstractYul.Stmt.skip, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.let1 _ _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.letMany _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.assign _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.assignMany _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.effect _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.switch _ _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural
  | L02_AbstractYul.Stmt.loop _ _ _ _, _, hStructural => by
      simp [structuralStmtTarget?] at hStructural

theorem structuralEntryTarget?_compileEntryChecked?_exists
    {source : L02_AbstractYul.Entry}
    {target : L03_GeneratedYul.Stmt}
    (hStructural : structuralEntryTarget? source = some target) :
    ∃ checked : CheckedEntry source,
      compileEntryChecked? source = some checked := by
  cases source with
  | mk id sourceFunction params body payable =>
      cases params with
      | nil =>
          simp [structuralEntryTarget?] at hStructural
          rcases
            structuralStmtTarget?_compileStmtChecked?_exists
              hStructural with
            ⟨stmtChecked, hStmtCompile⟩
          let checked :
              CheckedEntry
                ({ id := id
                   sourceFunction := sourceFunction
                   params := []
                   body := body
                   payable := payable } : L02_AbstractYul.Entry) :=
            { stmt := stmtChecked.stmt
              sourceExpr := stmtChecked.sourceExpr
              targetExpr := stmtChecked.targetExpr
              sourceReturned := by
                simp [L02_AbstractYul.Entry.returnedExpr?,
                  stmtChecked.sourceReturned]
              targetReturned := stmtChecked.targetReturned
              eval_eq := stmtChecked.eval_eq }
          exact
            ⟨checked, by
              simp [compileEntryChecked?, hStmtCompile, checked]⟩
      | cons _ _ =>
          simp [structuralEntryTarget?] at hStructural

theorem structuralProgramTarget?_compileProgramChecked?_exists
    {source : L02_AbstractYul.Program}
    {target : L03_GeneratedYul.Program}
    (hStructural : structuralProgramTarget? source = some target) :
    ∃ checked : CheckedProgram source,
      compileProgramChecked? source = some checked := by
  cases source with
  | mk entries procs init =>
      cases entries with
      | nil =>
          simp [structuralProgramTarget?] at hStructural
      | cons entry entryRest =>
          cases entryRest with
          | nil =>
              cases procs with
              | nil =>
                  cases init with
                  | none =>
                      cases hEntry :
                          structuralEntryTarget? entry with
                      | none =>
                          simp [structuralProgramTarget?, hEntry]
                            at hStructural
                      | some targetStmt =>
                          rcases
                            structuralEntryTarget?_compileEntryChecked?_exists
                              hEntry with
                            ⟨entryChecked, hEntryCompile⟩
                          let checked :
                              CheckedProgram
                                ({ entries := [entry]
                                   procs := []
                                   init := none } :
                                  L02_AbstractYul.Program) :=
                            { program :=
                                L03_GeneratedYul.Program.returnStmt
                                  entryChecked.stmt
                              wf :=
                                L03_GeneratedYul.Program.returnStmt_wf
                                  entryChecked.stmt
                              sourceExpr := entryChecked.sourceExpr
                              targetExpr := entryChecked.targetExpr
                              sourceReturned := by
                                simp [L02_AbstractYul.Program.returnedExpr?,
                                  entryChecked.sourceReturned]
                              targetReturned := by
                                simp [L03_GeneratedYul.Program.returnStmt,
                                  L03_GeneratedYul.Program.returnedExpr?,
                                  L03_GeneratedYul.Object.returnStmt,
                                  L03_GeneratedYul.Object.returnedExpr?,
                                  L03_GeneratedYul.Profile.empty,
                                  entryChecked.targetReturned]
                              eval_eq := entryChecked.eval_eq }
                          exact
                            ⟨checked, by
                              simp [compileProgramChecked?,
                                hEntryCompile, checked]⟩
                  | some _ =>
                      simp [structuralProgramTarget?] at hStructural
              | cons _ _ =>
                  simp [structuralProgramTarget?] at hStructural
          | cons _ _ =>
              simp [structuralProgramTarget?] at hStructural

noncomputable def compile? (program : L02_AbstractYul.Program) :
    Option Artifact := by
  classical
  exact
    if program = L02_AbstractYul.Program.empty then
      some
        { program := L03_GeneratedYul.Program.stop
          wf := L03_GeneratedYul.Program.stop_wf }
    else
      match compileProgramChecked? program with
      | some checked =>
          some
            { program := checked.program
              wf := checked.wf }
      | none => none

theorem compile?_accepted
    {program : L02_AbstractYul.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    Accepted program := by
  classical
  by_cases hEmpty : program = L02_AbstractYul.Program.empty
  · subst program
    simp [Accepted, accepted?, programEmptyShape?,
      L02_AbstractYul.Program.empty]
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
                program = L02_AbstractYul.Program.empty := by
              cases program with
              | mk entries procs init =>
                  cases entries <;> cases procs <;> cases init <;>
                    simp [programEmptyShape?,
                      L02_AbstractYul.Program.empty] at hShape ⊢
            exact False.elim (hEmpty hProgramEmpty)
        simp [Accepted, accepted?, hShapeFalse, hStructural]

structure SoundnessBoundary
    (_program : L02_AbstractYul.Program) (_artifact : Artifact) :
    Prop where
  preservesBehavior :
    ∀ {behavior : L01_ValidSolidity.Behavior},
    L02_AbstractYul.Semantics _program
        behavior ->
      L03_GeneratedYul.Semantics _artifact.program behavior

theorem compile?_sound
    {program : L02_AbstractYul.Program} {artifact : Artifact}
    (hCompile : compile? program = some artifact) :
    SoundnessBoundary program artifact := by
  classical
  by_cases hEmpty : program = L02_AbstractYul.Program.empty
  · simp [compile?, hEmpty] at hCompile
    cases hCompile
    subst program
    exact
      { preservesBehavior := by
          intro behavior hSource
          cases hSource with
          | empty _ =>
              exact L03_GeneratedYul.Program.stop_semantics
          | returnValue hReturn =>
              rcases hReturn with ⟨expr, hExpr, _hEval⟩
              simp [L02_AbstractYul.Program.empty,
                L02_AbstractYul.Program.returnedExpr?] at hExpr }
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
                    rcases hProgram with ⟨hEntries, hProcs, hInit⟩
                    cases program with
                    | mk entries procs init =>
                        simp at hEntries hProcs hInit
                        subst entries
                        subst procs
                        subst init
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
                    L03_GeneratedYul.Semantics.returnValue
                      ⟨checked.targetExpr, checked.targetReturned,
                        by
                          unfold L03_GeneratedYul.Expr.Eval
                          unfold L02_AbstractYul.Expr.Eval at hSourceEval
                          rw [checked.eval_eq, hSourceEval]⟩ }

theorem compile?_complete_for_empty
    {program : L02_AbstractYul.Program}
    (hEmpty : program.IsEmpty) :
    ∃ artifact, compile? program = some artifact := by
  classical
  rcases hEmpty with ⟨hEntries, hProcs, hInit⟩
  cases program with
  | mk entries procs init =>
      simp at hEntries hProcs hInit
      subst entries
      subst procs
      subst init
      exact
        ⟨{ program := L03_GeneratedYul.Program.stop
           wf := L03_GeneratedYul.Program.stop_wf },
          by
          simp [compile?, L02_AbstractYul.Program.empty]⟩

theorem compile?_complete_for_accepted
    {program : L02_AbstractYul.Program}
    (hAccepted : Accepted program) :
    ∃ artifact, compile? program = some artifact := by
  classical
  by_cases hProgramEmpty : program = L02_AbstractYul.Program.empty
  · subst program
    exact
      ⟨{ program := L03_GeneratedYul.Program.stop
         wf := L03_GeneratedYul.Program.stop_wf },
        by simp [compile?, L02_AbstractYul.Program.empty]⟩
  · have hShapeFalse : programEmptyShape? program = false := by
      cases hShape : programEmptyShape? program
      · rfl
      · have hEmpty : program = L02_AbstractYul.Program.empty := by
          cases program with
          | mk entries procs init =>
              cases entries <;> cases procs <;> cases init <;>
                simp [programEmptyShape?,
                  L02_AbstractYul.Program.empty] at hShape ⊢
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

end P03_AbstractYulToGeneratedYul
end Passes
end Spine
end SolidCore

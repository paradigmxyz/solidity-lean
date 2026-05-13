import SolidCore.Spine.Passes.P01_SourceSolidityToValidSolidity.Interface
import SolidCore.Spine.Passes.P02_ValidSolidityToAbstractYul.Interface
import SolidCore.Spine.Passes.P03_AbstractYulToGeneratedYul.Interface

namespace SolidCore
namespace Spine
namespace PublicClaims

structure YulArtifacts where
  valid : Passes.P01_SourceSolidityToValidSolidity.Artifact
  abstractYul : Passes.P02_ValidSolidityToAbstractYul.Artifact
  generatedYul : Passes.P03_AbstractYulToGeneratedYul.Artifact

structure YulBoundary
    (_source : L00_SourceSolidity.SourceUnit)
    (_artifacts : YulArtifacts)
    (behavior : L01_ValidSolidity.Behavior) : Prop where
  p01Sound :
    Passes.P01_SourceSolidityToValidSolidity.SoundnessBoundary
      _source _artifacts.valid behavior
  p02Sound :
    Passes.P02_ValidSolidityToAbstractYul.SoundnessBoundary
      _artifacts.valid.program _artifacts.abstractYul
  p03Sound :
    Passes.P03_AbstractYulToGeneratedYul.SoundnessBoundary
      _artifacts.abstractYul.program _artifacts.generatedYul
  sourceSemantics :
    L00_SourceSolidity.Executable.Semantics _source behavior
  validSemantics :
    L01_ValidSolidity.Semantics _artifacts.valid.program
      behavior
  abstractYulSemantics :
    L02_AbstractYul.Semantics _artifacts.abstractYul.program
      behavior
  generatedYulSemantics :
    L03_GeneratedYul.Semantics _artifacts.generatedYul.program
      behavior

noncomputable def compileToYul? (source : L00_SourceSolidity.SourceUnit) :
    Option YulArtifacts :=
  match Passes.P01_SourceSolidityToValidSolidity.check? source with
  | none => none
  | some valid =>
      match
        Passes.P02_ValidSolidityToAbstractYul.compile? valid.program with
      | none => none
      | some abstractYul =>
          match
            Passes.P03_AbstractYulToGeneratedYul.compile?
              abstractYul.program with
          | none => none
          | some generatedYul =>
              some
                { valid := valid
                  abstractYul := abstractYul
                  generatedYul := generatedYul }

structure YulPassSuccesses
    (source : L00_SourceSolidity.SourceUnit)
    (artifacts : YulArtifacts) : Prop where
  p01 :
    Passes.P01_SourceSolidityToValidSolidity.check? source =
      some artifacts.valid
  p02 :
    Passes.P02_ValidSolidityToAbstractYul.compile?
        artifacts.valid.program =
      some artifacts.abstractYul
  p03 :
    Passes.P03_AbstractYulToGeneratedYul.compile?
        artifacts.abstractYul.program =
      some artifacts.generatedYul

structure YulAcceptedInputs
    (source : L00_SourceSolidity.SourceUnit) : Prop where
  sourceAccepted :
    Passes.P01_SourceSolidityToValidSolidity.Accepted source
  validAccepted :
    ∀ {valid : Passes.P01_SourceSolidityToValidSolidity.Artifact},
      Passes.P01_SourceSolidityToValidSolidity.check? source =
        some valid ->
      Passes.P02_ValidSolidityToAbstractYul.Accepted valid.program
  abstractYulAccepted :
    ∀ {valid : Passes.P01_SourceSolidityToValidSolidity.Artifact}
      {abstractYul : Passes.P02_ValidSolidityToAbstractYul.Artifact},
      Passes.P01_SourceSolidityToValidSolidity.check? source =
        some valid ->
      Passes.P02_ValidSolidityToAbstractYul.compile? valid.program =
        some abstractYul ->
      Passes.P03_AbstractYulToGeneratedYul.Accepted abstractYul.program

namespace P01ToP02

open Passes

theorem compileExprChecked?_p02StructuralExprTarget?_exists :
    ∀ {source : L00_SourceSolidity.Expr}
      {checked :
        P01_SourceSolidityToValidSolidity.CheckedExpr source},
      P01_SourceSolidityToValidSolidity.compileExprChecked? source =
        some checked ->
        ∃ target,
          P02_ValidSolidityToAbstractYul.structuralExprTarget?
              checked.expr =
            some target
  | L00_SourceSolidity.Expr.literal lit, checked, hCompile => by
      cases lit with
      | number raw =>
          by_cases hRaw :
              P01_SourceSolidityToValidSolidity.decimalLiteralAccepted? raw
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hCompile
            cases hCompile
            exact
              ⟨L02_AbstractYul.Expr.word
                  (L00_SourceSolidity.Executable.parseDecimalNat raw),
                by
                  simp [
                    P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                    L01_ValidSolidity.Expr.word,
                    L01_ValidSolidity.Ty.uint256]⟩
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hCompile
        | bool _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hCompile
        | unitNumber _ _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hCompile
        | string _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hCompile
      | hexString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hCompile
      | unicodeString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hCompile
      | address _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hCompile
      | bytes _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hCompile
  | L00_SourceSolidity.Expr.binary op lhs rhs, checked, hCompile => by
      cases op <;> try
        simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
          at hCompile
      case add =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hCompile
            | some rhsChecked =>
                cases hAdd :
                    P01_SourceSolidityToValidSolidity.checkedAddChecked?
                      lhsChecked.value rhsChecked.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hAdd] at hCompile
                | some addChecked =>
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.add lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hAdd] at hCompile
                    split at hCompile
                    ·
                      cases hCompile
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hLhs with
                        ⟨lhsTarget, hLhsTarget⟩
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hRhs with
                        ⟨rhsTarget, hRhsTarget⟩
                      exact
                        ⟨L02_AbstractYul.Expr.add lhsTarget rhsTarget,
                          by
                            simp [
                              P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                              L01_ValidSolidity.Expr.add,
                              L01_ValidSolidity.Ty.uint256,
                              hLhsTarget, hRhsTarget]⟩
                    ·
                      cases hCompile
      case sub =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hCompile
            | some rhsChecked =>
                cases hSub :
                    P01_SourceSolidityToValidSolidity.checkedSubChecked?
                      lhsChecked.value rhsChecked.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hSub] at hCompile
                | some subChecked =>
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.sub lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hSub] at hCompile
                    split at hCompile
                    ·
                      cases hCompile
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hLhs with
                        ⟨lhsTarget, hLhsTarget⟩
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hRhs with
                        ⟨rhsTarget, hRhsTarget⟩
                      exact
                        ⟨L02_AbstractYul.Expr.sub lhsTarget rhsTarget,
                          by
                            simp [
                              P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                              L01_ValidSolidity.Expr.sub,
                              L01_ValidSolidity.Ty.uint256,
                              hLhsTarget, hRhsTarget]⟩
                    ·
                      cases hCompile
      case mul =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hCompile
            | some rhsChecked =>
                cases hMul :
                    P01_SourceSolidityToValidSolidity.checkedMulChecked?
                      lhsChecked.value rhsChecked.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hMul] at hCompile
                | some mulChecked =>
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.mul lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hMul] at hCompile
                    split at hCompile
                    ·
                      cases hCompile
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hLhs with
                        ⟨lhsTarget, hLhsTarget⟩
                      rcases
                        compileExprChecked?_p02StructuralExprTarget?_exists
                          hRhs with
                        ⟨rhsTarget, hRhsTarget⟩
                      exact
                        ⟨L02_AbstractYul.Expr.mul lhsTarget rhsTarget,
                          by
                            simp [
                              P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                              L01_ValidSolidity.Expr.mul,
                              L01_ValidSolidity.Ty.uint256,
                              hLhsTarget, hRhsTarget]⟩
                    ·
                      cases hCompile
      case bitAnd =>
        let source :=
          L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              source, hLhs] at hCompile
        | some lhsChecked =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  source, hLhs, hRhs] at hCompile
            | some rhsChecked =>
                by_cases hNotFolded :
                    P01_SourceSolidityToValidSolidity.sourceBinaryBitAndNotFolded?
                        source = some ()
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hCompile
                  cases hCompile
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hLhs with
                    ⟨lhsTarget, hLhsTarget⟩
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hRhs with
                    ⟨rhsTarget, hRhsTarget⟩
                  exact
                    ⟨L02_AbstractYul.Expr.bitAnd lhsTarget rhsTarget,
                      by
                        simp [
                          P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                          P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                          L01_ValidSolidity.Expr.bitAnd,
                          L01_ValidSolidity.Ty.uint256,
                          hLhsTarget, hRhsTarget]⟩
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hCompile
  | L00_SourceSolidity.Expr.ident _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.typeName _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.member _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.index _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.slice _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.call _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.callWithOptions _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.newExpr _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.tuple _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.array _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.enumFromUInt _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.unary _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.ternary _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
  | L00_SourceSolidity.Expr.assign _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
        at hCompile
    | L00_SourceSolidity.Expr.payableConversion _, _, hCompile => by
        simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
          at hCompile

theorem compileBoolExprChecked?_p02StructuralExprTarget?_exists
    {source : L00_SourceSolidity.Expr}
    {checked :
      P01_SourceSolidityToValidSolidity.CheckedBoolExpr source}
    (hCompile :
      P01_SourceSolidityToValidSolidity.compileBoolExprChecked? source =
        some checked) :
    ∃ target,
      P02_ValidSolidityToAbstractYul.structuralExprTarget?
          checked.expr =
        some target := by
  cases source <;>
    simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
      at hCompile
  case literal lit =>
    cases lit <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hCompile
    case bool value =>
      cases hCompile
      exact
        ⟨L02_AbstractYul.Expr.bool value,
          by
            simp [
              P02_ValidSolidityToAbstractYul.structuralExprTarget?,
              L01_ValidSolidity.Expr.bool,
              L01_ValidSolidity.Ty.bool]⟩
  case binary op lhs rhs =>
    cases op <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hCompile
    case lt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hCompile
          | some rhsChecked =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryLtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.lt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
                  cases hCompile
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hLhs with
                    ⟨lhsTarget, hLhsTarget⟩
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hRhs with
                    ⟨rhsTarget, hRhsTarget⟩
                  exact
                    ⟨L02_AbstractYul.Expr.ltOp lhsTarget rhsTarget,
                      by
                        simp [
                          P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                          L01_ValidSolidity.Expr.ltOp,
                          hLhsTarget, hRhsTarget]⟩
    case gt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hCompile
          | some rhsChecked =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryGtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.gt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
                  cases hCompile
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hLhs with
                    ⟨lhsTarget, hLhsTarget⟩
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hRhs with
                    ⟨rhsTarget, hRhsTarget⟩
                  exact
                    ⟨L02_AbstractYul.Expr.gtOp lhsTarget rhsTarget,
                      by
                        simp [
                          P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                          L01_ValidSolidity.Expr.gtOp,
                          hLhsTarget, hRhsTarget]⟩
    case eq =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hCompile
          | some rhsChecked =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryEqNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.eq lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hCompile
                  cases hCompile
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hLhs with
                    ⟨lhsTarget, hLhsTarget⟩
                  rcases
                    compileExprChecked?_p02StructuralExprTarget?_exists
                      hRhs with
                    ⟨rhsTarget, hRhsTarget⟩
                  exact
                    ⟨L02_AbstractYul.Expr.eqOp lhsTarget rhsTarget,
                      by
                        simp [
                          P02_ValidSolidityToAbstractYul.structuralExprTarget?,
                          L01_ValidSolidity.Expr.eqOp,
                          hLhsTarget, hRhsTarget]⟩

theorem compileStmtChecked?_p02StructuralStmtTarget?_exists :
    ∀ {functions : List L00_SourceSolidity.FunctionDecl}
      {source : L00_SourceSolidity.Stmt}
      {checked :
        P01_SourceSolidityToValidSolidity.CheckedStmt functions source},
      P01_SourceSolidityToValidSolidity.compileStmtChecked?
          functions source =
        some checked ->
        ∃ target,
          P02_ValidSolidityToAbstractYul.structuralStmtTarget?
              checked.stmt =
            some target
  | functions, L00_SourceSolidity.Stmt.returnValues expr?, checked,
      hCompile => by
      cases expr? with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hCompile
      | some expr =>
          cases hExpr :
              P01_SourceSolidityToValidSolidity.compileExprChecked? expr with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hExpr] at hCompile
          | some exprChecked =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hExpr] at hCompile
              cases hCompile
              rcases
                compileExprChecked?_p02StructuralExprTarget?_exists
                  hExpr with
                ⟨targetExpr, hTargetExpr⟩
              have hResultTy :
                  exprChecked.expr.resultTyIsUint256 = true := by
                simp [L01_ValidSolidity.Expr.resultTyIsUint256,
                  exprChecked.resultTy,
                  L01_ValidSolidity.Ty.uint256,
                  L01_ValidSolidity.Ty.isUint256]
              exact
                ⟨L02_AbstractYul.Stmt.returnExpr targetExpr,
                  by
                    simp [
                      P02_ValidSolidityToAbstractYul.structuralStmtTarget?,
                      L01_ValidSolidity.Stmt.returnExpr,
                      hResultTy, hTargetExpr]⟩
  | functions, L00_SourceSolidity.Stmt.block stmts, checked, hCompile => by
      cases stmts with
      | nil =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hCompile
      | cons stmt rest =>
          cases rest with
          | nil =>
              cases hStmt :
                  P01_SourceSolidityToValidSolidity.compileStmtChecked?
                    functions stmt with
              | none =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hStmt] at hCompile
              | some stmtChecked =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hStmt] at hCompile
                  cases hCompile
                  rcases
                    compileStmtChecked?_p02StructuralStmtTarget?_exists
                      hStmt with
                    ⟨targetStmt, hTargetStmt⟩
                  exact
                    ⟨L02_AbstractYul.Stmt.block [targetStmt],
                      by
                        simp [
                          P02_ValidSolidityToAbstractYul.structuralStmtTarget?,
                          L01_ValidSolidity.Stmt.block,
                          hTargetStmt]⟩
          | cons _ _ =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
                at hCompile
  | functions,
      L00_SourceSolidity.Stmt.ifElse condition thenBranch elseBranch?,
      checked, hCompile => by
      cases elseBranch? with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hCompile
      | some elseBranch =>
          cases hCondition :
              P01_SourceSolidityToValidSolidity.compileBoolExprChecked?
                condition with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hCondition] at hCompile
          | some conditionChecked =>
              cases hThen :
                  P01_SourceSolidityToValidSolidity.compileStmtChecked?
                    functions thenBranch with
              | none =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hCondition, hThen] at hCompile
              | some thenChecked =>
                  cases hElse :
                      P01_SourceSolidityToValidSolidity.compileStmtChecked?
                        functions elseBranch with
                  | none =>
                      simp [
                        P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                        hCondition, hThen, hElse] at hCompile
                  | some elseChecked =>
                      rcases
                        compileBoolExprChecked?_p02StructuralExprTarget?_exists
                          hCondition with
                        ⟨targetCondition, hTargetCondition⟩
                      rcases
                        compileStmtChecked?_p02StructuralStmtTarget?_exists
                          hThen with
                        ⟨targetThen, hTargetThen⟩
                      rcases
                        compileStmtChecked?_p02StructuralStmtTarget?_exists
                          hElse with
                        ⟨targetElse, hTargetElse⟩
                      have hEval := conditionChecked.eval
                      unfold L01_ValidSolidity.Expr.Eval at hEval
                      have hConditionTy :
                          conditionChecked.expr.resultTyIsBool = true := by
                        simp [L01_ValidSolidity.Expr.resultTyIsBool,
                          conditionChecked.resultTy,
                          L01_ValidSolidity.Ty.isBool]
                      by_cases hTruthy :
                          SolidCore.Solidity.Source.wordTruthy
                            conditionChecked.value
                      · simp [
                          P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                          hCondition, hThen, hElse, hTruthy] at hCompile
                        cases hCompile
                        exact
                          ⟨L02_AbstractYul.Stmt.ifElse targetCondition
                              targetThen targetElse,
                            by
                              simp [
                                P02_ValidSolidityToAbstractYul.structuralStmtTarget?,
                                hTargetCondition, hTargetThen, hTargetElse,
                                hConditionTy, hEval]⟩
                      · simp [
                          P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                          hCondition, hThen, hElse, hTruthy] at hCompile
                        cases hCompile
                        exact
                          ⟨L02_AbstractYul.Stmt.ifElse targetCondition
                              targetThen targetElse,
                            by
                              simp [
                                P02_ValidSolidityToAbstractYul.structuralStmtTarget?,
                                hTargetCondition, hTargetThen, hTargetElse,
                                hConditionTy, hEval]⟩
  | _, L00_SourceSolidity.Stmt.empty, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.varDecl _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.expr _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.whileLoop _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.doWhile _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.forLoop _ _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.tryCatch _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.tryCatchReturns _ _ _ _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.emitEvent _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.revertCall _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.break, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.continue, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.unchecked _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.inlineAssembly _, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile
  | _, L00_SourceSolidity.Stmt.modifierPlaceholder, _, hCompile => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
        at hCompile

theorem compileFunctionChecked?_p02StructuralFunctionTarget?_exists
    {source : L00_SourceSolidity.FunctionDecl}
    {checked :
      P01_SourceSolidityToValidSolidity.CheckedFunction source}
    (hCompile :
      P01_SourceSolidityToValidSolidity.compileFunctionChecked? source =
        some checked) :
    ∃ target,
      P02_ValidSolidityToAbstractYul.structuralFunctionTarget?
          checked.function =
        some target := by
  cases source with
  | mk kind name params returns visibility mutability virtualFlag overrideSpec
      modifiers body =>
      cases kind <;> try
        simp [P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
          at hCompile
      case function =>
        cases name with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
              at hCompile
        | some sourceName =>
            cases params with
            | cons param rest =>
                simp [
                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                  at hCompile
            | nil =>
                cases returns with
                | nil =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                      at hCompile
                | cons returnParam returnRest =>
                    cases returnRest with
                    | cons returnParam' returnRest' =>
                        simp [
                          P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                          at hCompile
                    | nil =>
                        cases returnParam with
                        | mk returnName returnTy returnLocation =>
                            cases returnTy <;> try
                              simp [
                                P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                at hCompile
                            case uint bits =>
                              by_cases hBits : bits = 256
                              · subst bits
                                cases visibility with
                                | none =>
                                    simp [
                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                      at hCompile
                                | some visibilityValue =>
                                    cases visibilityValue <;> try
                                      simp [
                                        P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                        at hCompile
                                    ·
                                      cases mutability <;> try
                                        simp [
                                          P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                          at hCompile
                                      ·
                                        cases modifiers with
                                        | cons modifier rest =>
                                            simp [
                                              P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                              at hCompile
                                        | nil =>
                                            cases body with
                                            | none =>
                                                simp [
                                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                                  at hCompile
                                            | some body =>
                                                let fn :
                                                    L00_SourceSolidity.FunctionDecl :=
                                                  { kind :=
                                                      L00_SourceSolidity.FunctionKind.function
                                                    name := some sourceName
                                                    params := []
                                                    returns :=
                                                      [{ name := returnName
                                                         ty :=
                                                          L00_SourceSolidity.Ty.uint
                                                            256
                                                         location :=
                                                          returnLocation }]
                                                    visibility :=
                                                      some
                                                        L00_SourceSolidity.Visibility.public_
                                                    mutability :=
                                                      L00_SourceSolidity.StateMutability.pure
                                                    virtual := virtualFlag
                                                    override? := overrideSpec
                                                    modifiers := []
                                                    body := some body }
                                                change
                                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?
                                                      fn =
                                                    some checked at hCompile
                                                cases hStmt :
                                                    P01_SourceSolidityToValidSolidity.compileStmtChecked?
                                                      [fn] body with
                                                | none =>
                                                    simp [fn,
                                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                                      hStmt] at hCompile
                                                | some stmtChecked =>
                                                    have hCompile' :=
                                                      hCompile
                                                    simp [fn,
                                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                                      hStmt] at hCompile'
                                                    cases hCompile'
                                                    rcases
                                                      compileStmtChecked?_p02StructuralStmtTarget?_exists
                                                        hStmt with
                                                      ⟨targetStmt,
                                                        hTargetStmt⟩
                                                    exact
                                                      ⟨L02_AbstractYul.Entry.withSourceBody
                                                          L01_ValidSolidity.FunctionId.entry
                                                          targetStmt,
                                                        by
                                                          simp [
                                                            P02_ValidSolidityToAbstractYul.structuralFunctionTarget?,
                                                            L01_ValidSolidity.FunctionDecl.withBody,
                                                            L01_ValidSolidity.ReturnVar.isUint256,
                                                            L01_ValidSolidity.ReturnVar.word0,
                                                            L01_ValidSolidity.Ty.isUint256,
                                                            L01_ValidSolidity.Ty.uint256,
                                                            hTargetStmt]⟩
                              · simp [
                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                  hBits] at hCompile

theorem compileContractChecked?_p02StructuralContractTarget?_exists
    {source : L00_SourceSolidity.ContractDecl}
    {checked :
      P01_SourceSolidityToValidSolidity.CheckedContract source}
    (hCompile :
      P01_SourceSolidityToValidSolidity.compileContractChecked? source =
        some checked) :
    ∃ target,
      P02_ValidSolidityToAbstractYul.structuralContractTarget?
          checked.contract =
        some target := by
  cases source with
  | mk kind contractName abstract bases items =>
      cases kind <;> try
        simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
          at hCompile
      case contract =>
        cases abstract <;> try
          simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
            at hCompile
        case false =>
          cases bases with
          | cons base rest =>
              simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
                at hCompile
          | nil =>
              cases items with
              | nil =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileContractChecked?]
                    at hCompile
              | cons item rest =>
                  cases rest with
                  | cons item' rest' =>
                      simp [
                        P01_SourceSolidityToValidSolidity.compileContractChecked?]
                        at hCompile
                  | nil =>
                      cases item <;> try
                        simp [
                          P01_SourceSolidityToValidSolidity.compileContractChecked?]
                          at hCompile
                      case function fn =>
                        let contract : L00_SourceSolidity.ContractDecl :=
                          { kind := L00_SourceSolidity.ContractKind.contract
                            name := contractName
                            abstract := false
                            bases := []
                            items :=
                              [L00_SourceSolidity.ContractItem.function fn] }
                        change
                          P01_SourceSolidityToValidSolidity.compileContractChecked?
                              contract =
                            some checked at hCompile
                        cases hFn :
                            P01_SourceSolidityToValidSolidity.compileFunctionChecked?
                              fn with
                        | none =>
                            simp [contract,
                              P01_SourceSolidityToValidSolidity.compileContractChecked?,
                              hFn] at hCompile
                        | some fnChecked =>
                            have hCompile' := hCompile
                            simp [contract,
                              P01_SourceSolidityToValidSolidity.compileContractChecked?,
                              hFn] at hCompile'
                            cases hCompile'
                            rcases
                              compileFunctionChecked?_p02StructuralFunctionTarget?_exists
                                hFn with
                              ⟨targetFn, hTargetFn⟩
                            exact
                              ⟨targetFn,
                                by
                                  simp [
                                    P02_ValidSolidityToAbstractYul.structuralContractTarget?,
                                    L01_ValidSolidity.ContractDecl.withFunction,
                                    hTargetFn]⟩

theorem compileSourceChecked?_p02StructuralProgramTarget?_exists
    {source : L00_SourceSolidity.SourceUnit}
    {checked :
      P01_SourceSolidityToValidSolidity.CheckedProgram source}
    (hCompile :
      P01_SourceSolidityToValidSolidity.compileSourceChecked? source =
        some checked) :
    ∃ target,
      P02_ValidSolidityToAbstractYul.structuralProgramTarget?
          checked.program =
        some target := by
  cases source with
  | mk items =>
      cases items with
      | nil =>
          simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
            at hCompile
      | cons item rest =>
          cases rest with
          | cons item' rest' =>
              simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
                at hCompile
          | nil =>
              cases item <;> try
                simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
                  at hCompile
              case contract contract =>
                let sourceUnit : L00_SourceSolidity.SourceUnit :=
                  { items :=
                      [L00_SourceSolidity.SourceItem.contract contract] }
                change
                  P01_SourceSolidityToValidSolidity.compileSourceChecked?
                      sourceUnit =
                    some checked at hCompile
                cases hContract :
                    P01_SourceSolidityToValidSolidity.compileContractChecked?
                      contract with
                | none =>
                    simp [sourceUnit,
                      P01_SourceSolidityToValidSolidity.compileSourceChecked?,
                      hContract] at hCompile
                | some contractChecked =>
                    have hCompile' := hCompile
                    simp [sourceUnit,
                      P01_SourceSolidityToValidSolidity.compileSourceChecked?,
                      hContract] at hCompile'
                    cases hCompile'
                    rcases
                      compileContractChecked?_p02StructuralContractTarget?_exists
                        hContract with
                      ⟨targetEntry, hTargetEntry⟩
                    exact
                      ⟨L02_AbstractYul.Program.withEntry targetEntry,
                        by
                          simp [
                            P02_ValidSolidityToAbstractYul.structuralProgramTarget?,
                            L01_ValidSolidity.Program.withContract,
                            hTargetEntry]⟩

theorem check?_p02Accepted
    {source : L00_SourceSolidity.SourceUnit}
    {artifact : P01_SourceSolidityToValidSolidity.Artifact}
    (hCheck :
      P01_SourceSolidityToValidSolidity.check? source = some artifact) :
    P02_ValidSolidityToAbstractYul.Accepted artifact.program := by
  by_cases hEmpty : source.items.isEmpty
  · simp [P01_SourceSolidityToValidSolidity.check?, hEmpty] at hCheck
    cases hCheck
    simp [P02_ValidSolidityToAbstractYul.Accepted,
      P02_ValidSolidityToAbstractYul.accepted?,
      P02_ValidSolidityToAbstractYul.programEmptyShape?,
      L01_ValidSolidity.Program.empty]
  · cases hChecked :
        P01_SourceSolidityToValidSolidity.compileSourceChecked? source with
    | none =>
        simp [P01_SourceSolidityToValidSolidity.check?, hEmpty, hChecked]
          at hCheck
    | some checked =>
        simp [P01_SourceSolidityToValidSolidity.check?, hEmpty, hChecked]
          at hCheck
        cases hCheck
        rcases compileSourceChecked?_p02StructuralProgramTarget?_exists
            hChecked with
          ⟨target, hTarget⟩
        unfold P02_ValidSolidityToAbstractYul.Accepted
        unfold P02_ValidSolidityToAbstractYul.accepted?
        cases hEmptyShape :
            P02_ValidSolidityToAbstractYul.programEmptyShape?
              checked.program
        · simp [hEmptyShape, hTarget]
        · simp [hEmptyShape]

end P01ToP02

namespace P01P02ToP03

open Passes

theorem compileExprChecked?_p03StructuralExprTarget?_exists :
    ∀ {source : L00_SourceSolidity.Expr}
      {p01 :
        P01_SourceSolidityToValidSolidity.CheckedExpr source}
      {p02 :
        P02_ValidSolidityToAbstractYul.CheckedExpr p01.expr},
      P01_SourceSolidityToValidSolidity.compileExprChecked? source =
        some p01 ->
      P02_ValidSolidityToAbstractYul.compileExprChecked? p01.expr =
        some p02 ->
        ∃ target,
          P03_AbstractYulToGeneratedYul.structuralExprTarget?
              p02.expr =
            some target ∧
          target.eval? = p02.expr.eval?
  | L00_SourceSolidity.Expr.literal lit, p01, p02, hP01, hP02 => by
      cases lit with
      | number raw =>
          by_cases hRaw :
              P01_SourceSolidityToValidSolidity.decimalLiteralAccepted? raw
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hP01
            cases hP01
            simp [P02_ValidSolidityToAbstractYul.compileExprChecked?,
              L01_ValidSolidity.Expr.word,
              L01_ValidSolidity.Ty.uint256] at hP02
            cases hP02
            exact
              ⟨L03_GeneratedYul.Expr.word
                  (L00_SourceSolidity.Executable.parseDecimalNat raw),
                by
                  constructor
                  · simp [
                      P03_AbstractYulToGeneratedYul.structuralExprTarget?]
                  · simp [L03_GeneratedYul.Expr.eval?,
                      L03_GeneratedYul.Expr.evalWith?,
                      L02_AbstractYul.Expr.eval?,
                      L02_AbstractYul.Expr.toCore?,
                      L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                      L00_SourceSolidity.Executable.CoreExpr.evalWord?,
                      L00_SourceSolidity.Executable.CoreValue.asWord?,
                      SolidCore.Solidity.Source.Expr.eval,
                      SolidCore.Solidity.Source.Value.asWord?,
                      SolidCore.Solidity.Source.normWord,
                      SharedSemantics.norm_norm]⟩
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hP01
        | bool _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
        | unitNumber _ _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
        | string _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
      | hexString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | unicodeString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | address _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | bytes _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
  | L00_SourceSolidity.Expr.binary op lhs rhs, p01, p02, hP01, hP02 => by
      cases op <;> try
        simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
          at hP01
      case add =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hP01
            | some rhsP01 =>
                cases hAdd :
                    P01_SourceSolidityToValidSolidity.checkedAddChecked?
                      lhsP01.value rhsP01.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hAdd] at hP01
                | some addChecked =>
                    have hP01Eval := p01.eval
                    have hP02Eval := p02.eval_eq
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.add lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hAdd] at hP01
                    split at hP01
                    ·
                        cases hP01
                        cases hP02Lhs :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              lhsP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileExprChecked?,
                              L01_ValidSolidity.Expr.add,
                              L01_ValidSolidity.Ty.uint256,
                              hP02Lhs] at hP02
                        | some lhsP02 =>
                            cases hP02Rhs :
                                P02_ValidSolidityToAbstractYul.compileExprChecked?
                                  rhsP01.expr with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.add,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                            | some rhsP02 =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.add,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                                cases hP02
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hLhs hP02Lhs with
                                  ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hRhs hP02Rhs with
                                  ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                                have hLhsTargetEval :
                                    lhsTarget.eval? = some lhsP01.value := by
                                  rw [hLhsEval, lhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using lhsP01.eval
                                have hRhsTargetEval :
                                    rhsTarget.eval? = some rhsP01.value := by
                                  rw [hRhsEval, rhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using rhsP01.eval
                                have hLhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        lhsTarget =
                                      some lhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hLhsTargetEval
                                have hRhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        rhsTarget =
                                      some rhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hRhsTargetEval
                                have hAddValue :
                                    SharedSemantics.addWord
                                        lhsP01.value rhsP01.value =
                                      addChecked.value :=
                                  P01_SourceSolidityToValidSolidity.checkedAddChecked?_addWord
                                    hAdd
                                have hTargetEval :
                                    (L03_GeneratedYul.Expr.add
                                        lhsTarget rhsTarget).eval? =
                                      some addChecked.value := by
                                  simp [L03_GeneratedYul.Expr.add,
                                    L03_GeneratedYul.Expr.eval?,
                                    L03_GeneratedYul.Expr.evalWith?,
                                      hLhsTargetEvalWith,
                                      hRhsTargetEvalWith,
                                      hAddValue]
                                have hP01Eval' :
                                    (L01_ValidSolidity.Expr.add
                                        lhsP01.expr rhsP01.expr).eval? =
                                      some addChecked.value := by
                                  simpa [L01_ValidSolidity.Expr.Eval,
                                    L01_ValidSolidity.Expr.add]
                                    using hP01Eval
                                have hSourceEval :
                                    (L02_AbstractYul.Expr.add
                                        lhsP02.expr rhsP02.expr).eval? =
                                      some addChecked.value := by
                                  rw [hP02Eval]
                                  exact hP01Eval'
                                have hEval :
                                    (L03_GeneratedYul.Expr.add
                                        lhsTarget rhsTarget).eval? =
                                      (L02_AbstractYul.Expr.add
                                        lhsP02.expr rhsP02.expr).eval? := by
                                  rw [hTargetEval, hSourceEval]
                                exact
                                  ⟨L03_GeneratedYul.Expr.add
                                      lhsTarget rhsTarget,
                                    by
                                      constructor
                                      · simp [
                                          P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                          L02_AbstractYul.Expr.add,
                                          hLhsTarget, hRhsTarget, hEval]
                                      · exact hEval⟩
                    ·
                        cases hP01
      case sub =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hP01
            | some rhsP01 =>
                cases hSub :
                    P01_SourceSolidityToValidSolidity.checkedSubChecked?
                      lhsP01.value rhsP01.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hSub] at hP01
                | some subChecked =>
                    have hP01Eval := p01.eval
                    have hP02Eval := p02.eval_eq
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.sub lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hSub] at hP01
                    split at hP01
                    ·
                        cases hP01
                        cases hP02Lhs :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              lhsP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileExprChecked?,
                              L01_ValidSolidity.Expr.sub,
                              L01_ValidSolidity.Ty.uint256,
                              hP02Lhs] at hP02
                        | some lhsP02 =>
                            cases hP02Rhs :
                                P02_ValidSolidityToAbstractYul.compileExprChecked?
                                  rhsP01.expr with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.sub,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                            | some rhsP02 =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.sub,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                                cases hP02
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hLhs hP02Lhs with
                                  ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hRhs hP02Rhs with
                                  ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                                have hLhsTargetEval :
                                    lhsTarget.eval? = some lhsP01.value := by
                                  rw [hLhsEval, lhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using lhsP01.eval
                                have hRhsTargetEval :
                                    rhsTarget.eval? = some rhsP01.value := by
                                  rw [hRhsEval, rhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using rhsP01.eval
                                have hLhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        lhsTarget =
                                      some lhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hLhsTargetEval
                                have hRhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        rhsTarget =
                                      some rhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hRhsTargetEval
                                have hSubValue :
                                    SharedSemantics.subWord
                                        lhsP01.value rhsP01.value =
                                      subChecked.value :=
                                  P01_SourceSolidityToValidSolidity.checkedSubChecked?_subWord
                                    hSub
                                have hTargetEval :
                                    (L03_GeneratedYul.Expr.sub
                                        lhsTarget rhsTarget).eval? =
                                      some subChecked.value := by
                                  simp [L03_GeneratedYul.Expr.sub,
                                    L03_GeneratedYul.Expr.eval?,
                                    L03_GeneratedYul.Expr.evalWith?,
                                    hLhsTargetEvalWith,
                                    hRhsTargetEvalWith,
                                    hSubValue]
                                have hP01Eval' :
                                    (L01_ValidSolidity.Expr.sub
                                        lhsP01.expr rhsP01.expr).eval? =
                                      some subChecked.value := by
                                  simpa [L01_ValidSolidity.Expr.Eval,
                                    L01_ValidSolidity.Expr.sub]
                                    using hP01Eval
                                have hSourceEval :
                                    (L02_AbstractYul.Expr.sub
                                        lhsP02.expr rhsP02.expr).eval? =
                                      some subChecked.value := by
                                  rw [hP02Eval]
                                  exact hP01Eval'
                                have hEval :
                                    (L03_GeneratedYul.Expr.sub
                                        lhsTarget rhsTarget).eval? =
                                      (L02_AbstractYul.Expr.sub
                                        lhsP02.expr rhsP02.expr).eval? := by
                                  rw [hTargetEval, hSourceEval]
                                exact
                                  ⟨L03_GeneratedYul.Expr.sub
                                      lhsTarget rhsTarget,
                                    by
                                      constructor
                                      · simp [
                                          P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                          L02_AbstractYul.Expr.sub,
                                          hLhsTarget, hRhsTarget, hEval]
                                      · exact hEval⟩
                    ·
                        cases hP01
      case mul =>
        cases hLhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hP01
            | some rhsP01 =>
                cases hMul :
                    P01_SourceSolidityToValidSolidity.checkedMulChecked?
                      lhsP01.value rhsP01.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hMul] at hP01
                | some mulChecked =>
                    have hP01Eval := p01.eval
                    have hP02Eval := p02.eval_eq
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.mul lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hMul] at hP01
                    split at hP01
                    ·
                        cases hP01
                        cases hP02Lhs :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              lhsP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileExprChecked?,
                              L01_ValidSolidity.Expr.mul,
                              L01_ValidSolidity.Ty.uint256,
                              hP02Lhs] at hP02
                        | some lhsP02 =>
                            cases hP02Rhs :
                                P02_ValidSolidityToAbstractYul.compileExprChecked?
                                  rhsP01.expr with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.mul,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                            | some rhsP02 =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.mul,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                                cases hP02
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hLhs hP02Lhs with
                                  ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                                rcases
                                  compileExprChecked?_p03StructuralExprTarget?_exists
                                    hRhs hP02Rhs with
                                  ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                                have hLhsTargetEval :
                                    lhsTarget.eval? = some lhsP01.value := by
                                  rw [hLhsEval, lhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using lhsP01.eval
                                have hRhsTargetEval :
                                    rhsTarget.eval? = some rhsP01.value := by
                                  rw [hRhsEval, rhsP02.eval_eq]
                                  simpa [L01_ValidSolidity.Expr.Eval]
                                    using rhsP01.eval
                                have hLhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        lhsTarget =
                                      some lhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hLhsTargetEval
                                have hRhsTargetEvalWith :
                                    L03_GeneratedYul.Expr.evalWith? []
                                        rhsTarget =
                                      some rhsP01.value := by
                                  simpa [L03_GeneratedYul.Expr.eval?]
                                    using hRhsTargetEval
                                have hMulValue :
                                    SharedSemantics.mulWord
                                        lhsP01.value rhsP01.value =
                                      mulChecked.value :=
                                  P01_SourceSolidityToValidSolidity.checkedMulChecked?_mulWord
                                    hMul
                                have hTargetEval :
                                    (L03_GeneratedYul.Expr.mul
                                        lhsTarget rhsTarget).eval? =
                                      some mulChecked.value := by
                                  simp [L03_GeneratedYul.Expr.mul,
                                    L03_GeneratedYul.Expr.eval?,
                                    L03_GeneratedYul.Expr.evalWith?,
                                    hLhsTargetEvalWith,
                                    hRhsTargetEvalWith,
                                    hMulValue]
                                have hP01Eval' :
                                    (L01_ValidSolidity.Expr.mul
                                        lhsP01.expr rhsP01.expr).eval? =
                                      some mulChecked.value := by
                                  simpa [L01_ValidSolidity.Expr.Eval,
                                    L01_ValidSolidity.Expr.mul]
                                    using hP01Eval
                                have hSourceEval :
                                    (L02_AbstractYul.Expr.mul
                                        lhsP02.expr rhsP02.expr).eval? =
                                      some mulChecked.value := by
                                  rw [hP02Eval]
                                  exact hP01Eval'
                                have hEval :
                                    (L03_GeneratedYul.Expr.mul
                                        lhsTarget rhsTarget).eval? =
                                      (L02_AbstractYul.Expr.mul
                                        lhsP02.expr rhsP02.expr).eval? := by
                                  rw [hTargetEval, hSourceEval]
                                exact
                                  ⟨L03_GeneratedYul.Expr.mul
                                      lhsTarget rhsTarget,
                                    by
                                      constructor
                                      · simp [
                                          P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                          L02_AbstractYul.Expr.mul,
                                          hLhsTarget, hRhsTarget, hEval]
                                      · exact hEval⟩
                    ·
                      cases hP01
      case bitAnd =>
        have hP01Eval := p01.eval
        have hP02Eval := p02.eval_eq
        let source :=
          L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              source, hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  source, hLhs, hRhs] at hP01
            | some rhsP01 =>
                by_cases hNotFolded :
                    P01_SourceSolidityToValidSolidity.sourceBinaryBitAndNotFolded?
                        source = some ()
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                        L01_ValidSolidity.Expr.bitAnd,
                        L01_ValidSolidity.Ty.uint256,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                            L01_ValidSolidity.Expr.bitAnd,
                            L01_ValidSolidity.Ty.uint256,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                            L01_ValidSolidity.Expr.bitAnd,
                            L01_ValidSolidity.Ty.uint256,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hLhs hP02Lhs with
                            ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hRhs hP02Rhs with
                            ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                          have hLhsTargetEval :
                              lhsTarget.eval? = some lhsP01.value := by
                            rw [hLhsEval, lhsP02.eval_eq]
                            simpa [L01_ValidSolidity.Expr.Eval]
                              using lhsP01.eval
                          have hRhsTargetEval :
                              rhsTarget.eval? = some rhsP01.value := by
                            rw [hRhsEval, rhsP02.eval_eq]
                            simpa [L01_ValidSolidity.Expr.Eval]
                              using rhsP01.eval
                          have hLhsTargetEvalWith :
                              L03_GeneratedYul.Expr.evalWith? []
                                  lhsTarget =
                                some lhsP01.value := by
                            simpa [L03_GeneratedYul.Expr.eval?]
                              using hLhsTargetEval
                          have hRhsTargetEvalWith :
                              L03_GeneratedYul.Expr.evalWith? []
                                  rhsTarget =
                                some rhsP01.value := by
                            simpa [L03_GeneratedYul.Expr.eval?]
                              using hRhsTargetEval
                          have hTargetEval :
                              (L03_GeneratedYul.Expr.bitAnd
                                  lhsTarget rhsTarget).eval? =
                                some
                                  (SharedSemantics.andWord
                                    lhsP01.value rhsP01.value) := by
                            simp [L03_GeneratedYul.Expr.bitAnd,
                              L03_GeneratedYul.Expr.eval?,
                              L03_GeneratedYul.Expr.evalWith?,
                              hLhsTargetEvalWith,
                              hRhsTargetEvalWith]
                          have hP01Eval' :
                              (L01_ValidSolidity.Expr.bitAnd
                                  lhsP01.expr rhsP01.expr).eval? =
                                some
                                  (SharedSemantics.andWord
                                    lhsP01.value rhsP01.value) := by
                            simpa [L01_ValidSolidity.Expr.Eval,
                              L01_ValidSolidity.Expr.bitAnd,
                              P01_SourceSolidityToValidSolidity.bitAndCheckedExpr]
                              using hP01Eval
                          have hSourceEval :
                              (L02_AbstractYul.Expr.bitAnd
                                  lhsP02.expr rhsP02.expr).eval? =
                                some
                                  (SharedSemantics.andWord
                                    lhsP01.value rhsP01.value) := by
                            rw [hP02Eval]
                            exact hP01Eval'
                          have hEval :
                              (L03_GeneratedYul.Expr.bitAnd
                                  lhsTarget rhsTarget).eval? =
                                (L02_AbstractYul.Expr.bitAnd
                                  lhsP02.expr rhsP02.expr).eval? := by
                            rw [hTargetEval, hSourceEval]
                          exact
                            ⟨L03_GeneratedYul.Expr.bitAnd
                                lhsTarget rhsTarget,
                              by
                                constructor
                                · simp [
                                    P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                    L02_AbstractYul.Expr.bitAnd,
                                    hLhsTarget, hRhsTarget, hEval]
                                · exact hEval⟩
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hP01
  | L00_SourceSolidity.Expr.ident _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.member _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.index _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.slice _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.tuple _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.unary _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.ternary _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.assign _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.call _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.callWithOptions _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.newExpr _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.array _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.enumFromUInt _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.payableConversion _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.typeName _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01

theorem compileBoolExprChecked?_p03StructuralExprTarget?_exists
    {source : L00_SourceSolidity.Expr}
    {p01 :
      P01_SourceSolidityToValidSolidity.CheckedBoolExpr source}
    {p02 :
      P02_ValidSolidityToAbstractYul.CheckedExpr p01.expr}
    (hP01 :
      P01_SourceSolidityToValidSolidity.compileBoolExprChecked? source =
        some p01)
    (hP02 :
      P02_ValidSolidityToAbstractYul.compileExprChecked? p01.expr =
        some p02) :
    ∃ target,
      P03_AbstractYulToGeneratedYul.structuralExprTarget?
          p02.expr =
        some target ∧
      target.eval? = p02.expr.eval? := by
  cases source <;>
    simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
      at hP01
  case literal lit =>
    cases lit <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hP01
    case bool value =>
      cases hP01
      simp [P02_ValidSolidityToAbstractYul.compileExprChecked?,
        L01_ValidSolidity.Expr.bool,
        L01_ValidSolidity.Ty.bool] at hP02
      cases hP02
      exact
        ⟨L03_GeneratedYul.Expr.word
            (SolidCore.Solidity.Source.boolWord value),
          by
            constructor
            · simp [
                P03_AbstractYulToGeneratedYul.structuralExprTarget?]
            · cases value <;> rfl⟩
  case binary op lhs rhs =>
    cases op <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hP01
    case lt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryLtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.lt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  have hP01Eval := p01.eval
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.ltOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.ltOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hP02Eval := p02.eval_eq
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hLhs hP02Lhs with
                            ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hRhs hP02Rhs with
                            ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.ltOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          have hEval :
                              (L03_GeneratedYul.Expr.ltOp
                                  lhsTarget rhsTarget).eval? =
                                (L02_AbstractYul.Expr.ltOp
                                  lhsP02.expr rhsP02.expr).eval? := by
                            have hLhsTargetEval :
                                lhsTarget.eval? = some lhsP01.value := by
                              rw [hLhsEval, lhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using lhsP01.eval
                            have hRhsTargetEval :
                                rhsTarget.eval? = some rhsP01.value := by
                              rw [hRhsEval, rhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using rhsP01.eval
                            have hLhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    lhsTarget =
                                  some lhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hLhsTargetEval
                            have hRhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    rhsTarget =
                                  some rhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hRhsTargetEval
                            have hTargetEval :
                                (L03_GeneratedYul.Expr.ltOp
                                    lhsTarget rhsTarget).eval? =
                                  some
                                    (SharedSemantics.ltWord
                                      lhsP01.value rhsP01.value) := by
                              simp [L03_GeneratedYul.Expr.ltOp,
                                L03_GeneratedYul.Expr.eval?,
                                L03_GeneratedYul.Expr.evalWith?,
                                hLhsTargetEvalWith,
                                hRhsTargetEvalWith]
                            have hP01Eval' :
                                (L01_ValidSolidity.Expr.ltOp
                                    lhsP01.expr rhsP01.expr).eval? =
                                  some
                                    (SharedSemantics.ltWord
                                      lhsP01.value rhsP01.value) := by
                              simpa [L01_ValidSolidity.Expr.Eval,
                                L01_ValidSolidity.Expr.ltOp]
                                using hP01Eval
                            have hSourceEval :
                                (L02_AbstractYul.Expr.ltOp
                                    lhsP02.expr rhsP02.expr).eval? =
                                  some
                                    (SharedSemantics.ltWord
                                      lhsP01.value rhsP01.value) := by
                              rw [hP02Eval]
                              exact hP01Eval'
                            rw [hTargetEval, hSourceEval]
                          have hEval' :
                              (L03_GeneratedYul.Expr.builtin
                                  SolidCoreYulCore.Evm.Builtin.ltOp
                                  [lhsTarget, rhsTarget]).eval? =
                                (L02_AbstractYul.Expr.binary
                                  L02_AbstractYul.BinaryOp.lt
                                  lhsP02.expr rhsP02.expr).eval? := by
                            simpa [L03_GeneratedYul.Expr.ltOp,
                              L02_AbstractYul.Expr.ltOp] using hEval
                          exact
                            ⟨L03_GeneratedYul.Expr.ltOp
                                lhsTarget rhsTarget,
                              by
                                constructor
                                · simp [
                                    P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                    L02_AbstractYul.Expr.ltOp,
                                    L03_GeneratedYul.Expr.ltOp,
                                    hLhsTarget, hRhsTarget]
                                  exact hEval'
                                · simpa [L03_GeneratedYul.Expr.ltOp,
                                    L02_AbstractYul.Expr.ltOp] using hEval⟩
    case gt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryGtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.gt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  have hP01Eval := p01.eval
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.gtOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.gtOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hP02Eval := p02.eval_eq
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hLhs hP02Lhs with
                            ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hRhs hP02Rhs with
                            ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.gtOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          have hEval :
                              (L03_GeneratedYul.Expr.gtOp
                                  lhsTarget rhsTarget).eval? =
                                (L02_AbstractYul.Expr.gtOp
                                  lhsP02.expr rhsP02.expr).eval? := by
                            have hLhsTargetEval :
                                lhsTarget.eval? = some lhsP01.value := by
                              rw [hLhsEval, lhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using lhsP01.eval
                            have hRhsTargetEval :
                                rhsTarget.eval? = some rhsP01.value := by
                              rw [hRhsEval, rhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using rhsP01.eval
                            have hLhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    lhsTarget =
                                  some lhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hLhsTargetEval
                            have hRhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    rhsTarget =
                                  some rhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hRhsTargetEval
                            have hTargetEval :
                                (L03_GeneratedYul.Expr.gtOp
                                    lhsTarget rhsTarget).eval? =
                                  some
                                    (SharedSemantics.gtWord
                                      lhsP01.value rhsP01.value) := by
                              simp [L03_GeneratedYul.Expr.gtOp,
                                L03_GeneratedYul.Expr.eval?,
                                L03_GeneratedYul.Expr.evalWith?,
                                hLhsTargetEvalWith,
                                hRhsTargetEvalWith]
                            have hP01Eval' :
                                (L01_ValidSolidity.Expr.gtOp
                                    lhsP01.expr rhsP01.expr).eval? =
                                  some
                                    (SharedSemantics.gtWord
                                      lhsP01.value rhsP01.value) := by
                              simpa [L01_ValidSolidity.Expr.Eval,
                                L01_ValidSolidity.Expr.gtOp]
                                using hP01Eval
                            have hSourceEval :
                                (L02_AbstractYul.Expr.gtOp
                                    lhsP02.expr rhsP02.expr).eval? =
                                  some
                                    (SharedSemantics.gtWord
                                      lhsP01.value rhsP01.value) := by
                              rw [hP02Eval]
                              exact hP01Eval'
                            rw [hTargetEval, hSourceEval]
                          have hEval' :
                              (L03_GeneratedYul.Expr.builtin
                                  SolidCoreYulCore.Evm.Builtin.gtOp
                                  [lhsTarget, rhsTarget]).eval? =
                                (L02_AbstractYul.Expr.binary
                                  L02_AbstractYul.BinaryOp.gt
                                  lhsP02.expr rhsP02.expr).eval? := by
                            simpa [L03_GeneratedYul.Expr.gtOp,
                              L02_AbstractYul.Expr.gtOp] using hEval
                          exact
                            ⟨L03_GeneratedYul.Expr.gtOp
                                lhsTarget rhsTarget,
                              by
                                constructor
                                · simp [
                                    P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                    L02_AbstractYul.Expr.gtOp,
                                    L03_GeneratedYul.Expr.gtOp,
                                    hLhsTarget, hRhsTarget]
                                  exact hEval'
                                · simpa [L03_GeneratedYul.Expr.gtOp,
                                    L02_AbstractYul.Expr.gtOp] using hEval⟩
    case eq =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryEqNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.eq lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  have hP01Eval := p01.eval
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.eqOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.eqOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hP02Eval := p02.eval_eq
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hLhs hP02Lhs with
                            ⟨lhsTarget, hLhsTarget, hLhsEval⟩
                          rcases
                            compileExprChecked?_p03StructuralExprTarget?_exists
                              hRhs hP02Rhs with
                            ⟨rhsTarget, hRhsTarget, hRhsEval⟩
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.eqOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          have hEval :
                              (L03_GeneratedYul.Expr.eqOp
                                  lhsTarget rhsTarget).eval? =
                                (L02_AbstractYul.Expr.eqOp
                                  lhsP02.expr rhsP02.expr).eval? := by
                            have hLhsTargetEval :
                                lhsTarget.eval? = some lhsP01.value := by
                              rw [hLhsEval, lhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using lhsP01.eval
                            have hRhsTargetEval :
                                rhsTarget.eval? = some rhsP01.value := by
                              rw [hRhsEval, rhsP02.eval_eq]
                              simpa [L01_ValidSolidity.Expr.Eval]
                                using rhsP01.eval
                            have hLhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    lhsTarget =
                                  some lhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hLhsTargetEval
                            have hRhsTargetEvalWith :
                                L03_GeneratedYul.Expr.evalWith? []
                                    rhsTarget =
                                  some rhsP01.value := by
                              simpa [L03_GeneratedYul.Expr.eval?]
                                using hRhsTargetEval
                            have hTargetEval :
                                (L03_GeneratedYul.Expr.eqOp
                                    lhsTarget rhsTarget).eval? =
                                  some
                                    (SharedSemantics.eqWord
                                      lhsP01.value rhsP01.value) := by
                              simp [L03_GeneratedYul.Expr.eqOp,
                                L03_GeneratedYul.Expr.eval?,
                                L03_GeneratedYul.Expr.evalWith?,
                                hLhsTargetEvalWith,
                                hRhsTargetEvalWith]
                            have hP01Eval' :
                                (L01_ValidSolidity.Expr.eqOp
                                    lhsP01.expr rhsP01.expr).eval? =
                                  some
                                    (SharedSemantics.eqWord
                                      lhsP01.value rhsP01.value) := by
                              simpa [L01_ValidSolidity.Expr.Eval,
                                L01_ValidSolidity.Expr.eqOp]
                                using hP01Eval
                            have hSourceEval :
                                (L02_AbstractYul.Expr.eqOp
                                    lhsP02.expr rhsP02.expr).eval? =
                                  some
                                    (SharedSemantics.eqWord
                                      lhsP01.value rhsP01.value) := by
                              rw [hP02Eval]
                              exact hP01Eval'
                            rw [hTargetEval, hSourceEval]
                          have hEval' :
                              (L03_GeneratedYul.Expr.builtin
                                  SolidCoreYulCore.Evm.Builtin.eqOp
                                  [lhsTarget, rhsTarget]).eval? =
                                (L02_AbstractYul.Expr.binary
                                  L02_AbstractYul.BinaryOp.eq
                                  lhsP02.expr rhsP02.expr).eval? := by
                            simpa [L03_GeneratedYul.Expr.eqOp,
                              L02_AbstractYul.Expr.eqOp] using hEval
                          exact
                            ⟨L03_GeneratedYul.Expr.eqOp
                                lhsTarget rhsTarget,
                              by
                                constructor
                                · simp [
                                    P03_AbstractYulToGeneratedYul.structuralExprTarget?,
                                    L02_AbstractYul.Expr.eqOp,
                                    L03_GeneratedYul.Expr.eqOp,
                                    hLhsTarget, hRhsTarget]
                                  exact hEval'
                                · simpa [L03_GeneratedYul.Expr.eqOp,
                                    L02_AbstractYul.Expr.eqOp] using hEval⟩

theorem compileExprChecked?_p02ExprResultTy? :
    ∀ {source : L00_SourceSolidity.Expr}
      {p01 :
        P01_SourceSolidityToValidSolidity.CheckedExpr source}
      {p02 :
        P02_ValidSolidityToAbstractYul.CheckedExpr p01.expr},
      P01_SourceSolidityToValidSolidity.compileExprChecked? source =
        some p01 ->
      P02_ValidSolidityToAbstractYul.compileExprChecked? p01.expr =
        some p02 ->
        p02.expr.resultTy? = some L02_AbstractYul.Ty.word
  | L00_SourceSolidity.Expr.literal lit, p01, p02, hP01, hP02 => by
      cases lit with
      | number raw =>
          by_cases hRaw :
              P01_SourceSolidityToValidSolidity.decimalLiteralAccepted? raw
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hP01
            cases hP01
            simp [P02_ValidSolidityToAbstractYul.compileExprChecked?,
              L01_ValidSolidity.Expr.word,
              L01_ValidSolidity.Ty.uint256] at hP02
            cases hP02
            rfl
          · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hRaw] at hP01
        | bool _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
        | unitNumber _ _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
        | string _ =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
              at hP01
      | hexString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | unicodeString _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | address _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
      | bytes _ =>
          simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
            at hP01
  | L00_SourceSolidity.Expr.binary op lhs rhs, p01, p02, hP01, hP02 => by
      cases op <;> try
        simp [P01_SourceSolidityToValidSolidity.compileExprChecked?]
          at hP01
      case add =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hP01
            | some rhsP01 =>
                cases hAdd :
                    P01_SourceSolidityToValidSolidity.checkedAddChecked?
                      lhsP01.value rhsP01.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hAdd] at hP01
                | some addChecked =>
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.add lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hAdd] at hP01
                    split at hP01
                    ·
                        cases hP01
                        cases hP02Lhs :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              lhsP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileExprChecked?,
                              L01_ValidSolidity.Expr.add,
                              L01_ValidSolidity.Ty.uint256,
                              hP02Lhs] at hP02
                        | some lhsP02 =>
                            cases hP02Rhs :
                                P02_ValidSolidityToAbstractYul.compileExprChecked?
                                  rhsP01.expr with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.add,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                            | some rhsP02 =>
                                have hLhsTy :
                                    lhsP02.expr.resultTy? =
                                      some L02_AbstractYul.Ty.word :=
                                  compileExprChecked?_p02ExprResultTy?
                                    hLhs hP02Lhs
                                have hRhsTy :
                                    rhsP02.expr.resultTy? =
                                      some L02_AbstractYul.Ty.word :=
                                  compileExprChecked?_p02ExprResultTy?
                                    hRhs hP02Rhs
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.add,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                                cases hP02
                                simp [L02_AbstractYul.Expr.add,
                                  L02_AbstractYul.Expr.resultTy?,
                                  hLhsTy, hRhsTy]
                    ·
                        cases hP01
      case sub =>
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  hLhs, hRhs] at hP01
            | some rhsP01 =>
                cases hSub :
                    P01_SourceSolidityToValidSolidity.checkedSubChecked?
                      lhsP01.value rhsP01.value with
                | none =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      hLhs, hRhs, hSub] at hP01
                | some subChecked =>
                    let source :=
                      L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.sub lhs rhs
                    simp [
                      P01_SourceSolidityToValidSolidity.compileExprChecked?,
                      source, hLhs, hRhs, hSub] at hP01
                    split at hP01
                    ·
                        cases hP01
                        cases hP02Lhs :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              lhsP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileExprChecked?,
                              L01_ValidSolidity.Expr.sub,
                              L01_ValidSolidity.Ty.uint256,
                              hP02Lhs] at hP02
                        | some lhsP02 =>
                            cases hP02Rhs :
                                P02_ValidSolidityToAbstractYul.compileExprChecked?
                                  rhsP01.expr with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.sub,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                            | some rhsP02 =>
                                have hLhsTy :
                                    lhsP02.expr.resultTy? =
                                      some L02_AbstractYul.Ty.word :=
                                  compileExprChecked?_p02ExprResultTy?
                                    hLhs hP02Lhs
                                have hRhsTy :
                                    rhsP02.expr.resultTy? =
                                      some L02_AbstractYul.Ty.word :=
                                  compileExprChecked?_p02ExprResultTy?
                                    hRhs hP02Rhs
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                  L01_ValidSolidity.Expr.sub,
                                  L01_ValidSolidity.Ty.uint256,
                                  hP02Lhs, hP02Rhs] at hP02
                                cases hP02
                                simp [L02_AbstractYul.Expr.sub,
                                  L02_AbstractYul.Expr.resultTy?,
                                  hLhsTy, hRhsTy]
                    ·
                        cases hP01
      case mul =>
        cases hLhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                hLhs] at hP01
          | some lhsP01 =>
              cases hRhs :
                  P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    hLhs, hRhs] at hP01
              | some rhsP01 =>
                  cases hMul :
                      P01_SourceSolidityToValidSolidity.checkedMulChecked?
                        lhsP01.value rhsP01.value with
                  | none =>
                      simp [
                        P01_SourceSolidityToValidSolidity.compileExprChecked?,
                        hLhs, hRhs, hMul] at hP01
                  | some mulChecked =>
                      let source :=
                        L00_SourceSolidity.Expr.binary
                          L00_SourceSolidity.BinaryOp.mul lhs rhs
                      simp [
                        P01_SourceSolidityToValidSolidity.compileExprChecked?,
                        source, hLhs, hRhs, hMul] at hP01
                      split at hP01
                      ·
                          cases hP01
                          cases hP02Lhs :
                              P02_ValidSolidityToAbstractYul.compileExprChecked?
                                lhsP01.expr with
                          | none =>
                              simp [
                                P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                L01_ValidSolidity.Expr.mul,
                                L01_ValidSolidity.Ty.uint256,
                                hP02Lhs] at hP02
                          | some lhsP02 =>
                              cases hP02Rhs :
                                  P02_ValidSolidityToAbstractYul.compileExprChecked?
                                    rhsP01.expr with
                              | none =>
                                  simp [
                                    P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                    L01_ValidSolidity.Expr.mul,
                                    L01_ValidSolidity.Ty.uint256,
                                    hP02Lhs, hP02Rhs] at hP02
                              | some rhsP02 =>
                                  have hLhsTy :
                                      lhsP02.expr.resultTy? =
                                        some L02_AbstractYul.Ty.word :=
                                    compileExprChecked?_p02ExprResultTy?
                                      hLhs hP02Lhs
                                  have hRhsTy :
                                      rhsP02.expr.resultTy? =
                                        some L02_AbstractYul.Ty.word :=
                                    compileExprChecked?_p02ExprResultTy?
                                      hRhs hP02Rhs
                                  simp [
                                    P02_ValidSolidityToAbstractYul.compileExprChecked?,
                                    L01_ValidSolidity.Expr.mul,
                                    L01_ValidSolidity.Ty.uint256,
                                    hP02Lhs, hP02Rhs] at hP02
                                  cases hP02
                                  simp [L02_AbstractYul.Expr.mul,
                                    L02_AbstractYul.Expr.resultTy?,
                                    hLhsTy, hRhsTy]
                      ·
                        cases hP01
      case bitAnd =>
        let source :=
          L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
        cases hLhs :
            P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
              source, hLhs] at hP01
        | some lhsP01 =>
            cases hRhs :
                P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
            | none =>
                simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                  source, hLhs, hRhs] at hP01
            | some rhsP01 =>
                by_cases hNotFolded :
                    P01_SourceSolidityToValidSolidity.sourceBinaryBitAndNotFolded?
                        source = some ()
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                        L01_ValidSolidity.Expr.bitAnd,
                        L01_ValidSolidity.Ty.uint256,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                            L01_ValidSolidity.Expr.bitAnd,
                            L01_ValidSolidity.Ty.uint256,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hLhsTy :
                              lhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hLhs hP02Lhs
                          have hRhsTy :
                              rhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hRhs hP02Rhs
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            P01_SourceSolidityToValidSolidity.bitAndCheckedExpr,
                            L01_ValidSolidity.Expr.bitAnd,
                            L01_ValidSolidity.Ty.uint256,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          simp [L02_AbstractYul.Expr.bitAnd,
                            L02_AbstractYul.Expr.resultTy?,
                            hLhsTy, hRhsTy]
                · simp [P01_SourceSolidityToValidSolidity.compileExprChecked?,
                    source, hLhs, hRhs, hNotFolded] at hP01
  | L00_SourceSolidity.Expr.ident _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.member _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.index _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.slice _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.tuple _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.unary _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.ternary _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.assign _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.call _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.callWithOptions _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.newExpr _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.array _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.enumFromUInt _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.payableConversion _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01
  | L00_SourceSolidity.Expr.typeName _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileExprChecked?] at hP01

theorem compileBoolExprChecked?_p02ExprResultTy? :
    {source : L00_SourceSolidity.Expr} ->
    {p01 :
      P01_SourceSolidityToValidSolidity.CheckedBoolExpr source} ->
    {p02 :
      P02_ValidSolidityToAbstractYul.CheckedExpr p01.expr} ->
    P01_SourceSolidityToValidSolidity.compileBoolExprChecked? source =
      some p01 ->
    P02_ValidSolidityToAbstractYul.compileExprChecked? p01.expr =
      some p02 ->
      p02.expr.resultTy? = some L02_AbstractYul.Ty.bool := by
  intro source p01 p02 hP01 hP02
  cases source <;>
    simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
      at hP01
  case literal lit =>
    cases lit <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hP01
    case bool value =>
      cases hP01
      simp [P02_ValidSolidityToAbstractYul.compileExprChecked?,
        L01_ValidSolidity.Expr.bool,
        L01_ValidSolidity.Ty.bool] at hP02
      cases hP02
      rfl
  case binary op lhs rhs =>
    cases op <;>
      simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?]
        at hP01
    case lt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryLtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.lt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.ltOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.ltOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hLhsTy :
                              lhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hLhs hP02Lhs
                          have hRhsTy :
                              rhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hRhs hP02Rhs
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.ltOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          simp [L02_AbstractYul.Expr.ltOp,
                            L02_AbstractYul.Expr.resultTy?,
                            hLhsTy, hRhsTy]
    case gt =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryGtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.gt lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.gtOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.gtOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hLhsTy :
                              lhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hLhs hP02Lhs
                          have hRhsTy :
                              rhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hRhs hP02Rhs
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.gtOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          simp [L02_AbstractYul.Expr.gtOp,
                            L02_AbstractYul.Expr.resultTy?,
                            hLhsTy, hRhsTy]
    case eq =>
      cases hLhs :
          P01_SourceSolidityToValidSolidity.compileExprChecked? lhs with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
            hLhs] at hP01
      | some lhsP01 =>
          cases hRhs :
              P01_SourceSolidityToValidSolidity.compileExprChecked? rhs with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                hLhs, hRhs] at hP01
          | some rhsP01 =>
              cases hNotFolded :
                  P01_SourceSolidityToValidSolidity.sourceBinaryEqNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.eq lhs rhs) with
              | none =>
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
              | some unitValue =>
                  cases unitValue
                  simp [P01_SourceSolidityToValidSolidity.compileBoolExprChecked?,
                    hLhs, hRhs, hNotFolded] at hP01
                  cases hP01
                  cases hP02Lhs :
                      P02_ValidSolidityToAbstractYul.compileExprChecked?
                        lhsP01.expr with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileExprChecked?,
                        L01_ValidSolidity.Expr.eqOp,
                        hP02Lhs] at hP02
                  | some lhsP02 =>
                      cases hP02Rhs :
                          P02_ValidSolidityToAbstractYul.compileExprChecked?
                            rhsP01.expr with
                      | none =>
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.eqOp,
                            hP02Lhs, hP02Rhs] at hP02
                      | some rhsP02 =>
                          have hLhsTy :
                              lhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hLhs hP02Lhs
                          have hRhsTy :
                              rhsP02.expr.resultTy? =
                                some L02_AbstractYul.Ty.word :=
                            compileExprChecked?_p02ExprResultTy?
                              hRhs hP02Rhs
                          simp [
                            P02_ValidSolidityToAbstractYul.compileExprChecked?,
                            L01_ValidSolidity.Expr.eqOp,
                            hP02Lhs, hP02Rhs] at hP02
                          cases hP02
                          simp [L02_AbstractYul.Expr.eqOp,
                            L02_AbstractYul.Expr.resultTy?,
                            hLhsTy, hRhsTy]

theorem compileStmtChecked?_p03StructuralStmtTarget?_exists :
    ∀ {functions : List L00_SourceSolidity.FunctionDecl}
      {source : L00_SourceSolidity.Stmt}
      {p01 :
        P01_SourceSolidityToValidSolidity.CheckedStmt functions source}
      {p02 :
        P02_ValidSolidityToAbstractYul.CheckedStmt p01.stmt},
      P01_SourceSolidityToValidSolidity.compileStmtChecked?
          functions source =
        some p01 ->
      P02_ValidSolidityToAbstractYul.compileStmtChecked? p01.stmt =
        some p02 ->
        ∃ target,
          P03_AbstractYulToGeneratedYul.structuralStmtTarget?
              p02.stmt =
            some target
  | functions, L00_SourceSolidity.Stmt.returnValues expr?, p01, p02,
      hP01, hP02 => by
      cases expr? with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hP01
      | some expr =>
          cases hExprP01 :
              P01_SourceSolidityToValidSolidity.compileExprChecked? expr with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hExprP01] at hP01
          | some exprP01 =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hExprP01] at hP01
              cases hP01
              cases hExprP02 :
                  P02_ValidSolidityToAbstractYul.compileExprChecked?
                    exprP01.expr with
              | none =>
                  simp [
                    P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                    L01_ValidSolidity.Stmt.returnExpr, hExprP02] at hP02
              | some exprP02 =>
                  simp [
                    P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                    L01_ValidSolidity.Stmt.returnExpr, hExprP02] at hP02
                  rcases hP02 with ⟨_hResultTyP02, hP02⟩
                  cases hP02
                  rcases
                    compileExprChecked?_p03StructuralExprTarget?_exists
                      hExprP01 hExprP02 with
                    ⟨targetExpr, hTargetExpr, _hEval⟩
                  have hP02ExprTy :
                      exprP02.expr.resultTy? =
                        some L02_AbstractYul.Ty.word :=
                    compileExprChecked?_p02ExprResultTy?
                      hExprP01 hExprP02
                  have hResultTy :
                      exprP02.expr.resultTyIsWord = true := by
                    simp [L02_AbstractYul.Expr.resultTyIsWord,
                      hP02ExprTy, L02_AbstractYul.Ty.isWord]
                  exact
                    ⟨L03_GeneratedYul.Stmt.returnExpr targetExpr,
                      by
                        simp [
                          P03_AbstractYulToGeneratedYul.structuralStmtTarget?,
                          L02_AbstractYul.Stmt.returnExpr,
                          hResultTy, hTargetExpr]⟩
  | functions, L00_SourceSolidity.Stmt.block stmts, p01, p02,
      hP01, hP02 => by
      cases stmts with
      | nil =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hP01
      | cons stmt rest =>
          cases rest with
          | nil =>
              cases hStmtP01 :
                  P01_SourceSolidityToValidSolidity.compileStmtChecked?
                    functions stmt with
              | none =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hStmtP01] at hP01
              | some stmtP01 =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hStmtP01] at hP01
                  cases hP01
                  cases hStmtP02 :
                      P02_ValidSolidityToAbstractYul.compileStmtChecked?
                        stmtP01.stmt with
                  | none =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                        hStmtP02] at hP02
                  | some stmtP02 =>
                      simp [
                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                        hStmtP02] at hP02
                      cases hP02
                      rcases
                        compileStmtChecked?_p03StructuralStmtTarget?_exists
                          hStmtP01 hStmtP02 with
                        ⟨targetStmt, hTargetStmt⟩
                      exact
                        ⟨L03_GeneratedYul.Stmt.block [targetStmt],
                          by
                            simp [
                              P03_AbstractYulToGeneratedYul.structuralStmtTarget?,
                              hTargetStmt]⟩
          | cons _ _ =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
                at hP01
  | functions,
      L00_SourceSolidity.Stmt.ifElse condition thenBranch elseBranch?,
      p01, p02, hP01, hP02 => by
      cases elseBranch? with
      | none =>
          simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?]
            at hP01
      | some elseBranch =>
          cases hConditionP01 :
              P01_SourceSolidityToValidSolidity.compileBoolExprChecked?
                condition with
          | none =>
              simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                hConditionP01] at hP01
          | some conditionP01 =>
              cases hThenP01 :
                  P01_SourceSolidityToValidSolidity.compileStmtChecked?
                    functions thenBranch with
              | none =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                    hConditionP01, hThenP01] at hP01
              | some thenP01 =>
                  cases hElseP01 :
                      P01_SourceSolidityToValidSolidity.compileStmtChecked?
                        functions elseBranch with
                  | none =>
                      simp [
                        P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                        hConditionP01, hThenP01, hElseP01] at hP01
                  | some elseP01 =>
                      have hConditionEval := conditionP01.eval
                      unfold L01_ValidSolidity.Expr.Eval at hConditionEval
                      have hConditionTy :
                          conditionP01.expr.resultTyIsBool = true := by
                        simp [L01_ValidSolidity.Expr.resultTyIsBool,
                          conditionP01.resultTy,
                          L01_ValidSolidity.Ty.isBool]
                      by_cases hTruthy :
                          SolidCore.Solidity.Source.wordTruthy
                            conditionP01.value
                      · simp [
                          P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                          hConditionP01, hThenP01, hElseP01, hTruthy]
                          at hP01
                        cases hP01
                        cases hConditionP02 :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              conditionP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                              hConditionTy, hConditionP02] at hP02
                        | some conditionP02 =>
                            cases hThenP02 :
                                P02_ValidSolidityToAbstractYul.compileStmtChecked?
                                  thenP01.stmt with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                  hConditionTy, hConditionP02, hThenP02]
                                  at hP02
                            | some thenP02 =>
                                cases hElseP02 :
                                    P02_ValidSolidityToAbstractYul.compileStmtChecked?
                                      elseP01.stmt with
                                | none =>
                                    simp [
                                      P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                      hConditionTy, hConditionP02,
                                      hThenP02, hElseP02] at hP02
                                | some elseP02 =>
                                    by_cases hConditionEvalSome :
                                        conditionP01.expr.eval?.isSome =
                                          true
                                    · simp [
                                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                        hConditionTy, hConditionP02,
                                        hThenP02, hElseP02,
                                        hConditionEvalSome] at hP02
                                      cases hP02
                                      rcases
                                        compileBoolExprChecked?_p03StructuralExprTarget?_exists
                                          hConditionP01 hConditionP02 with
                                        ⟨targetCondition, hTargetCondition,
                                          _hConditionEval⟩
                                      rcases
                                        compileStmtChecked?_p03StructuralStmtTarget?_exists
                                          hThenP01 hThenP02 with
                                        ⟨targetThen, hTargetThen⟩
                                      rcases
                                        compileStmtChecked?_p03StructuralStmtTarget?_exists
                                          hElseP01 hElseP02 with
                                        ⟨targetElse, hTargetElse⟩
                                      have hConditionP02Ty :
                                          conditionP02.expr.resultTy? =
                                            some L02_AbstractYul.Ty.bool :=
                                        compileBoolExprChecked?_p02ExprResultTy?
                                          hConditionP01 hConditionP02
                                      have hConditionTyP02 :
                                          conditionP02.expr.resultTyIsBool =
                                            true := by
                                        simp [L02_AbstractYul.Expr.resultTyIsBool,
                                          hConditionP02Ty,
                                          L02_AbstractYul.Ty.isBool]
                                      have hConditionEvalP02 :
                                          conditionP02.expr.eval? =
                                            some conditionP01.value := by
                                        rw [conditionP02.eval_eq]
                                        exact hConditionEval
                                      have hCheckedStmt :
                                          (P02_ValidSolidityToAbstractYul.checkedIfElseOfEvalSome
                                            conditionP01.expr
                                            thenP01.stmt elseP01.stmt
                                            conditionP02 thenP02 elseP02
                                            hConditionEvalSome).stmt =
                                            L02_AbstractYul.Stmt.ifElse
                                              conditionP02.expr
                                              thenP02.stmt elseP02.stmt := by
                                        exact
                                          P02_ValidSolidityToAbstractYul.checkedIfElseOfEvalSome_stmt
                                            conditionP01.expr
                                            thenP01.stmt elseP01.stmt
                                            conditionP02 thenP02 elseP02
                                            hConditionEvalSome
                                      exact
                                        ⟨L03_GeneratedYul.Stmt.switch
                                            targetCondition
                                            [(0, targetElse)]
                                            (some targetThen),
                                          by
                                            simp [
                                              P03_AbstractYulToGeneratedYul.structuralStmtTarget?,
                                              hCheckedStmt,
                                              hConditionTyP02,
                                              hTargetCondition,
                                              hTargetThen, hTargetElse,
                                              hConditionEvalP02]⟩
                                    · simp [
                                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                        hConditionTy, hConditionP02,
                                        hThenP02, hElseP02,
                                        hConditionEvalSome] at hP02
                      · simp [
                          P01_SourceSolidityToValidSolidity.compileStmtChecked?,
                          hConditionP01, hThenP01, hElseP01, hTruthy]
                          at hP01
                        cases hP01
                        cases hConditionP02 :
                            P02_ValidSolidityToAbstractYul.compileExprChecked?
                              conditionP01.expr with
                        | none =>
                            simp [
                              P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                              hConditionTy, hConditionP02] at hP02
                        | some conditionP02 =>
                            cases hThenP02 :
                                P02_ValidSolidityToAbstractYul.compileStmtChecked?
                                  thenP01.stmt with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                  hConditionTy, hConditionP02, hThenP02]
                                  at hP02
                            | some thenP02 =>
                                cases hElseP02 :
                                    P02_ValidSolidityToAbstractYul.compileStmtChecked?
                                      elseP01.stmt with
                                | none =>
                                    simp [
                                      P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                      hConditionTy, hConditionP02,
                                      hThenP02, hElseP02] at hP02
                                | some elseP02 =>
                                    by_cases hConditionEvalSome :
                                        conditionP01.expr.eval?.isSome =
                                          true
                                    · simp [
                                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                        hConditionTy, hConditionP02,
                                        hThenP02, hElseP02,
                                        hConditionEvalSome] at hP02
                                      cases hP02
                                      rcases
                                        compileBoolExprChecked?_p03StructuralExprTarget?_exists
                                          hConditionP01 hConditionP02 with
                                        ⟨targetCondition, hTargetCondition,
                                          _hConditionEval⟩
                                      rcases
                                        compileStmtChecked?_p03StructuralStmtTarget?_exists
                                          hThenP01 hThenP02 with
                                        ⟨targetThen, hTargetThen⟩
                                      rcases
                                        compileStmtChecked?_p03StructuralStmtTarget?_exists
                                          hElseP01 hElseP02 with
                                        ⟨targetElse, hTargetElse⟩
                                      have hConditionP02Ty :
                                          conditionP02.expr.resultTy? =
                                            some L02_AbstractYul.Ty.bool :=
                                        compileBoolExprChecked?_p02ExprResultTy?
                                          hConditionP01 hConditionP02
                                      have hConditionTyP02 :
                                          conditionP02.expr.resultTyIsBool =
                                            true := by
                                        simp [L02_AbstractYul.Expr.resultTyIsBool,
                                          hConditionP02Ty,
                                          L02_AbstractYul.Ty.isBool]
                                      have hConditionEvalP02 :
                                          conditionP02.expr.eval? =
                                            some conditionP01.value := by
                                        rw [conditionP02.eval_eq]
                                        exact hConditionEval
                                      have hCheckedStmt :
                                          (P02_ValidSolidityToAbstractYul.checkedIfElseOfEvalSome
                                            conditionP01.expr
                                            thenP01.stmt elseP01.stmt
                                            conditionP02 thenP02 elseP02
                                            hConditionEvalSome).stmt =
                                            L02_AbstractYul.Stmt.ifElse
                                              conditionP02.expr
                                              thenP02.stmt elseP02.stmt := by
                                        exact
                                          P02_ValidSolidityToAbstractYul.checkedIfElseOfEvalSome_stmt
                                            conditionP01.expr
                                            thenP01.stmt elseP01.stmt
                                            conditionP02 thenP02 elseP02
                                            hConditionEvalSome
                                      exact
                                        ⟨L03_GeneratedYul.Stmt.switch
                                            targetCondition
                                            [(0, targetElse)]
                                            (some targetThen),
                                          by
                                            simp [
                                              P03_AbstractYulToGeneratedYul.structuralStmtTarget?,
                                              hCheckedStmt,
                                              hConditionTyP02,
                                              hTargetCondition,
                                              hTargetThen, hTargetElse,
                                              hConditionEvalP02]⟩
                                    · simp [
                                        P02_ValidSolidityToAbstractYul.compileStmtChecked?,
                                        hConditionTy, hConditionP02,
                                        hThenP02, hElseP02,
                                        hConditionEvalSome] at hP02
  | _, L00_SourceSolidity.Stmt.empty, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.varDecl _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.expr _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.whileLoop _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.doWhile _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.forLoop _ _ _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.tryCatch _ _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.tryCatchReturns _ _ _ _, _, _, hP01,
      _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.emitEvent _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.revertCall _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.break, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.continue, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.unchecked _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.inlineAssembly _, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01
  | _, L00_SourceSolidity.Stmt.modifierPlaceholder, _, _, hP01, _ => by
      simp [P01_SourceSolidityToValidSolidity.compileStmtChecked?] at hP01

theorem compileFunctionChecked?_p03StructuralEntryTarget?_exists
    {source : L00_SourceSolidity.FunctionDecl}
    {p01 :
      P01_SourceSolidityToValidSolidity.CheckedFunction source}
    {p02 :
      P02_ValidSolidityToAbstractYul.CheckedFunction p01.function}
    (hP01 :
      P01_SourceSolidityToValidSolidity.compileFunctionChecked? source =
        some p01)
    (hP02 :
      P02_ValidSolidityToAbstractYul.compileFunctionChecked?
          p01.function =
        some p02) :
    ∃ target,
      P03_AbstractYulToGeneratedYul.structuralEntryTarget?
          p02.entry =
        some target := by
  cases source with
  | mk kind name params returns visibility mutability virtualFlag overrideSpec
      modifiers body =>
      cases kind <;> try
        simp [P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
          at hP01
      case function =>
        cases name with
        | none =>
            simp [P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
              at hP01
        | some sourceName =>
            cases params with
            | cons param rest =>
                simp [
                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                  at hP01
            | nil =>
                cases returns with
                | nil =>
                    simp [
                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                      at hP01
                | cons returnParam returnRest =>
                    cases returnRest with
                    | cons returnParam' returnRest' =>
                        simp [
                          P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                          at hP01
                    | nil =>
                        cases returnParam with
                        | mk returnName returnTy returnLocation =>
                            cases returnTy <;> try
                              simp [
                                P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                at hP01
                            case uint bits =>
                              by_cases hBits : bits = 256
                              · subst bits
                                cases visibility with
                                | none =>
                                    simp [
                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                      at hP01
                                | some visibilityValue =>
                                    cases visibilityValue <;> try
                                      simp [
                                        P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                        at hP01
                                    ·
                                      cases mutability <;> try
                                        simp [
                                          P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                          at hP01
                                      ·
                                        cases modifiers with
                                        | cons modifier rest =>
                                            simp [
                                              P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                              at hP01
                                        | nil =>
                                            cases body with
                                            | none =>
                                                simp [
                                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?]
                                                  at hP01
                                            | some body =>
                                                let fn :
                                                    L00_SourceSolidity.FunctionDecl :=
                                                  { kind :=
                                                      L00_SourceSolidity.FunctionKind.function
                                                    name := some sourceName
                                                    params := []
                                                    returns :=
                                                      [{ name := returnName
                                                         ty :=
                                                          L00_SourceSolidity.Ty.uint
                                                            256
                                                         location :=
                                                          returnLocation }]
                                                    visibility :=
                                                      some
                                                        L00_SourceSolidity.Visibility.public_
                                                    mutability :=
                                                      L00_SourceSolidity.StateMutability.pure
                                                    virtual := virtualFlag
                                                    override? := overrideSpec
                                                    modifiers := []
                                                    body := some body }
                                                change
                                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?
                                                      fn =
                                                    some p01 at hP01
                                                cases hStmtP01 :
                                                    P01_SourceSolidityToValidSolidity.compileStmtChecked?
                                                      [fn] body with
                                                | none =>
                                                    simp [fn,
                                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                                      hStmtP01] at hP01
                                                | some stmtP01 =>
                                                    have hP01' := hP01
                                                    simp [fn,
                                                      P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                                      hStmtP01] at hP01'
                                                    cases hP01'
                                                    cases hStmtP02 :
                                                        P02_ValidSolidityToAbstractYul.compileStmtChecked?
                                                          stmtP01.stmt with
                                                    | none =>
                                                        simp [
                                                          P02_ValidSolidityToAbstractYul.compileFunctionChecked?,
                                                          L01_ValidSolidity.FunctionDecl.withBody,
                                                          L01_ValidSolidity.ReturnVar.isUint256,
                                                          L01_ValidSolidity.ReturnVar.word0,
                                                          L01_ValidSolidity.Ty.uint256,
                                                          hStmtP02] at hP02
                                                      | some stmtP02 =>
                                                          simp [
                                                            P02_ValidSolidityToAbstractYul.compileFunctionChecked?,
                                                            L01_ValidSolidity.FunctionDecl.withBody,
                                                            L01_ValidSolidity.ReturnVar.isUint256,
                                                            L01_ValidSolidity.ReturnVar.word0,
                                                            L01_ValidSolidity.Ty.uint256,
                                                            hStmtP02] at hP02
                                                          rcases hP02 with ⟨_hRet, hP02⟩
                                                          cases hP02
                                                          rcases
                                                            compileStmtChecked?_p03StructuralStmtTarget?_exists
                                                              hStmtP01
                                                              hStmtP02 with
                                                            ⟨targetStmt,
                                                              hTargetStmt⟩
                                                          exact
                                                            ⟨targetStmt,
                                                              by
                                                                simp [
                                                                  P03_AbstractYulToGeneratedYul.structuralEntryTarget?,
                                                                  L02_AbstractYul.Entry.withSourceBody,
                                                                  hTargetStmt]⟩
                              · simp [
                                  P01_SourceSolidityToValidSolidity.compileFunctionChecked?,
                                  hBits] at hP01

theorem compileContractChecked?_p03StructuralEntryTarget?_exists
    {source : L00_SourceSolidity.ContractDecl}
    {p01 :
      P01_SourceSolidityToValidSolidity.CheckedContract source}
    {p02 :
      P02_ValidSolidityToAbstractYul.CheckedContract p01.contract}
    (hP01 :
      P01_SourceSolidityToValidSolidity.compileContractChecked? source =
        some p01)
    (hP02 :
      P02_ValidSolidityToAbstractYul.compileContractChecked?
          p01.contract =
        some p02) :
    ∃ target,
      P03_AbstractYulToGeneratedYul.structuralEntryTarget?
          p02.entry =
        some target := by
  cases source with
  | mk kind contractName abstract bases items =>
      cases kind <;> try
        simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
          at hP01
      case contract =>
        cases abstract <;> try
          simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
            at hP01
        case false =>
          cases bases with
          | cons base rest =>
              simp [P01_SourceSolidityToValidSolidity.compileContractChecked?]
                at hP01
          | nil =>
              cases items with
              | nil =>
                  simp [
                    P01_SourceSolidityToValidSolidity.compileContractChecked?]
                    at hP01
              | cons item rest =>
                  cases rest with
                  | cons item' rest' =>
                      simp [
                        P01_SourceSolidityToValidSolidity.compileContractChecked?]
                        at hP01
                  | nil =>
                      cases item <;> try
                        simp [
                          P01_SourceSolidityToValidSolidity.compileContractChecked?]
                          at hP01
                      case function fn =>
                        let contract : L00_SourceSolidity.ContractDecl :=
                          { kind := L00_SourceSolidity.ContractKind.contract
                            name := contractName
                            abstract := false
                            bases := []
                            items :=
                              [L00_SourceSolidity.ContractItem.function fn] }
                        change
                          P01_SourceSolidityToValidSolidity.compileContractChecked?
                              contract =
                            some p01 at hP01
                        cases hFnP01 :
                            P01_SourceSolidityToValidSolidity.compileFunctionChecked?
                              fn with
                        | none =>
                            simp [contract,
                              P01_SourceSolidityToValidSolidity.compileContractChecked?,
                              hFnP01] at hP01
                        | some fnP01 =>
                            have hP01' := hP01
                            simp [contract,
                              P01_SourceSolidityToValidSolidity.compileContractChecked?,
                              hFnP01] at hP01'
                            cases hP01'
                            cases hFnP02 :
                                P02_ValidSolidityToAbstractYul.compileFunctionChecked?
                                  fnP01.function with
                            | none =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileContractChecked?,
                                  L01_ValidSolidity.ContractDecl.withFunction,
                                  hFnP02] at hP02
                            | some fnP02 =>
                                simp [
                                  P02_ValidSolidityToAbstractYul.compileContractChecked?,
                                  L01_ValidSolidity.ContractDecl.withFunction,
                                  hFnP02] at hP02
                                cases hP02
                                exact
                                  compileFunctionChecked?_p03StructuralEntryTarget?_exists
                                    hFnP01 hFnP02

theorem compileSourceChecked?_p03StructuralProgramTarget?_exists
    {source : L00_SourceSolidity.SourceUnit}
    {p01 :
      P01_SourceSolidityToValidSolidity.CheckedProgram source}
    {p02 :
      P02_ValidSolidityToAbstractYul.CheckedProgram p01.program}
    (hP01 :
      P01_SourceSolidityToValidSolidity.compileSourceChecked? source =
        some p01)
    (hP02 :
      P02_ValidSolidityToAbstractYul.compileProgramChecked?
          p01.program =
        some p02) :
    ∃ target,
      P03_AbstractYulToGeneratedYul.structuralProgramTarget?
          p02.program =
        some target := by
  cases source with
  | mk items =>
      cases items with
      | nil =>
          simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
            at hP01
      | cons item rest =>
          cases rest with
          | cons item' rest' =>
              simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
                at hP01
          | nil =>
              cases item <;> try
                simp [P01_SourceSolidityToValidSolidity.compileSourceChecked?]
                  at hP01
              case contract contract =>
                let sourceUnit : L00_SourceSolidity.SourceUnit :=
                  { items :=
                      [L00_SourceSolidity.SourceItem.contract contract] }
                change
                  P01_SourceSolidityToValidSolidity.compileSourceChecked?
                      sourceUnit =
                    some p01 at hP01
                cases hContractP01 :
                    P01_SourceSolidityToValidSolidity.compileContractChecked?
                      contract with
                | none =>
                    simp [sourceUnit,
                      P01_SourceSolidityToValidSolidity.compileSourceChecked?,
                      hContractP01] at hP01
                | some contractP01 =>
                    have hP01' := hP01
                    simp [sourceUnit,
                      P01_SourceSolidityToValidSolidity.compileSourceChecked?,
                      hContractP01] at hP01'
                    cases hP01'
                    cases hContractP02 :
                        P02_ValidSolidityToAbstractYul.compileContractChecked?
                          contractP01.contract with
                    | none =>
                        simp [
                          P02_ValidSolidityToAbstractYul.compileProgramChecked?,
                          L01_ValidSolidity.Program.withContract,
                          hContractP02] at hP02
                    | some contractP02 =>
                        simp [
                          P02_ValidSolidityToAbstractYul.compileProgramChecked?,
                          L01_ValidSolidity.Program.withContract,
                          hContractP02] at hP02
                        cases hP02
                        rcases
                          compileContractChecked?_p03StructuralEntryTarget?_exists
                            hContractP01 hContractP02 with
                          ⟨targetEntry, hTargetEntry⟩
                        exact
                          ⟨L03_GeneratedYul.Program.returnStmt targetEntry,
                            by
                              simp [
                                P03_AbstractYulToGeneratedYul.structuralProgramTarget?,
                                L02_AbstractYul.Program.withEntry,
                                hTargetEntry]⟩

theorem check?_p02Compile?_p03Accepted
    {source : L00_SourceSolidity.SourceUnit}
    {valid : P01_SourceSolidityToValidSolidity.Artifact}
    {abstractYul : P02_ValidSolidityToAbstractYul.Artifact}
    (hP01 :
      P01_SourceSolidityToValidSolidity.check? source = some valid)
    (hP02 :
      P02_ValidSolidityToAbstractYul.compile? valid.program =
        some abstractYul) :
    P03_AbstractYulToGeneratedYul.Accepted abstractYul.program := by
  classical
  by_cases hEmpty : source.items.isEmpty
  · simp [P01_SourceSolidityToValidSolidity.check?, hEmpty] at hP01
    cases hP01
    simp [P02_ValidSolidityToAbstractYul.compile?,
      L01_ValidSolidity.Program.empty] at hP02
    cases hP02
    simp [P03_AbstractYulToGeneratedYul.Accepted,
      P03_AbstractYulToGeneratedYul.accepted?,
      P03_AbstractYulToGeneratedYul.programEmptyShape?,
      L02_AbstractYul.Program.empty]
  · cases hSourceP01 :
        P01_SourceSolidityToValidSolidity.compileSourceChecked? source with
    | none =>
        simp [P01_SourceSolidityToValidSolidity.check?, hEmpty,
          hSourceP01] at hP01
    | some sourceP01 =>
        simp [P01_SourceSolidityToValidSolidity.check?, hEmpty,
          hSourceP01] at hP01
        cases hP01
        by_cases hValidEmpty :
            sourceP01.program = L01_ValidSolidity.Program.empty
        · simp [P02_ValidSolidityToAbstractYul.compile?,
            hValidEmpty] at hP02
          cases hP02
          simp [P03_AbstractYulToGeneratedYul.Accepted,
            P03_AbstractYulToGeneratedYul.accepted?,
            P03_AbstractYulToGeneratedYul.programEmptyShape?,
            L02_AbstractYul.Program.empty]
        · cases hSourceP02 :
              P02_ValidSolidityToAbstractYul.compileProgramChecked?
                sourceP01.program with
          | none =>
              simp [P02_ValidSolidityToAbstractYul.compile?,
                hValidEmpty, hSourceP02] at hP02
          | some sourceP02 =>
              simp [P02_ValidSolidityToAbstractYul.compile?,
                hValidEmpty, hSourceP02] at hP02
              cases hP02
              rcases
                compileSourceChecked?_p03StructuralProgramTarget?_exists
                  hSourceP01 hSourceP02 with
                ⟨target, hTarget⟩
              unfold P03_AbstractYulToGeneratedYul.Accepted
              unfold P03_AbstractYulToGeneratedYul.accepted?
              cases hEmptyShape :
                  P03_AbstractYulToGeneratedYul.programEmptyShape?
                    sourceP02.program
              · rw [hTarget]
                rfl
              · rfl

end P01P02ToP03

theorem yulPassSuccesses_sound
    {source : L00_SourceSolidity.SourceUnit}
    {artifacts : YulArtifacts}
    (hPasses : YulPassSuccesses source artifacts) :
    ∃ behavior, YulBoundary source artifacts behavior := by
  rcases
    Passes.P01_SourceSolidityToValidSolidity.check?_sound hPasses.p01 with
    ⟨behavior, h01⟩
  let h02 :=
    Passes.P02_ValidSolidityToAbstractYul.compile?_sound hPasses.p02
  let h03 :=
    Passes.P03_AbstractYulToGeneratedYul.compile?_sound hPasses.p03
  have hValid := h01.validSoliditySemantics
  have hAbstract := h02.preservesBehavior hValid
  have hGenerated := h03.preservesBehavior hAbstract
  exact
    ⟨behavior,
      { p01Sound := h01
        p02Sound := h02
        p03Sound := h03
        sourceSemantics := h01.sourceSemantics
        validSemantics := hValid
        abstractYulSemantics := hAbstract
        generatedYulSemantics := hGenerated }⟩

theorem yulPassSuccesses_acceptedInputs
    {source : L00_SourceSolidity.SourceUnit}
    {artifacts : YulArtifacts}
    (hPasses : YulPassSuccesses source artifacts) :
    YulAcceptedInputs source := by
  rcases
    Passes.P01_SourceSolidityToValidSolidity.check?_sound hPasses.p01 with
    ⟨_behavior, h01⟩
  exact
    { sourceAccepted := h01.sourceAccepted
      validAccepted := by
        intro valid hValid
        have hValidEq : valid = artifacts.valid := by
          rw [hPasses.p01] at hValid
          cases hValid
          rfl
        subst valid
        exact
          Passes.P02_ValidSolidityToAbstractYul.compile?_accepted
            hPasses.p02
      abstractYulAccepted := by
        intro valid abstractYul hValid hAbstractYul
        have hValidEq : valid = artifacts.valid := by
          rw [hPasses.p01] at hValid
          cases hValid
          rfl
        subst valid
        have hAbstractYulEq :
            abstractYul = artifacts.abstractYul := by
          rw [hPasses.p02] at hAbstractYul
          cases hAbstractYul
          rfl
        subst abstractYul
        exact
          Passes.P03_AbstractYulToGeneratedYul.compile?_accepted
            hPasses.p03 }

theorem compileToYul?_sound
    {source : L00_SourceSolidity.SourceUnit}
    {artifacts : YulArtifacts}
    (hCompile : compileToYul? source = some artifacts) :
    ∃ behavior, YulBoundary source artifacts behavior := by
  unfold compileToYul? at hCompile
  cases hP01 :
      Passes.P01_SourceSolidityToValidSolidity.check? source with
  | none =>
      simp [hP01] at hCompile
  | some valid =>
      cases hP02 :
          Passes.P02_ValidSolidityToAbstractYul.compile?
            valid.program with
      | none =>
          simp [hP01, hP02] at hCompile
      | some abstractYul =>
          cases hP03 :
              Passes.P03_AbstractYulToGeneratedYul.compile?
                abstractYul.program with
          | none =>
              simp [hP01, hP02, hP03] at hCompile
          | some generatedYul =>
              simp [hP01, hP02, hP03] at hCompile
              cases hCompile
              exact
                yulPassSuccesses_sound
                  { p01 := hP01
                    p02 := hP02
                    p03 := hP03 }

theorem compileToYul?_acceptedInputs
    {source : L00_SourceSolidity.SourceUnit}
    {artifacts : YulArtifacts}
    (hCompile : compileToYul? source = some artifacts) :
    YulAcceptedInputs source := by
  unfold compileToYul? at hCompile
  cases hP01 :
      Passes.P01_SourceSolidityToValidSolidity.check? source with
  | none =>
      simp [hP01] at hCompile
  | some valid =>
      cases hP02 :
          Passes.P02_ValidSolidityToAbstractYul.compile?
            valid.program with
      | none =>
          simp [hP01, hP02] at hCompile
      | some abstractYul =>
          cases hP03 :
              Passes.P03_AbstractYulToGeneratedYul.compile?
                abstractYul.program with
          | none =>
              simp [hP01, hP02, hP03] at hCompile
          | some generatedYul =>
              simp [hP01, hP02, hP03] at hCompile
              cases hCompile
              exact
                yulPassSuccesses_acceptedInputs
                  (artifacts :=
                    { valid := valid
                      abstractYul := abstractYul
                      generatedYul := generatedYul })
                  { p01 := hP01
                    p02 := hP02
                    p03 := hP03 }

theorem compileToYul?_complete_for_acceptedInputs
    {source : L00_SourceSolidity.SourceUnit}
    (hAccepted : YulAcceptedInputs source) :
    ∃ artifacts, compileToYul? source = some artifacts := by
  rcases
    Passes.P01_SourceSolidityToValidSolidity.check?_complete_for_accepted
      hAccepted.sourceAccepted with
    ⟨valid, hP01⟩
  rcases
    Passes.P02_ValidSolidityToAbstractYul.compile?_complete_for_accepted
      (hAccepted.validAccepted hP01) with
    ⟨abstractYul, hP02⟩
  rcases
    Passes.P03_AbstractYulToGeneratedYul.compile?_complete_for_accepted
      (hAccepted.abstractYulAccepted hP01 hP02) with
    ⟨generatedYul, hP03⟩
  exact
    ⟨{ valid := valid
       abstractYul := abstractYul
       generatedYul := generatedYul },
      by simp [compileToYul?, hP01, hP02, hP03]⟩

theorem compileToYul?_complete_for_sourceAccepted_and_p03Accepted
    {source : L00_SourceSolidity.SourceUnit}
    (hSource :
      Passes.P01_SourceSolidityToValidSolidity.Accepted source)
    (hP03Accepted :
      ∀ {valid : Passes.P01_SourceSolidityToValidSolidity.Artifact}
        {abstractYul :
          Passes.P02_ValidSolidityToAbstractYul.Artifact},
        Passes.P01_SourceSolidityToValidSolidity.check? source =
          some valid ->
        Passes.P02_ValidSolidityToAbstractYul.compile? valid.program =
          some abstractYul ->
        Passes.P03_AbstractYulToGeneratedYul.Accepted
          abstractYul.program) :
    ∃ artifacts, compileToYul? source = some artifacts := by
  rcases
    Passes.P01_SourceSolidityToValidSolidity.check?_complete_for_accepted
      hSource with
    ⟨valid, hP01⟩
  rcases
    Passes.P02_ValidSolidityToAbstractYul.compile?_complete_for_accepted
      (P01ToP02.check?_p02Accepted hP01) with
    ⟨abstractYul, hP02⟩
  rcases
    Passes.P03_AbstractYulToGeneratedYul.compile?_complete_for_accepted
      (hP03Accepted hP01 hP02) with
    ⟨generatedYul, hP03⟩
  exact
    ⟨{ valid := valid
       abstractYul := abstractYul
       generatedYul := generatedYul },
      by simp [compileToYul?, hP01, hP02, hP03]⟩

theorem compileToYul?_complete_for_sourceAccepted
    {source : L00_SourceSolidity.SourceUnit}
    (hSource :
      Passes.P01_SourceSolidityToValidSolidity.Accepted source) :
    ∃ artifacts, compileToYul? source = some artifacts := by
  rcases
    Passes.P01_SourceSolidityToValidSolidity.check?_complete_for_accepted
      hSource with
    ⟨valid, hP01⟩
  rcases
    Passes.P02_ValidSolidityToAbstractYul.compile?_complete_for_accepted
      (P01ToP02.check?_p02Accepted hP01) with
    ⟨abstractYul, hP02⟩
  rcases
    Passes.P03_AbstractYulToGeneratedYul.compile?_complete_for_accepted
      (P01P02ToP03.check?_p02Compile?_p03Accepted hP01 hP02) with
    ⟨generatedYul, hP03⟩
  exact
    ⟨{ valid := valid
       abstractYul := abstractYul
       generatedYul := generatedYul },
      by simp [compileToYul?, hP01, hP02, hP03]⟩

theorem compileToYul?_success_iff_acceptedInputs
    {source : L00_SourceSolidity.SourceUnit} :
    (∃ artifacts, compileToYul? source = some artifacts) ↔
      YulAcceptedInputs source := by
  constructor
  · intro hSuccess
    rcases hSuccess with ⟨artifacts, hCompile⟩
    exact compileToYul?_acceptedInputs hCompile
  · intro hAccepted
    exact compileToYul?_complete_for_acceptedInputs hAccepted

theorem compileToYul?_complete_and_sound_for_acceptedInputs
    {source : L00_SourceSolidity.SourceUnit}
    (hAccepted : YulAcceptedInputs source) :
    ∃ artifacts behavior,
      compileToYul? source = some artifacts ∧
      YulBoundary source artifacts behavior := by
  rcases compileToYul?_complete_for_acceptedInputs hAccepted with
    ⟨artifacts, hCompile⟩
  rcases compileToYul?_sound hCompile with ⟨behavior, hBoundary⟩
  exact ⟨artifacts, behavior, hCompile, hBoundary⟩

theorem compileToYul?_complete_and_sound_for_sourceAccepted
    {source : L00_SourceSolidity.SourceUnit}
    (hSource :
      Passes.P01_SourceSolidityToValidSolidity.Accepted source) :
    ∃ artifacts behavior,
      compileToYul? source = some artifacts ∧
      YulBoundary source artifacts behavior := by
  rcases compileToYul?_complete_for_sourceAccepted hSource with
    ⟨artifacts, hCompile⟩
  rcases compileToYul?_sound hCompile with ⟨behavior, hBoundary⟩
  exact ⟨artifacts, behavior, hCompile, hBoundary⟩

end PublicClaims
end Spine
end SolidCore

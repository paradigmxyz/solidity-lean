import SolidCore.MVP

namespace SolidCore
namespace Solidity
namespace MVP
namespace EmittedFullYul

abbrev Builtin := SolidCoreYulCore.Evm.Builtin
abbrev Value := SolidCoreYulCore.FullYul.Value

inductive ExprBuiltin : Builtin -> Prop where
  | add : ExprBuiltin SolidCoreYulCore.Evm.Builtin.add
  | addmodOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.addmodOp
  | andOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.andOp
  | byteOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.byteOp
  | divOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.divOp
  | eqOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.eqOp
  | expOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.expOp
  | gtOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.gtOp
  | iszero : ExprBuiltin SolidCoreYulCore.Evm.Builtin.iszero
  | ltOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.ltOp
  | modOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.modOp
  | mul : ExprBuiltin SolidCoreYulCore.Evm.Builtin.mul
  | mulmodOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.mulmodOp
  | notOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.notOp
  | orOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.orOp
  | sarOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sarOp
  | sdivOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sdivOp
  | sgtOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sgtOp
  | shlOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.shlOp
  | shrOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.shrOp
  | sload : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sload
  | sltOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sltOp
  | smodOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.smodOp
  | sub : ExprBuiltin SolidCoreYulCore.Evm.Builtin.sub
  | xorOp : ExprBuiltin SolidCoreYulCore.Evm.Builtin.xorOp

mutual
  inductive ExprShape : YulExpr -> Prop where
    | word (value : Word) :
        ExprShape
          (SolidCoreYulCore.FullYul.Expr.value
            (SolidCoreYulCore.FullYul.Value.word value))
    | localVar :
        ExprShape (SolidCoreYulCore.FullYul.Expr.var localName)
    | builtin {builtin : Builtin} {args : List YulExpr} :
        ExprBuiltin builtin ->
        ExprsShape args ->
        ExprShape (SolidCoreYulCore.FullYul.Expr.builtin builtin args)

  inductive ExprsShape : List YulExpr -> Prop where
    | nil : ExprsShape []
    | cons {expr : YulExpr} {rest : List YulExpr} :
        ExprShape expr ->
        ExprsShape rest ->
        ExprsShape (expr :: rest)
end

theorem ExprsShape.one {expr : YulExpr}
    (hExpr : ExprShape expr) : ExprsShape [expr] :=
  ExprsShape.cons hExpr ExprsShape.nil

theorem ExprsShape.two {lhs rhs : YulExpr}
    (hLhs : ExprShape lhs) (hRhs : ExprShape rhs) :
    ExprsShape [lhs, rhs] :=
  ExprsShape.cons hLhs (ExprsShape.cons hRhs ExprsShape.nil)

theorem ExprsShape.three {first second third : YulExpr}
    (hFirst : ExprShape first) (hSecond : ExprShape second)
    (hThird : ExprShape third) :
    ExprsShape [first, second, third] :=
  ExprsShape.cons hFirst
    (ExprsShape.cons hSecond (ExprsShape.cons hThird ExprsShape.nil))

mutual
  inductive StmtShape : YulStmt -> Prop where
    | skip : StmtShape SolidCoreYulCore.FullYul.Stmt.skip
    | exprSstore {slot value : YulExpr} :
        ExprShape slot ->
        ExprShape value ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.expr
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.sstore [slot, value]))
    | exprRevert :
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.expr
            (SolidCoreYulCore.FullYul.Expr.builtin
              SolidCoreYulCore.Evm.Builtin.revertOp
              [ SolidCoreYulCore.FullYul.Expr.value
                  (SolidCoreYulCore.FullYul.Value.word 0)
              , SolidCoreYulCore.FullYul.Expr.value
                  (SolidCoreYulCore.FullYul.Value.word 0) ]))
    | letLocalSome {init : YulExpr} :
        ExprShape init ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.let1 localName (some init))
    | assignResult {expr : YulExpr} :
        ExprShape expr ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.assign returnName expr)
    | assignLocal {expr : YulExpr} :
        ExprShape expr ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.assign localName expr)
    | seq {first second : YulStmt} :
        StmtShape first ->
        StmtShape second ->
        StmtShape (SolidCoreYulCore.FullYul.Stmt.seq first second)
    | block {stmts : List YulStmt} :
        BlockShape stmts ->
        StmtShape (SolidCoreYulCore.FullYul.Stmt.block stmts)
    | ifThen {cond : YulExpr} {body : YulStmt} :
        ExprShape cond ->
        StmtShape body ->
        StmtShape (SolidCoreYulCore.FullYul.Stmt.ifThen cond body)
    | switch {discr : YulExpr} {cases : List (Value × YulStmt)}
        {defaultBranch : Option YulStmt} :
        ExprShape discr ->
        SwitchCasesShape cases ->
        OptionalStmtShape defaultBranch ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.switch discr cases defaultBranch)
    | forLoop {cond : YulExpr} {body : YulStmt} :
        ExprShape cond ->
        StmtShape body ->
        StmtShape
          (SolidCoreYulCore.FullYul.Stmt.forLoop
            SolidCoreYulCore.FullYul.Stmt.skip
            cond
            SolidCoreYulCore.FullYul.Stmt.skip
            body)
    | break : StmtShape SolidCoreYulCore.FullYul.Stmt.break
    | leave : StmtShape SolidCoreYulCore.FullYul.Stmt.leave

  inductive BlockShape : List YulStmt -> Prop where
    | nil : BlockShape []
    | cons {stmt : YulStmt} {rest : List YulStmt} :
        StmtShape stmt ->
        BlockShape rest ->
        BlockShape (stmt :: rest)

  inductive SwitchCasesShape : List (Value × YulStmt) -> Prop where
    | nil : SwitchCasesShape []
    | cons {label : Word} {branch : YulStmt}
        {rest : List (Value × YulStmt)} :
        StmtShape branch ->
        SwitchCasesShape rest ->
        SwitchCasesShape
          ((SolidCoreYulCore.FullYul.Value.word label, branch) :: rest)

  inductive OptionalStmtShape : Option YulStmt -> Prop where
    | none : OptionalStmtShape none
    | some {stmt : YulStmt} :
        StmtShape stmt ->
        OptionalStmtShape (some stmt)
end

theorem Expr.toFullYul_shape : (expr : Solidity.Expr) ->
    ExprShape expr.toFullYul
  | Solidity.Expr.lit value =>
      ExprShape.word (SolidCoreYulCore.norm value)
  | Solidity.Expr.neg expr =>
      ExprShape.builtin ExprBuiltin.sub
        (ExprsShape.two (ExprShape.word 0) (Expr.toFullYul_shape expr))
  | Solidity.Expr.add lhs rhs =>
      ExprShape.builtin ExprBuiltin.add
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.sub lhs rhs =>
      ExprShape.builtin ExprBuiltin.sub
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.mul lhs rhs =>
      ExprShape.builtin ExprBuiltin.mul
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.exp lhs rhs =>
      ExprShape.builtin ExprBuiltin.expOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.div lhs rhs =>
      ExprShape.builtin ExprBuiltin.divOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.mod lhs rhs =>
      ExprShape.builtin ExprBuiltin.modOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.signedDiv lhs rhs =>
      ExprShape.builtin ExprBuiltin.sdivOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.signedMod lhs rhs =>
      ExprShape.builtin ExprBuiltin.smodOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.addmod lhs rhs modulus =>
      ExprShape.builtin ExprBuiltin.addmodOp
        (ExprsShape.three (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs) (Expr.toFullYul_shape modulus))
  | Solidity.Expr.mulmod lhs rhs modulus =>
      ExprShape.builtin ExprBuiltin.mulmodOp
        (ExprsShape.three (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs) (Expr.toFullYul_shape modulus))
  | Solidity.Expr.bitAnd lhs rhs =>
      ExprShape.builtin ExprBuiltin.andOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.bitOr lhs rhs =>
      ExprShape.builtin ExprBuiltin.orOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.bitXor lhs rhs =>
      ExprShape.builtin ExprBuiltin.xorOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.bitNot expr =>
      ExprShape.builtin ExprBuiltin.notOp
        (ExprsShape.one (Expr.toFullYul_shape expr))
  | Solidity.Expr.shl value shift =>
      ExprShape.builtin ExprBuiltin.shlOp
        (ExprsShape.two (Expr.toFullYul_shape shift)
          (Expr.toFullYul_shape value))
  | Solidity.Expr.shr value shift =>
      ExprShape.builtin ExprBuiltin.shrOp
        (ExprsShape.two (Expr.toFullYul_shape shift)
          (Expr.toFullYul_shape value))
  | Solidity.Expr.sar value shift =>
      ExprShape.builtin ExprBuiltin.sarOp
        (ExprsShape.two (Expr.toFullYul_shape shift)
          (Expr.toFullYul_shape value))
  | Solidity.Expr.byteAt index value =>
      ExprShape.builtin ExprBuiltin.byteOp
        (ExprsShape.two (Expr.toFullYul_shape index)
          (Expr.toFullYul_shape value))
  | Solidity.Expr.iszero expr =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one (Expr.toFullYul_shape expr))
  | Solidity.Expr.boolAnd lhs rhs =>
      let lhsZero :=
        ExprShape.builtin ExprBuiltin.iszero
          (ExprsShape.one (Expr.toFullYul_shape lhs))
      let rhsZero :=
        ExprShape.builtin ExprBuiltin.iszero
          (ExprsShape.one (Expr.toFullYul_shape rhs))
      let orShape :=
        ExprShape.builtin ExprBuiltin.orOp
          (ExprsShape.two lhsZero rhsZero)
      ExprShape.builtin ExprBuiltin.iszero (ExprsShape.one orShape)
  | Solidity.Expr.boolOr lhs rhs =>
      let lhsZero :=
        ExprShape.builtin ExprBuiltin.iszero
          (ExprsShape.one (Expr.toFullYul_shape lhs))
      let rhsZero :=
        ExprShape.builtin ExprBuiltin.iszero
          (ExprsShape.one (Expr.toFullYul_shape rhs))
      let andShape :=
        ExprShape.builtin ExprBuiltin.andOp
          (ExprsShape.two lhsZero rhsZero)
      ExprShape.builtin ExprBuiltin.iszero (ExprsShape.one andShape)
  | Solidity.Expr.eq lhs rhs =>
      ExprShape.builtin ExprBuiltin.eqOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.ne lhs rhs =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one
          (ExprShape.builtin ExprBuiltin.eqOp
            (ExprsShape.two (Expr.toFullYul_shape lhs)
              (Expr.toFullYul_shape rhs))))
  | Solidity.Expr.lt lhs rhs =>
      ExprShape.builtin ExprBuiltin.ltOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.gt lhs rhs =>
      ExprShape.builtin ExprBuiltin.gtOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.le lhs rhs =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one
          (ExprShape.builtin ExprBuiltin.gtOp
            (ExprsShape.two (Expr.toFullYul_shape lhs)
              (Expr.toFullYul_shape rhs))))
  | Solidity.Expr.ge lhs rhs =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one
          (ExprShape.builtin ExprBuiltin.ltOp
            (ExprsShape.two (Expr.toFullYul_shape lhs)
              (Expr.toFullYul_shape rhs))))
  | Solidity.Expr.signedLt lhs rhs =>
      ExprShape.builtin ExprBuiltin.sltOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.signedGt lhs rhs =>
      ExprShape.builtin ExprBuiltin.sgtOp
        (ExprsShape.two (Expr.toFullYul_shape lhs)
          (Expr.toFullYul_shape rhs))
  | Solidity.Expr.signedLe lhs rhs =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one
          (ExprShape.builtin ExprBuiltin.sgtOp
            (ExprsShape.two (Expr.toFullYul_shape lhs)
              (Expr.toFullYul_shape rhs))))
  | Solidity.Expr.signedGe lhs rhs =>
      ExprShape.builtin ExprBuiltin.iszero
        (ExprsShape.one
          (ExprShape.builtin ExprBuiltin.sltOp
            (ExprsShape.two (Expr.toFullYul_shape lhs)
              (Expr.toFullYul_shape rhs))))

theorem StateExpr.toFullYul_shape (expr : StateExpr) :
    ExprShape expr.toFullYul := by
  induction expr with
  | pure expr =>
      exact Expr.toFullYul_shape expr
  | load slot =>
      exact
        ExprShape.builtin ExprBuiltin.sload
          (ExprsShape.one (Expr.toFullYul_shape slot))
  | add lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.add (ExprsShape.two lhs_ih rhs_ih)
  | sub lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.sub (ExprsShape.two lhs_ih rhs_ih)
  | mul lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.mul (ExprsShape.two lhs_ih rhs_ih)
  | eq lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.eqOp (ExprsShape.two lhs_ih rhs_ih)
  | lt lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.ltOp (ExprsShape.two lhs_ih rhs_ih)
  | gt lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.gtOp (ExprsShape.two lhs_ih rhs_ih)
  | bitAnd lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.andOp (ExprsShape.two lhs_ih rhs_ih)
  | bitOr lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.orOp (ExprsShape.two lhs_ih rhs_ih)
  | bitXor lhs rhs lhs_ih rhs_ih =>
      exact ExprShape.builtin ExprBuiltin.xorOp (ExprsShape.two lhs_ih rhs_ih)
  | bitNot expr expr_ih =>
      exact ExprShape.builtin ExprBuiltin.notOp (ExprsShape.one expr_ih)
  | iszero expr expr_ih =>
      exact ExprShape.builtin ExprBuiltin.iszero (ExprsShape.one expr_ih)

theorem Stmt.localFrameFullYul_shape
    (init : Solidity.Expr) {tail : YulStmt}
    (hTail : StmtShape tail) :
    StmtShape (Stmt.localFrameFullYul init tail) := by
  exact
    StmtShape.block
      (BlockShape.cons
        (StmtShape.seq
          (StmtShape.letLocalSome (Expr.toFullYul_shape init))
          hTail)
        BlockShape.nil)

theorem Stmt.toFullYul_shape (stmt : Stmt) :
    StmtShape stmt.toFullYul := by
  induction stmt with
  | skip =>
      exact StmtShape.skip
  | discard _ =>
      exact StmtShape.skip
  | returnExpr expr =>
      exact
        StmtShape.seq
          (StmtShape.assignResult (Expr.toFullYul_shape expr))
          StmtShape.leave
  | returnStateExpr expr =>
      exact
        StmtShape.seq
          (StmtShape.assignResult (StateExpr.toFullYul_shape expr))
          StmtShape.leave
  | revert =>
      exact StmtShape.exprRevert
  | store slot value =>
      exact
        StmtShape.exprSstore
          (Expr.toFullYul_shape slot)
          (Expr.toFullYul_shape value)
  | storeStateExpr slot value =>
      exact
        StmtShape.exprSstore
          (Expr.toFullYul_shape slot)
          (StateExpr.toFullYul_shape value)
  | loadReturn slot =>
      exact
        StmtShape.seq
          (StmtShape.assignResult
            (ExprShape.builtin ExprBuiltin.sload
              (ExprsShape.one (Expr.toFullYul_shape slot))))
          StmtShape.leave
  | storeThenIfLoad slot value _ body_ih =>
      exact
        StmtShape.seq
          (StmtShape.exprSstore
            (Expr.toFullYul_shape slot)
            (Expr.toFullYul_shape value))
          (StmtShape.ifThen
            (ExprShape.builtin ExprBuiltin.sload
              (ExprsShape.one (Expr.toFullYul_shape slot)))
            body_ih)
  | seq _ _ first_ih second_ih =>
      simp [Stmt.toFullYul]
      exact StmtShape.seq first_ih second_ih
  | ifThen cond _ body_ih =>
      simp [Stmt.toFullYul]
      exact StmtShape.ifThen (Expr.toFullYul_shape cond) body_ih
  | switch1 discr label _ _ branch_ih default_ih =>
      simp [Stmt.toFullYul]
      exact
        StmtShape.switch
          (Expr.toFullYul_shape discr)
          (SwitchCasesShape.cons (label := SolidCoreYulCore.norm label)
            branch_ih SwitchCasesShape.nil)
          (OptionalStmtShape.some default_ih)
  | switch2 discr firstLabel _ secondLabel _ _ _
      first_ih second_ih default_ih =>
      simp [Stmt.toFullYul]
      exact
        StmtShape.switch
          (Expr.toFullYul_shape discr)
          (SwitchCasesShape.cons
            (label := SolidCoreYulCore.norm firstLabel)
            first_ih
            (SwitchCasesShape.cons
              (label := SolidCoreYulCore.norm secondLabel)
              second_ih SwitchCasesShape.nil))
          (OptionalStmtShape.some default_ih)
  | forFalse _ body_ih =>
      simp [Stmt.toFullYul]
      exact StmtShape.forLoop (ExprShape.word 0) body_ih
  | forOnce _ body_ih =>
      simp [Stmt.toFullYul, Stmt.singleIterationLoopFullYul,
        Stmt.bodyThenBreakFullYul]
      exact
        StmtShape.forLoop (ExprShape.word 1)
          (StmtShape.seq body_ih StmtShape.break)
  | forIf cond _ body_ih =>
      simp [Stmt.toFullYul, Stmt.singleIterationLoopFullYul,
        Stmt.bodyThenBreakFullYul]
      exact
        StmtShape.forLoop (Expr.toFullYul_shape cond)
          (StmtShape.seq body_ih StmtShape.break)

theorem compileStmt_shape (source : Stmt) :
    StmtShape (compileStmt source) := by
  exact Stmt.toFullYul_shape source

theorem compileStmtArtifact_shape (source : Stmt) :
    StmtShape (compileStmtArtifact source).stmt := by
  exact compileStmt_shape source

theorem compileSourceProgramStmt_shape (source : SourceProgram) :
    StmtShape (compileSourceProgramStmt source) := by
  exact compileStmt_shape source.body

theorem compileSourceProgramArtifact_shape (source : SourceProgram) :
    StmtShape (compileSourceProgramArtifact source).stmtArtifact.stmt := by
  exact compileStmtArtifact_shape source.body

theorem SurfaceStmt.toCoreStmt_shape (source : SurfaceStmt) :
    StmtShape source.toCoreStmt.toFullYul := by
  exact Stmt.toFullYul_shape source.toCoreStmt

theorem compileSurfaceProgramStmt_shape (source : SurfaceProgram) :
    StmtShape (compileSurfaceProgramStmt source) := by
  exact compileSourceProgramStmt_shape source.toSourceProgram

theorem compileSurfaceProgramArtifact_shape (source : SurfaceProgram) :
    StmtShape
      (compileSurfaceProgramArtifact source).sourceArtifact.stmtArtifact.stmt := by
  exact compileSourceProgramArtifact_shape source.toSourceProgram

theorem SurfaceProgramCertificate.stmt_shape
    (cert : SurfaceProgramCertificate) :
    StmtShape cert.stmt := by
  rw [cert.stmt_eq]
  exact compileSurfaceProgramStmt_shape cert.source

theorem compileSurfaceProgramCertificate_shape (source : SurfaceProgram) :
    StmtShape (compileSurfaceProgramCertificate source).stmt := by
  exact SurfaceProgramCertificate.stmt_shape
    (compileSurfaceProgramCertificate source)

theorem SurfaceSourceCertificate.stmt_shape
    (cert : SurfaceSourceCertificate) :
    StmtShape cert.programCert.stmt := by
  exact SurfaceProgramCertificate.stmt_shape cert.programCert

theorem compileSurfaceSourceCertificate?_shape
    {sourceText : String} {cert : SurfaceSourceCertificate}
    (_hCompile :
      compileSurfaceSourceCertificate? sourceText = some cert) :
    StmtShape cert.programCert.stmt := by
  exact SurfaceSourceCertificate.stmt_shape cert

theorem compileSurfaceSourceStmt?_shape
    {sourceText : String} {stmt : YulStmt}
    (hCompile : compileSurfaceSourceStmt? sourceText = some stmt) :
    StmtShape stmt := by
  rcases compileSurfaceSourceStmt?_verified_certificate hCompile with
    ⟨cert, _hCert, hStmt, _hVerified⟩
  rw [← hStmt]
  exact SurfaceSourceCertificate.stmt_shape cert

theorem compileSurfaceSourceStmt?_sound_flat_with_shape
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
      StmtShape stmt ∧
      SurfaceSourceCertificate.VerifiedForText sourceText cert := by
  rcases compileSurfaceSourceStmt?_sound_flat hCompile state with
    ⟨cert, hCert, hStmt, hDynamic, hStatic, hAccepted, hVerified⟩
  refine ⟨cert, hCert, hStmt, hDynamic, hStatic, hAccepted, ?_, hVerified⟩
  exact compileSurfaceSourceStmt?_shape hCompile

end EmittedFullYul
end MVP
end Solidity
end SolidCore

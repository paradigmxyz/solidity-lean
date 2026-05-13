import SharedSemantics.Word
import SolidCore.Spine.Passes.P01_SourceSolidityToValidSolidity.TypeCheck

set_option maxHeartbeats 1000000

namespace SolidCore
namespace Spine
namespace Passes
namespace P01_SourceSolidityToValidSolidity

structure Artifact where
  program : L01_ValidSolidity.Program
  wf : L01_ValidSolidity.WF program

def isUint256? : L00_SourceSolidity.Ty -> Bool
  | L00_SourceSolidity.Ty.uint bits => bits == 256
  | _ => false

abbrev CoreExpr := L00_SourceSolidity.Executable.CoreExpr
abbrev CoreStmt := L00_SourceSolidity.Executable.CoreStmt
abbrev CoreContext := L00_SourceSolidity.Executable.CoreContext
abbrev CoreRuntime := L00_SourceSolidity.Executable.CoreRuntime
abbrev CoreState := L00_SourceSolidity.Executable.CoreState
abbrev CoreValue := L00_SourceSolidity.Executable.CoreValue
abbrev CoreResult := L00_SourceSolidity.Executable.CoreResult
abbrev CoreCallResult := L00_SourceSolidity.Executable.CoreCallResult

@[simp] theorem exceptOk_bind {ε α β : Type u}
    (value : α) (k : α -> Except ε β) :
    (Except.ok value >>= k) = k value := rfl

def sourceBinaryAddNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
  | none =>
      match L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
      | none => some ()
      | some _ => none
  | some _ => none

def sourceBinaryMulNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

def sourceBinarySubNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

def sourceBinaryEqNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

def sourceBinaryLtNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

def sourceBinaryGtNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

def sourceBinaryBitAndNotFolded? (source : L00_SourceSolidity.Expr) :
    Option Unit :=
  sourceBinaryAddNotFolded? source

theorem sourceBinaryAddNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryAddNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none := by
  intro h
  cases hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
  | none => rfl
  | some _ =>
      simp [sourceBinaryAddNotFolded?, hRat] at h

theorem sourceBinaryAddNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryAddNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none := by
  intro h
  cases hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
  | some _ =>
      simp [sourceBinaryAddNotFolded?, hRat] at h
  | none =>
      cases hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
      | none => rfl
      | some _ =>
          simp [sourceBinaryAddNotFolded?, hRat, hBool] at h

theorem sourceBinaryMulNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryMulNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinaryMulNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryMulNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem sourceBinarySubNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinarySubNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinarySubNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinarySubNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem sourceBinaryEqNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryEqNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinaryEqNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryEqNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem sourceBinaryLtNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryLtNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinaryLtNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryLtNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem sourceBinaryGtNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryGtNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinaryGtNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryGtNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem sourceBinaryBitAndNotFolded?_rat_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryBitAndNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
  sourceBinaryAddNotFolded?_rat_none

theorem sourceBinaryBitAndNotFolded?_bool_none
    {source : L00_SourceSolidity.Expr} :
    sourceBinaryBitAndNotFolded? source = some () ->
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
  sourceBinaryAddNotFolded?_bool_none

theorem binaryEq_numberLiteralRat?_none
    {lhs rhs : L00_SourceSolidity.Expr} :
    L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) = none := by
  cases hLhs :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? lhs with
  | none =>
      simp [L00_SourceSolidity.Executable.Expr.numberLiteralRat?, hLhs]
  | some lhsValue =>
      cases hRhs :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? rhs with
      | none =>
          simp [L00_SourceSolidity.Executable.Expr.numberLiteralRat?,
            hLhs, hRhs]
      | some rhsValue =>
          simp [L00_SourceSolidity.Executable.Expr.numberLiteralRat?,
            L00_SourceSolidity.Executable.BinaryOp.applyNumberRat?,
            hLhs, hRhs]

theorem boolWord_wordEq_eqWord (lhs rhs : L01_ValidSolidity.Word) :
    SolidCore.Solidity.Source.boolWord
        (SolidCore.Solidity.Source.wordEq lhs rhs) =
      SharedSemantics.eqWord lhs rhs := by
  unfold SolidCore.Solidity.Source.boolWord
  unfold SolidCore.Solidity.Source.wordEq
  unfold SharedSemantics.eqWord
  by_cases h : SharedSemantics.norm lhs = SharedSemantics.norm rhs
  · simp [h]
  · simp [h]

theorem norm_eqWord (lhs rhs : L01_ValidSolidity.Word) :
    SharedSemantics.norm (SharedSemantics.eqWord lhs rhs) =
      SharedSemantics.eqWord lhs rhs := by
  unfold SharedSemantics.eqWord
  unfold SharedSemantics.norm
  split <;> simp [SharedSemantics.wordModulus]

theorem norm_ltWord (lhs rhs : L01_ValidSolidity.Word) :
    SharedSemantics.norm (SharedSemantics.ltWord lhs rhs) =
      SharedSemantics.ltWord lhs rhs := by
  unfold SharedSemantics.ltWord
  unfold SharedSemantics.norm
  split <;> simp [SharedSemantics.wordModulus]

theorem norm_gtWord (lhs rhs : L01_ValidSolidity.Word) :
    SharedSemantics.norm (SharedSemantics.gtWord lhs rhs) =
      SharedSemantics.gtWord lhs rhs := by
  unfold SharedSemantics.gtWord
  unfold SharedSemantics.norm
  split <;> simp [SharedSemantics.wordModulus]

theorem norm_andWord (lhs rhs : L01_ValidSolidity.Word) :
    SharedSemantics.norm (SharedSemantics.andWord lhs rhs) =
      SharedSemantics.andWord lhs rhs := by
  simp [SharedSemantics.andWord, SharedSemantics.norm_norm]

@[simp] theorem tyResolveUserTypesFuel_uint
    (fuel : Nat) (env : L00_SourceSolidity.Executable.UserTypeEnv)
    (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveUserTypesFuel fuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  cases fuel <;>
    simp [L00_SourceSolidity.Executable.Ty.resolveUserTypesFuel]

@[simp] theorem tyResolveUserTypes_uint
    (env : L00_SourceSolidity.Executable.UserTypeEnv) (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveUserTypes env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  change
    L00_SourceSolidity.Executable.Ty.resolveUserTypesFuel
        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits
  exact tyResolveUserTypesFuel_uint
    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env bits

@[simp] theorem tyResolveEnumsFuel_uint
    (fuel : Nat) (env : L00_SourceSolidity.Executable.EnumEnv)
    (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveEnumsFuel fuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  cases fuel <;>
    simp [L00_SourceSolidity.Executable.Ty.resolveEnumsFuel]

@[simp] theorem tyResolveEnums_uint
    (env : L00_SourceSolidity.Executable.EnumEnv) (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveEnums env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  change
    L00_SourceSolidity.Executable.Ty.resolveEnumsFuel
        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits
  exact tyResolveEnumsFuel_uint
    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env bits

@[simp] theorem tyResolveStructsFuel_uint
    (fuel : Nat) (env : L00_SourceSolidity.Executable.StructEnv)
    (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveStructsFuel fuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  cases fuel <;>
    simp [L00_SourceSolidity.Executable.Ty.resolveStructsFuel]

@[simp] theorem tyResolveStructs_uint
    (env : L00_SourceSolidity.Executable.StructEnv) (bits : Nat) :
    L00_SourceSolidity.Executable.Ty.resolveStructs env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits := by
  change
    L00_SourceSolidity.Executable.Ty.resolveStructsFuel
        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
        (L00_SourceSolidity.Ty.uint bits) =
      L00_SourceSolidity.Ty.uint bits
  exact tyResolveStructsFuel_uint
    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env bits

structure CheckedExprWithTy
    (source : L00_SourceSolidity.Expr)
    (expectedTy : L01_ValidSolidity.Ty) where
  expr : L01_ValidSolidity.Expr
  resultTy : expr.resultTy = expectedTy
  value : L01_ValidSolidity.Word
  valueNorm : SharedSemantics.norm value = value
  eval : expr.Eval value
  -- Source elaboration may fold constructs that remain structural in L01.
  core : CoreExpr
  sourceCore :
    L00_SourceSolidity.Executable.Expr.toCore? [] source = some core
  sourceInlineConstantsFuel :
    ∀ fuel,
      L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
          fuel [] source = source
  sourceInlineConstants :
    L00_SourceSolidity.Executable.Expr.inlineConstants [] source = source
  sourceRewriteSuperCallsFuel :
    ∀ contractName fuel,
      L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
          contractName fuel source = source
  sourceRewriteSuperCalls :
    ∀ contractName,
      L00_SourceSolidity.Executable.Expr.rewriteSuperCalls
          contractName source = source
  sourceRewriteBaseCallsFuel :
    ∀ baseNames fuel,
      L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
          baseNames fuel source = source
  sourceRewriteBaseCalls :
    ∀ baseNames,
      L00_SourceSolidity.Executable.Expr.rewriteBaseCalls baseNames source =
        source
  sourceAnnotatedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.annotateAbiFuel
          fuel env source = source
  sourceAnnotated :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.annotateAbi env source = source
  sourceResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
          fuel env source =
        source
  sourceResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.resolveUserTypes env source =
        source
  sourceEnumsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel fuel env source =
        source
  sourceEnumsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.resolveEnums env source =
        source
  sourceStructsResolvedFuel :
    ∀ fuel env typeEnv,
      L00_SourceSolidity.Executable.Expr.resolveStructsFuel
          fuel env typeEnv source =
        source
  sourceStructsResolved :
    ∀ env typeEnv,
      L00_SourceSolidity.Executable.Expr.resolveStructs env typeEnv source =
        source
  sourceSelectorsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
          fuel env source =
        source
  sourceSelectorsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.resolveSelectors env source =
        source
  sourceFunctionAddressesResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
          fuel env source =
        source
  sourceFunctionAddressesResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.resolveFunctionAddresses env source =
        source
  sourceInterfaceIdsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
          fuel env source =
        source
  sourceInterfaceIdsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Expr.resolveInterfaceIds env source =
        source
  returnCoreWithInternalCalls :
    ∀ env functions returnTys,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv := [])
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := functions)
          (freeFunctions := [])
          (returnTys := returnTys)
          (stmt := L00_SourceSolidity.Stmt.returnValues (some source)) =
        some (SolidCore.Solidity.Source.Stmt.returnValues [core])
  -- Target core is tracked separately so P01 stays relational, not syntactic.
  targetCoreExpr : CoreExpr
  targetCore : expr.toCore? = some targetCoreExpr
  targetValueEval :
    SolidCore.Solidity.Source.Expr.eval
        SolidCore.Solidity.Source.Context.empty
        (SolidCore.Solidity.Source.Runtime.ofState
          SolidCore.Solidity.Source.State.empty)
        targetCoreExpr =
      Except.ok (SolidCore.Solidity.Source.Value.word value)
  sourceValueEvalChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.eval
            context runtime core =
          Except.ok (SolidCore.Solidity.Source.Value.word value)
  sourceValueEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.eval
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok (SolidCore.Solidity.Source.Value.word value)
  sourceValueEvalWithRuntimeChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.evalWithRuntime
            context runtime core =
          Except.ok (SolidCore.Solidity.Source.Value.word value, runtime)
  sourceValueEvalWithRuntime :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.evalWithRuntime
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok (SolidCore.Solidity.Source.Value.word value, runtime)

abbrev CheckedExpr (source : L00_SourceSolidity.Expr) :=
  CheckedExprWithTy source L01_ValidSolidity.Ty.uint256

abbrev CheckedBoolExpr (source : L00_SourceSolidity.Expr) :=
  CheckedExprWithTy source L01_ValidSolidity.Ty.bool

theorem literalNumber_sourceCore
    {raw : String}
    (hParse :
      L00_SourceSolidity.Executable.parseNumberNat? raw =
        some (L00_SourceSolidity.Executable.parseDecimalNat raw)) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number raw)) =
      some
        (SolidCore.Solidity.Source.Expr.word
          (L00_SourceSolidity.Executable.parseDecimalNat raw)) := by
  simp [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.Literal.toCoreExpr?, hParse]

theorem literalNumber_returnCoreWithInternalCalls
    {raw : String}
    (hParse :
      L00_SourceSolidity.Executable.parseNumberNat? raw =
        some (L00_SourceSolidity.Executable.parseDecimalNat raw))
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.number raw)))) =
      some
        (SolidCore.Solidity.Source.Stmt.returnValues
          [SolidCore.Solidity.Source.Expr.word
            (L00_SourceSolidity.Executable.parseDecimalNat raw)]) := by
  simp [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.Literal.toCoreExpr?, hParse]

theorem literalBool_sourceCore
    {value : Bool} :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.bool value)) =
      some
        (SolidCore.Solidity.Source.Expr.word
          (SolidCore.Solidity.Source.boolWord value)) := by
  simp [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.Literal.toCoreExpr?]

theorem literalBool_returnCoreWithInternalCalls
    {value : Bool} (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.bool value)))) =
      some
        (SolidCore.Solidity.Source.Stmt.returnValues
          [SolidCore.Solidity.Source.Expr.word
            (SolidCore.Solidity.Source.boolWord value)]) := by
  simp [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.Literal.toCoreExpr?]

theorem binaryAdd_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.add lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryAdd_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.add lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.add lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binarySub_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.sub lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binarySub_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.sub lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.sub lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryMul_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.mul lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryMul_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.mul lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.mul lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryEq_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.eq lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryLt_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.lt lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryGt_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.gt lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryBitAnd_sourceCore
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) = none) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) =
  some
    (SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.bitAnd lhsCore rhsCore) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryEq_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.eq lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.eq lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryLt_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.lt lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.lt lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryGt_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.gt lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.gt lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryBitAnd_returnCoreWithInternalCalls
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsCore rhsCore : SolidCore.Solidity.Source.Expr}
    (hLhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] lhs = some lhsCore)
    (hRhs :
      L00_SourceSolidity.Executable.Expr.toCore? [] rhs = some rhsCore)
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) = none)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.bitAnd lhs rhs))) =
  some
    (SolidCore.Solidity.Source.Stmt.returnValues
      [SolidCore.Solidity.Source.Expr.binary
        SolidCore.Solidity.Source.BinaryOp.bitAnd lhsCore rhsCore]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?,
    L00_SourceSolidity.Executable.BinaryOp.toCore?, hLhs, hRhs,
    hRat, hBool]
  rfl

theorem binaryNumberLiteralRat_sourceCore
    {op : L00_SourceSolidity.BinaryOp}
    {lhs rhs : L00_SourceSolidity.Expr}
    {value : L00_SourceSolidity.Executable.NumberRat}
    {word : L01_ValidSolidity.Word}
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = some value)
    (hExact : value.exactNat? = some word) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary op lhs rhs) =
      some (SolidCore.Solidity.Source.Expr.word word) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?, hRat, hExact]
  rfl

theorem binaryNumberLiteralRat_returnCoreWithInternalCalls
    {op : L00_SourceSolidity.BinaryOp}
    {lhs rhs : L00_SourceSolidity.Expr}
    {value : L00_SourceSolidity.Executable.NumberRat}
    {word : L01_ValidSolidity.Word}
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = some value)
    (hExact : value.exactNat? = some word)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.binary op lhs rhs))) =
      some
        (SolidCore.Solidity.Source.Stmt.returnValues
          [SolidCore.Solidity.Source.Expr.word word]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?, hRat, hExact]
  rfl

theorem binaryNumberLiteralBool_sourceCore
    {op : L00_SourceSolidity.BinaryOp}
    {lhs rhs : L00_SourceSolidity.Expr}
    {value : Bool}
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = some value) :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary op lhs rhs) =
      some
        (SolidCore.Solidity.Source.Expr.word
          (L00_SourceSolidity.Executable.numberLiteralBoolWord value)) := by
  simp only [L00_SourceSolidity.Executable.Expr.toCore?, hRat, hBool]

theorem binaryNumberLiteralBool_returnCoreWithInternalCalls
    {op : L00_SourceSolidity.BinaryOp}
    {lhs rhs : L00_SourceSolidity.Expr}
    {value : Bool}
    (hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = none)
    (hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool?
        (L00_SourceSolidity.Expr.binary op lhs rhs) = some value)
    (env : L00_SourceSolidity.Executable.TypeEnv)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (freeFunctions : List L00_SourceSolidity.FunctionDecl)
    (returnTys : List L00_SourceSolidity.Ty) :
    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
        (internalFuel :=
          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
        (storageRefEnv := [])
        (env := env)
        (storageNames := [])
        (modifiers := [])
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.binary op lhs rhs))) =
      some
        (SolidCore.Solidity.Source.Stmt.returnValues
          [SolidCore.Solidity.Source.Expr.word
            (L00_SourceSolidity.Executable.numberLiteralBoolWord value)]) := by
  simp only [L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
    L00_SourceSolidity.Executable.Stmt.toCore?,
    L00_SourceSolidity.Executable.Expr.toCore?, hRat, hBool]
  rfl

structure CheckedAdd (lhs rhs : L01_ValidSolidity.Word) where
  value : L01_ValidSolidity.Word
  checked :
    SolidCore.Solidity.Source.checkedAdd true lhs rhs =
      Except.ok value
  valueNorm : SharedSemantics.norm value = value

def checkedAddChecked? (lhs rhs : L01_ValidSolidity.Word) :
    Option (CheckedAdd lhs rhs) :=
  match hAdd :
      SolidCore.Solidity.Source.checkedAdd true lhs rhs with
  | Except.ok value =>
      some
        { value := value
          checked := hAdd
          valueNorm := by
            have hAddOk := hAdd
            unfold SolidCore.Solidity.Source.checkedAdd at hAddOk
            by_cases hOverflow :
                SolidCore.Solidity.Source.wordModulus <=
                  SharedSemantics.norm lhs + SharedSemantics.norm rhs
            · simp [hOverflow] at hAddOk
            · simp [hOverflow] at hAddOk
              rw [← hAddOk]
              simp [SharedSemantics.addWord, SharedSemantics.norm_norm] }
  | Except.error _ => none

theorem checkedAddChecked?_addWord
    {lhs rhs : L01_ValidSolidity.Word}
    {checked : CheckedAdd lhs rhs}
    (_hChecked : checkedAddChecked? lhs rhs = some checked) :
    SharedSemantics.addWord lhs rhs = checked.value := by
  have hAddOk := checked.checked
  unfold SolidCore.Solidity.Source.checkedAdd at hAddOk
  by_cases hOverflow :
      SolidCore.Solidity.Source.wordModulus <=
        SharedSemantics.norm lhs + SharedSemantics.norm rhs
  · simp [hOverflow] at hAddOk
  · simp [hOverflow] at hAddOk
    exact hAddOk

structure CheckedSub (lhs rhs : L01_ValidSolidity.Word) where
  value : L01_ValidSolidity.Word
  checked :
    SolidCore.Solidity.Source.checkedSub true lhs rhs =
      Except.ok value
  valueNorm : SharedSemantics.norm value = value

def checkedSubChecked? (lhs rhs : L01_ValidSolidity.Word) :
    Option (CheckedSub lhs rhs) :=
  match hSub :
      SolidCore.Solidity.Source.checkedSub true lhs rhs with
  | Except.ok value =>
      some
        { value := value
          checked := hSub
          valueNorm := by
            have hSubOk := hSub
            unfold SolidCore.Solidity.Source.checkedSub at hSubOk
            by_cases hOverflow :
                SharedSemantics.norm lhs < SharedSemantics.norm rhs
            · simp [hOverflow] at hSubOk
            · simp [hOverflow] at hSubOk
              rw [← hSubOk]
              simp [SharedSemantics.subWord, SharedSemantics.norm_norm] }
  | Except.error _ => none

theorem checkedSubChecked?_subWord
    {lhs rhs : L01_ValidSolidity.Word}
    {checked : CheckedSub lhs rhs}
    (_hChecked : checkedSubChecked? lhs rhs = some checked) :
    SharedSemantics.subWord lhs rhs = checked.value := by
  have hSubOk := checked.checked
  unfold SolidCore.Solidity.Source.checkedSub at hSubOk
  by_cases hOverflow :
      SharedSemantics.norm lhs < SharedSemantics.norm rhs
  · simp [hOverflow] at hSubOk
  · simp [hOverflow] at hSubOk
    exact hSubOk

structure CheckedMul (lhs rhs : L01_ValidSolidity.Word) where
  value : L01_ValidSolidity.Word
  checked :
    SolidCore.Solidity.Source.checkedMul true lhs rhs =
      Except.ok value
  valueNorm : SharedSemantics.norm value = value

def checkedMulChecked? (lhs rhs : L01_ValidSolidity.Word) :
    Option (CheckedMul lhs rhs) :=
  match hMul :
      SolidCore.Solidity.Source.checkedMul true lhs rhs with
  | Except.ok value =>
      some
        { value := value
          checked := hMul
          valueNorm := by
            have hMulOk := hMul
            unfold SolidCore.Solidity.Source.checkedMul at hMulOk
            by_cases hOverflow :
                SolidCore.Solidity.Source.wordModulus <=
                  SharedSemantics.norm lhs * SharedSemantics.norm rhs
            · simp [hOverflow] at hMulOk
            · simp [hOverflow] at hMulOk
              rw [← hMulOk]
              simp [SharedSemantics.mulWord, SharedSemantics.norm_norm] }
  | Except.error _ => none

theorem checkedMulChecked?_mulWord
    {lhs rhs : L01_ValidSolidity.Word}
    {checked : CheckedMul lhs rhs}
    (_hChecked : checkedMulChecked? lhs rhs = some checked) :
    SharedSemantics.mulWord lhs rhs = checked.value := by
  have hMulOk := checked.checked
  unfold SolidCore.Solidity.Source.checkedMul at hMulOk
  by_cases hOverflow :
      SolidCore.Solidity.Source.wordModulus <=
        SharedSemantics.norm lhs * SharedSemantics.norm rhs
  · simp [hOverflow] at hMulOk
  · simp [hOverflow] at hMulOk
    exact hMulOk

structure CheckedEq (lhs rhs : L01_ValidSolidity.Word) where
  value : L01_ValidSolidity.Word
  value_eq : value = SharedSemantics.eqWord lhs rhs
  valueNorm : SharedSemantics.norm value = value

def checkedEq (lhs rhs : L01_ValidSolidity.Word) : CheckedEq lhs rhs :=
  { value := SharedSemantics.eqWord lhs rhs
    value_eq := rfl
    valueNorm := norm_eqWord lhs rhs }

inductive EqSourceMode where
  | structural
  | folded (value : Bool)

def eqSourceMode? (source : L00_SourceSolidity.Expr) :
    Option EqSourceMode :=
  if sourceBinaryEqNotFolded? source = some () then
    some EqSourceMode.structural
  else
    match L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
    | some value => some (EqSourceMode.folded value)
    | none => none

theorem eqSourceMode?_structural
    {source : L00_SourceSolidity.Expr}
    (hMode :
      eqSourceMode? source = some EqSourceMode.structural) :
    sourceBinaryEqNotFolded? source = some () := by
  unfold eqSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryEqNotFolded? source = some ()
  · exact hNotFolded
  · simp [hNotFolded] at hMode
    cases hBool :
        L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
    | none => simp [hBool] at hMode
    | some value => simp [hBool] at hMode

theorem eqSourceMode?_folded
    {source : L00_SourceSolidity.Expr}
    {value : Bool}
    (hMode :
      eqSourceMode? source = some (EqSourceMode.folded value)) :
    L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
      some value := by
  unfold eqSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryEqNotFolded? source = some ()
  · simp [hNotFolded] at hMode
  · simp [hNotFolded] at hMode
    cases hBool :
        L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
    | none => simp [hBool] at hMode
    | some foldedValue =>
        simp [hBool] at hMode
        cases hMode
        rfl

theorem eqSourceMode?_folded_notFolded
    {source : L00_SourceSolidity.Expr}
    {value : Bool}
    (hMode :
      eqSourceMode? source = some (EqSourceMode.folded value)) :
    sourceBinaryEqNotFolded? source = none := by
  unfold eqSourceMode? at hMode
  cases hNotFolded : sourceBinaryEqNotFolded? source with
  | none => rfl
  | some unitValue =>
      cases unitValue
      simp [hNotFolded] at hMode

structure AddSourceWitness
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (addChecked : CheckedAdd lhsChecked.value rhsChecked.value) where
  core : CoreExpr
  sourceCore :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) =
      some core
  returnCoreWithInternalCalls :
    ∀ env functions returnTys,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv := [])
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := functions)
          (freeFunctions := [])
          (returnTys := returnTys)
          (stmt := L00_SourceSolidity.Stmt.returnValues
            (some
              (L00_SourceSolidity.Expr.binary
                L00_SourceSolidity.BinaryOp.add lhs rhs))) =
        some (SolidCore.Solidity.Source.Stmt.returnValues [core])
  sourceValueEvalChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.eval context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word addChecked.value)
  sourceValueEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.eval
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word addChecked.value)
  sourceValueEvalWithRuntimeChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.evalWithRuntime
            context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word addChecked.value, runtime)
  sourceValueEvalWithRuntime :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.evalWithRuntime
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word addChecked.value, runtime)

inductive AddSourceMode where
  | structural
  | folded
      (rat : L00_SourceSolidity.Executable.NumberRat)
      (raw : L01_ValidSolidity.Word)

def addSourceMode? (source : L00_SourceSolidity.Expr)
    (value : L01_ValidSolidity.Word) : Option AddSourceMode :=
  if sourceBinaryAddNotFolded? source = some () then
    some AddSourceMode.structural
  else
    match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | some rat =>
        match rat.exactNat? with
        | some raw =>
            if SharedSemantics.norm raw = value then
              some (AddSourceMode.folded rat raw)
            else
              none
        | none => none
    | none => none

theorem addSourceMode?_structural
    {source : L00_SourceSolidity.Expr}
    {value : L01_ValidSolidity.Word}
    (hMode :
      addSourceMode? source value = some AddSourceMode.structural) :
    sourceBinaryAddNotFolded? source = some () := by
  unfold addSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryAddNotFolded? source = some ()
  · exact hNotFolded
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = value <;>
              simp [hRat, hExact, hValue] at hMode

theorem addSourceMode?_folded
    {source : L00_SourceSolidity.Expr}
    {value raw : L01_ValidSolidity.Word}
    {rat : L00_SourceSolidity.Executable.NumberRat}
    (hMode :
      addSourceMode? source value =
        some (AddSourceMode.folded rat raw)) :
    L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
        some rat ∧
      rat.exactNat? = some raw ∧
      SharedSemantics.norm raw = value := by
  unfold addSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryAddNotFolded? source = some ()
  · simp [hNotFolded] at hMode
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw' =>
            by_cases hValue : SharedSemantics.norm raw' = value
            · simp [hRat, hExact, hValue] at hMode
              rcases hMode with ⟨hRatEq, hRawEq⟩
              cases hRatEq
              cases hRawEq
              exact ⟨rfl, hExact, hValue⟩
            · simp [hRat, hExact, hValue] at hMode

def addSourceWitnessOfMode
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (addChecked : CheckedAdd lhsChecked.value rhsChecked.value)
    {mode : AddSourceMode}
    (hMode :
      addSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.add lhs rhs)
          addChecked.value =
        some mode) :
    AddSourceWitness lhsChecked rhsChecked addChecked :=
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.add lhs rhs
  match mode with
  | AddSourceMode.structural =>
      let core :=
        SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.add
          lhsChecked.core rhsChecked.core
      have hNotFolded :
          sourceBinaryAddNotFolded? source = some () :=
        addSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            none :=
        sourceBinaryAddNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinaryAddNotFolded?_bool_none hNotFolded
      { core := core
        sourceCore := by
          simpa [source, core] using
            binaryAdd_sourceCore
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binaryAdd_returnCoreWithInternalCalls
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEvalChecked context runtime hChecked]
          rw [rhsChecked.sourceValueEvalChecked context runtime hChecked]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedAdd context.checked
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word addChecked.value)
          rw [hChecked]
          rw [addChecked.checked]
          rfl
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEval runtime]
          rw [rhsChecked.sourceValueEval runtime]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedAdd true
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word addChecked.value)
          rw [addChecked.checked]
          rfl
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  context runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  context.checked
                  SolidCore.Solidity.Source.BinaryOp.add
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word addChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord, hChecked,
            addChecked.checked]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntime runtime]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  SolidCore.Solidity.Source.Context.empty
                  runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  SolidCore.Solidity.Source.Context.empty.checked
                  SolidCore.Solidity.Source.BinaryOp.add
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word addChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntime runtime]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord,
            SolidCore.Solidity.Source.Context.empty, addChecked.checked] }
  | AddSourceMode.folded rat raw =>
      let core := SolidCore.Solidity.Source.Expr.word raw
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (addSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (addSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = addChecked.value :=
        (addSourceMode?_folded hMode).right.right
      { core := core
        sourceCore := by
          simpa [source, core] using
            binaryNumberLiteralRat_sourceCore
              (op := L00_SourceSolidity.BinaryOp.add)
              (lhs := lhs) (rhs := rhs)
              hRat hExact
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binaryNumberLiteralRat_returnCoreWithInternalCalls
              (op := L00_SourceSolidity.BinaryOp.add)
              (lhs := lhs) (rhs := rhs)
              hRat hExact env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue] }

structure SubSourceWitness
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (subChecked : CheckedSub lhsChecked.value rhsChecked.value) where
  core : CoreExpr
  sourceCore :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) =
      some core
  returnCoreWithInternalCalls :
    ∀ env functions returnTys,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv := [])
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := functions)
          (freeFunctions := [])
          (returnTys := returnTys)
          (stmt := L00_SourceSolidity.Stmt.returnValues
            (some
              (L00_SourceSolidity.Expr.binary
                L00_SourceSolidity.BinaryOp.sub lhs rhs))) =
        some (SolidCore.Solidity.Source.Stmt.returnValues [core])
  sourceValueEvalChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.eval context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word subChecked.value)
  sourceValueEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.eval
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word subChecked.value)
  sourceValueEvalWithRuntimeChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.evalWithRuntime
            context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word subChecked.value, runtime)
  sourceValueEvalWithRuntime :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.evalWithRuntime
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word subChecked.value, runtime)

inductive SubSourceMode where
  | structural
  | folded
      (rat : L00_SourceSolidity.Executable.NumberRat)
      (raw : L01_ValidSolidity.Word)

def subSourceMode? (source : L00_SourceSolidity.Expr)
    (value : L01_ValidSolidity.Word) : Option SubSourceMode :=
  if sourceBinarySubNotFolded? source = some () then
    some SubSourceMode.structural
  else
    match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | some rat =>
        match rat.exactNat? with
        | some raw =>
            if SharedSemantics.norm raw = value then
              some (SubSourceMode.folded rat raw)
            else
              none
        | none => none
    | none => none

theorem subSourceMode?_structural
    {source : L00_SourceSolidity.Expr}
    {value : L01_ValidSolidity.Word}
    (hMode :
      subSourceMode? source value = some SubSourceMode.structural) :
    sourceBinarySubNotFolded? source = some () := by
  unfold subSourceMode? at hMode
  by_cases hNotFolded : sourceBinarySubNotFolded? source = some ()
  · exact hNotFolded
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = value <;>
              simp [hRat, hExact, hValue] at hMode

theorem subSourceMode?_folded
    {source : L00_SourceSolidity.Expr}
    {value raw : L01_ValidSolidity.Word}
    {rat : L00_SourceSolidity.Executable.NumberRat}
    (hMode :
      subSourceMode? source value =
        some (SubSourceMode.folded rat raw)) :
    L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
        some rat ∧
      rat.exactNat? = some raw ∧
      SharedSemantics.norm raw = value := by
  unfold subSourceMode? at hMode
  by_cases hNotFolded : sourceBinarySubNotFolded? source = some ()
  · simp [hNotFolded] at hMode
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw' =>
            by_cases hValue : SharedSemantics.norm raw' = value
            · simp [hRat, hExact, hValue] at hMode
              rcases hMode with ⟨hRatEq, hRawEq⟩
              cases hRatEq
              cases hRawEq
              exact ⟨rfl, hExact, hValue⟩
            · simp [hRat, hExact, hValue] at hMode

def subSourceWitnessOfMode
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (subChecked : CheckedSub lhsChecked.value rhsChecked.value)
    {mode : SubSourceMode}
    (hMode :
      subSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.sub lhs rhs)
          subChecked.value =
        some mode) :
    SubSourceWitness lhsChecked rhsChecked subChecked :=
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.sub lhs rhs
  match mode with
  | SubSourceMode.structural =>
      let core :=
        SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.sub
          lhsChecked.core rhsChecked.core
      have hNotFolded :
          sourceBinarySubNotFolded? source = some () :=
        subSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            none :=
        sourceBinarySubNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinarySubNotFolded?_bool_none hNotFolded
      { core := core
        sourceCore := by
          simpa [source, core] using
            binarySub_sourceCore
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binarySub_returnCoreWithInternalCalls
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEvalChecked context runtime hChecked]
          rw [rhsChecked.sourceValueEvalChecked context runtime hChecked]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedSub context.checked
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word subChecked.value)
          rw [hChecked]
          rw [subChecked.checked]
          rfl
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEval runtime]
          rw [rhsChecked.sourceValueEval runtime]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedSub true
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word subChecked.value)
          rw [subChecked.checked]
          rfl
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  context runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  context.checked
                  SolidCore.Solidity.Source.BinaryOp.sub
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word subChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord, hChecked,
            subChecked.checked]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntime runtime]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  SolidCore.Solidity.Source.Context.empty
                  runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  SolidCore.Solidity.Source.Context.empty.checked
                  SolidCore.Solidity.Source.BinaryOp.sub
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word subChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntime runtime]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord,
            SolidCore.Solidity.Source.Context.empty, subChecked.checked] }
  | SubSourceMode.folded rat raw =>
      let core := SolidCore.Solidity.Source.Expr.word raw
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (subSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (subSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = subChecked.value :=
        (subSourceMode?_folded hMode).right.right
      { core := core
        sourceCore := by
          simpa [source, core] using
            binaryNumberLiteralRat_sourceCore
              (op := L00_SourceSolidity.BinaryOp.sub)
              (lhs := lhs) (rhs := rhs)
              hRat hExact
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binaryNumberLiteralRat_returnCoreWithInternalCalls
              (op := L00_SourceSolidity.BinaryOp.sub)
              (lhs := lhs) (rhs := rhs)
              hRat hExact env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue] }

structure MulSourceWitness
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (mulChecked : CheckedMul lhsChecked.value rhsChecked.value) where
  core : CoreExpr
  sourceCore :
    L00_SourceSolidity.Executable.Expr.toCore? []
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) =
      some core
  returnCoreWithInternalCalls :
    ∀ env functions returnTys,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv := [])
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := functions)
          (freeFunctions := [])
          (returnTys := returnTys)
          (stmt := L00_SourceSolidity.Stmt.returnValues
            (some
              (L00_SourceSolidity.Expr.binary
                L00_SourceSolidity.BinaryOp.mul lhs rhs))) =
        some (SolidCore.Solidity.Source.Stmt.returnValues [core])
  sourceValueEvalChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.eval context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word mulChecked.value)
  sourceValueEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.eval
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word mulChecked.value)
  sourceValueEvalWithRuntimeChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Expr.evalWithRuntime
            context runtime core =
          Except.ok
            (SolidCore.Solidity.Source.Value.word mulChecked.value, runtime)
  sourceValueEvalWithRuntime :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Expr.evalWithRuntime
          SolidCore.Solidity.Source.Context.empty runtime core =
        Except.ok
          (SolidCore.Solidity.Source.Value.word mulChecked.value, runtime)

inductive MulSourceMode where
  | structural
  | folded
      (rat : L00_SourceSolidity.Executable.NumberRat)
      (raw : L01_ValidSolidity.Word)

def mulSourceMode? (source : L00_SourceSolidity.Expr)
    (value : L01_ValidSolidity.Word) : Option MulSourceMode :=
  if sourceBinaryMulNotFolded? source = some () then
    some MulSourceMode.structural
  else
    match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | some rat =>
        match rat.exactNat? with
        | some raw =>
            if SharedSemantics.norm raw = value then
              some (MulSourceMode.folded rat raw)
            else
              none
        | none => none
    | none => none

theorem mulSourceMode?_structural
    {source : L00_SourceSolidity.Expr}
    {value : L01_ValidSolidity.Word}
    (hMode :
      mulSourceMode? source value = some MulSourceMode.structural) :
    sourceBinaryMulNotFolded? source = some () := by
  unfold mulSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryMulNotFolded? source = some ()
  · exact hNotFolded
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = value <;>
              simp [hRat, hExact, hValue] at hMode

theorem mulSourceMode?_folded
    {source : L00_SourceSolidity.Expr}
    {value raw : L01_ValidSolidity.Word}
    {rat : L00_SourceSolidity.Executable.NumberRat}
    (hMode :
      mulSourceMode? source value =
        some (MulSourceMode.folded rat raw)) :
    L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
        some rat ∧
      rat.exactNat? = some raw ∧
      SharedSemantics.norm raw = value := by
  unfold mulSourceMode? at hMode
  by_cases hNotFolded : sourceBinaryMulNotFolded? source = some ()
  · simp [hNotFolded] at hMode
  · simp [hNotFolded] at hMode
    cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        simp [hRat] at hMode
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [hRat, hExact] at hMode
        | some raw' =>
            by_cases hValue : SharedSemantics.norm raw' = value
            · simp [hRat, hExact, hValue] at hMode
              rcases hMode with ⟨hRatEq, hRawEq⟩
              cases hRatEq
              cases hRawEq
              exact ⟨rfl, hExact, hValue⟩
            · simp [hRat, hExact, hValue] at hMode

def mulSourceWitnessOfMode
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (mulChecked : CheckedMul lhsChecked.value rhsChecked.value)
    {mode : MulSourceMode}
    (hMode :
      mulSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.mul lhs rhs)
          mulChecked.value =
        some mode) :
    MulSourceWitness lhsChecked rhsChecked mulChecked :=
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.mul lhs rhs
  match mode with
  | MulSourceMode.structural =>
      let core :=
        SolidCore.Solidity.Source.Expr.binary
          SolidCore.Solidity.Source.BinaryOp.mul
          lhsChecked.core rhsChecked.core
      have hNotFolded :
          sourceBinaryMulNotFolded? source = some () :=
        mulSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            none :=
        sourceBinaryMulNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinaryMulNotFolded?_bool_none hNotFolded
      { core := core
        sourceCore := by
          simpa [source, core] using
            binaryMul_sourceCore
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binaryMul_returnCoreWithInternalCalls
              (hLhs := lhsChecked.sourceCore)
              (hRhs := rhsChecked.sourceCore)
              hRat hBool env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEvalChecked context runtime hChecked]
          rw [rhsChecked.sourceValueEvalChecked context runtime hChecked]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedMul context.checked
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word mulChecked.value)
          rw [hChecked]
          rw [mulChecked.checked]
          rfl
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval]
          rw [lhsChecked.sourceValueEval runtime]
          rw [rhsChecked.sourceValueEval runtime]
          change
            (do
              let checkedValue ←
                SolidCore.Solidity.Source.checkedMul true
                  lhsChecked.value rhsChecked.value
              Except.ok
                (SolidCore.Solidity.Source.Value.word checkedValue)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word mulChecked.value)
          rw [mulChecked.checked]
          rfl
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  context runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  context.checked
                  SolidCore.Solidity.Source.BinaryOp.mul
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word mulChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntimeChecked
            context runtime hChecked]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord, hChecked,
            mulChecked.checked]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
          rw [lhsChecked.sourceValueEvalWithRuntime runtime]
          change
            (do
              let rhsValue ←
                SolidCore.Solidity.Source.Expr.evalWithRuntime
                  SolidCore.Solidity.Source.Context.empty
                  runtime rhsChecked.core
              let value ←
                SolidCore.Solidity.Source.BinaryOp.apply
                  SolidCore.Solidity.Source.Context.empty.checked
                  SolidCore.Solidity.Source.BinaryOp.mul
                  (SolidCore.Solidity.Source.Value.word lhsChecked.value)
                  rhsValue.fst
              Except.ok (value, rhsValue.snd)) =
              Except.ok
                (SolidCore.Solidity.Source.Value.word mulChecked.value,
                  runtime)
          rw [rhsChecked.sourceValueEvalWithRuntime runtime]
          simp [SolidCore.Solidity.Source.BinaryOp.apply,
            SolidCore.Solidity.Source.BinaryOp.applyWord,
            SolidCore.Solidity.Source.Context.empty, mulChecked.checked] }
  | MulSourceMode.folded rat raw =>
      let core := SolidCore.Solidity.Source.Expr.word raw
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (mulSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (mulSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = mulChecked.value :=
        (mulSourceMode?_folded hMode).right.right
      { core := core
        sourceCore := by
          simpa [source, core] using
            binaryNumberLiteralRat_sourceCore
              (op := L00_SourceSolidity.BinaryOp.mul)
              (lhs := lhs) (rhs := rhs)
              hRat hExact
        returnCoreWithInternalCalls := by
          intro env functions returnTys
          simpa [source, core] using
            binaryNumberLiteralRat_returnCoreWithInternalCalls
              (op := L00_SourceSolidity.BinaryOp.mul)
              (lhs := lhs) (rhs := rhs)
              hRat hExact env functions [] returnTys
        sourceValueEvalChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEval := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.eval,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntimeChecked := by
          intro context runtime hChecked
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue]
        sourceValueEvalWithRuntime := by
          intro runtime
          simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime,
            SolidCore.Solidity.Source.normWord, hValue] }

def bitAndCheckedExpr
    {lhs rhs : L00_SourceSolidity.Expr}
    (lhsChecked : CheckedExpr lhs)
    (rhsChecked : CheckedExpr rhs)
    (hNotFolded :
      sourceBinaryBitAndNotFolded?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) =
        some ()) :
    CheckedExpr
      (L00_SourceSolidity.Expr.binary
        L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) :=
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
  let value :=
    SharedSemantics.andWord lhsChecked.value rhsChecked.value
  let expr :=
    L01_ValidSolidity.Expr.bitAnd lhsChecked.expr rhsChecked.expr
  let core :=
    SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.bitAnd
      lhsChecked.core rhsChecked.core
  let targetCoreExpr :=
    SolidCore.Solidity.Source.Expr.binary
      SolidCore.Solidity.Source.BinaryOp.bitAnd
      lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
  have hValueNorm : SharedSemantics.norm value = value :=
    norm_andWord lhsChecked.value rhsChecked.value
  have hRat :
      L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
    sourceBinaryBitAndNotFolded?_rat_none hNotFolded
  have hBool :
      L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
    sourceBinaryBitAndNotFolded?_bool_none hNotFolded
  have hTargetValueEval :
      SolidCore.Solidity.Source.Expr.eval
          SolidCore.Solidity.Source.Context.empty
          (SolidCore.Solidity.Source.Runtime.ofState
            SolidCore.Solidity.Source.State.empty)
          targetCoreExpr =
        Except.ok (SolidCore.Solidity.Source.Value.word value) := by
    simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
    rw [lhsChecked.targetValueEval]
    rw [rhsChecked.targetValueEval]
    simp [SolidCore.Solidity.Source.BinaryOp.apply,
      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
  { expr := expr
    resultTy := by
      rfl
    value := value
    valueNorm := hValueNorm
    eval := by
      unfold L01_ValidSolidity.Expr.Eval
      simp [expr, L01_ValidSolidity.Expr.bitAnd,
        L01_ValidSolidity.Expr.eval?,
        L01_ValidSolidity.Expr.toCore?,
        L01_ValidSolidity.BinaryOp.toCore?,
        L01_ValidSolidity.Ty.uint256,
        lhsChecked.targetCore, rhsChecked.targetCore,
        L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
        L00_SourceSolidity.Executable.CoreExpr.evalWord?]
      change
        (match
            SolidCore.Solidity.Source.Expr.eval
              SolidCore.Solidity.Source.Context.empty
              (SolidCore.Solidity.Source.Runtime.ofState
                SolidCore.Solidity.Source.State.empty)
              targetCoreExpr with
        | Except.ok coreValue =>
            L00_SourceSolidity.Executable.CoreValue.asWord? coreValue
        | Except.error _ => none) = some value
      rw [hTargetValueEval]
      simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
        SolidCore.Solidity.Source.Value.asWord?, hValueNorm]
    core := core
    sourceCore := by
      simpa [source, core] using
        binaryBitAnd_sourceCore
          (hLhs := lhsChecked.sourceCore)
          (hRhs := rhsChecked.sourceCore)
          hRat hBool
    sourceInlineConstantsFuel := by
      intro fuel
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
            lhsChecked.sourceInlineConstantsFuel fuel,
            rhsChecked.sourceInlineConstantsFuel fuel]
    sourceInlineConstants := by
      change
        L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
            L00_SourceSolidity.Executable.defaultInlineConstantsFuel
            [] source = source
      cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
            lhsChecked.sourceInlineConstantsFuel fuel,
            rhsChecked.sourceInlineConstantsFuel fuel]
    sourceRewriteSuperCallsFuel := by
      intro contractName fuel
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
            lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
            rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
    sourceRewriteSuperCalls := by
      intro contractName
      change
        L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
            contractName
            L00_SourceSolidity.Executable.defaultInlineConstantsFuel
            source = source
      cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
            lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
            rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
    sourceRewriteBaseCallsFuel := by
      intro baseNames fuel
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
            lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
            rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
    sourceRewriteBaseCalls := by
      intro baseNames
      change
        L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
            baseNames
            L00_SourceSolidity.Executable.defaultInlineConstantsFuel
            source = source
      cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
            lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
            rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
    sourceAnnotatedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
            lhsChecked.sourceAnnotatedFuel fuel env,
            rhsChecked.sourceAnnotatedFuel fuel env]
    sourceAnnotated := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.annotateAbiFuel
            L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
            env source = source
      cases L00_SourceSolidity.Executable.defaultAnnotateAbiFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
            lhsChecked.sourceAnnotatedFuel fuel env,
            rhsChecked.sourceAnnotatedFuel fuel env]
    sourceResolvedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
            lhsChecked.sourceResolvedFuel fuel env,
            rhsChecked.sourceResolvedFuel fuel env]
    sourceResolved := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
            L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
            env source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
            lhsChecked.sourceResolvedFuel fuel env,
            rhsChecked.sourceResolvedFuel fuel env]
    sourceEnumsResolvedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
            lhsChecked.sourceEnumsResolvedFuel fuel env,
            rhsChecked.sourceEnumsResolvedFuel fuel env]
    sourceEnumsResolved := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
            L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
            env source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
            lhsChecked.sourceEnumsResolvedFuel fuel env,
            rhsChecked.sourceEnumsResolvedFuel fuel env]
    sourceStructsResolvedFuel := by
      intro fuel env typeEnv
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
            lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
            rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
    sourceStructsResolved := by
      intro env typeEnv
      change
        L00_SourceSolidity.Executable.Expr.resolveStructsFuel
            L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
            env typeEnv source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
            lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
            rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
    sourceSelectorsResolvedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
            lhsChecked.sourceSelectorsResolvedFuel fuel env,
            rhsChecked.sourceSelectorsResolvedFuel fuel env]
    sourceSelectorsResolved := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
            L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
            env source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
            lhsChecked.sourceSelectorsResolvedFuel fuel env,
            rhsChecked.sourceSelectorsResolvedFuel fuel env]
    sourceFunctionAddressesResolvedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
            lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
            rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
    sourceFunctionAddressesResolved := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
            L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
            env source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
            lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
            rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
    sourceInterfaceIdsResolvedFuel := by
      intro fuel env
      cases fuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
            lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
            rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
    sourceInterfaceIdsResolved := by
      intro env
      change
        L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
            L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
            env source =
          source
      cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
      | zero =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
      | succ fuel =>
          simp [source,
            L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
            lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
            rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
    returnCoreWithInternalCalls := by
      intro env functions returnTys
      simpa [source, core] using
        binaryBitAnd_returnCoreWithInternalCalls
          (hLhs := lhsChecked.sourceCore)
          (hRhs := rhsChecked.sourceCore)
          hRat hBool env functions [] returnTys
    targetCoreExpr := targetCoreExpr
    targetCore := by
      simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.bitAnd,
        L01_ValidSolidity.Expr.toCore?,
        L01_ValidSolidity.BinaryOp.toCore?,
        L01_ValidSolidity.Ty.uint256,
        lhsChecked.targetCore, rhsChecked.targetCore]
    targetValueEval := hTargetValueEval
    sourceValueEvalChecked := by
      intro context runtime hChecked
      simp [core, SolidCore.Solidity.Source.Expr.eval]
      rw [lhsChecked.sourceValueEvalChecked context runtime hChecked]
      rw [rhsChecked.sourceValueEvalChecked context runtime hChecked]
      simp [SolidCore.Solidity.Source.BinaryOp.apply,
        SolidCore.Solidity.Source.BinaryOp.applyWord, value]
    sourceValueEval := by
      intro runtime
      simp [core, SolidCore.Solidity.Source.Expr.eval]
      rw [lhsChecked.sourceValueEval runtime]
      rw [rhsChecked.sourceValueEval runtime]
      simp [SolidCore.Solidity.Source.BinaryOp.apply,
        SolidCore.Solidity.Source.BinaryOp.applyWord, value]
    sourceValueEvalWithRuntimeChecked := by
      intro context runtime hChecked
      simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
      rw [lhsChecked.sourceValueEvalWithRuntimeChecked
        context runtime hChecked]
      change
        (do
          let rhsValue ←
            SolidCore.Solidity.Source.Expr.evalWithRuntime
              context runtime rhsChecked.core
          let applied ←
            SolidCore.Solidity.Source.BinaryOp.apply
              context.checked
              SolidCore.Solidity.Source.BinaryOp.bitAnd
              (SolidCore.Solidity.Source.Value.word lhsChecked.value)
              rhsValue.fst
          Except.ok (applied, rhsValue.snd)) =
          Except.ok
            (SolidCore.Solidity.Source.Value.word value, runtime)
      rw [rhsChecked.sourceValueEvalWithRuntimeChecked
        context runtime hChecked]
      simp [SolidCore.Solidity.Source.BinaryOp.apply,
        SolidCore.Solidity.Source.BinaryOp.applyWord, value]
    sourceValueEvalWithRuntime := by
      intro runtime
      simp [core, SolidCore.Solidity.Source.Expr.evalWithRuntime]
      rw [lhsChecked.sourceValueEvalWithRuntime runtime]
      change
        (do
          let rhsValue ←
            SolidCore.Solidity.Source.Expr.evalWithRuntime
              SolidCore.Solidity.Source.Context.empty runtime rhsChecked.core
          let applied ←
            SolidCore.Solidity.Source.BinaryOp.apply
              SolidCore.Solidity.Source.Context.empty.checked
              SolidCore.Solidity.Source.BinaryOp.bitAnd
              (SolidCore.Solidity.Source.Value.word lhsChecked.value)
              rhsValue.fst
          Except.ok (applied, rhsValue.snd)) =
          Except.ok
            (SolidCore.Solidity.Source.Value.word value, runtime)
      rw [rhsChecked.sourceValueEvalWithRuntime runtime]
      simp [SolidCore.Solidity.Source.BinaryOp.apply,
        SolidCore.Solidity.Source.BinaryOp.applyWord,
        SolidCore.Solidity.Source.Context.empty, value] }

set_option maxHeartbeats 1000000

def decimalDigit? : Char -> Bool
  | '0' => true
  | '1' => true
  | '2' => true
  | '3' => true
  | '4' => true
  | '5' => true
  | '6' => true
  | '7' => true
  | '8' => true
  | '9' => true
  | _ => false

def decimalCharsAccepted? : List Char -> Bool
  | [] => false
  | ch :: rest => decimalDigit? ch && rest.all decimalDigit?

def decimalLiteralAccepted? (raw : String) : Bool :=
  match L00_SourceSolidity.Executable.parseNumberNat? raw with
  | some value => value == L00_SourceSolidity.Executable.parseDecimalNat raw
  | none => false

def compileExprChecked? :
    (source : L00_SourceSolidity.Expr) -> Option (CheckedExpr source)
  | L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.number raw) =>
      if hRaw : decimalLiteralAccepted? raw then
        let rawValue := L00_SourceSolidity.Executable.parseDecimalNat raw
        let value := SharedSemantics.norm rawValue
        let source := L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number raw)
        let expr := L01_ValidSolidity.Expr.word rawValue
        let core := SolidCore.Solidity.Source.Expr.word rawValue
        have hAnnotatedFuel :
            ∀ fuel env,
              L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                  fuel env source = source := by
          intro fuel env
          cases fuel <;>
            simp [source,
              L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
        have hAnnotated :
            ∀ env,
              L00_SourceSolidity.Executable.Expr.annotateAbi env source =
                source := by
          intro env
          change
            L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                env source = source
          exact hAnnotatedFuel
            L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
        have hResolvedFuel :
            ∀ fuel env,
              L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                  fuel env source =
                source := by
          intro fuel env
          cases fuel <;>
            simp [source,
              L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
        have hEnumsResolvedFuel :
            ∀ fuel env,
              L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                  fuel env source =
                source := by
          intro fuel env
          cases fuel <;>
            simp [source,
              L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
        have hStructsResolvedFuel :
            ∀ fuel env typeEnv,
              L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                  fuel env typeEnv source =
                source := by
          intro fuel env typeEnv
          cases fuel <;>
            simp [source,
              L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
        have hParseNumber :
            L00_SourceSolidity.Executable.parseNumberNat? raw =
              some rawValue := by
          cases hParse :
              L00_SourceSolidity.Executable.parseNumberNat? raw with
          | none =>
              simp [decimalLiteralAccepted?, hParse] at hRaw
          | some value =>
              simp [decimalLiteralAccepted?, hParse, rawValue] at hRaw
              simpa [rawValue] using congrArg some hRaw
        some
          { expr := expr
            resultTy := by
              simp [expr]
            value := value
            valueNorm := by
              simp [value, SharedSemantics.norm_norm]
            eval := by
              unfold L01_ValidSolidity.Expr.Eval
              simp [expr, value, L01_ValidSolidity.Expr.word,
                L01_ValidSolidity.Expr.eval?,
                L01_ValidSolidity.Expr.toCore?,
                L01_ValidSolidity.Ty.uint256,
                L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                L00_SourceSolidity.Executable.CoreExpr.evalWord?,
                L00_SourceSolidity.Executable.CoreValue.asWord?,
                SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.Value.asWord?,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm_norm]
            core := core
            sourceCore := by
              simpa [source, core, rawValue]
                using (literalNumber_sourceCore
                  (raw := raw) hParseNumber)
            sourceInlineConstantsFuel := by
              intro fuel
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
            sourceInlineConstants := by
              change
                L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                    L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                    [] source = source
              cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
            sourceRewriteSuperCallsFuel := by
              intro contractName fuel
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
            sourceRewriteSuperCalls := by
              intro contractName
              change
                L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                    contractName
                    L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                    source = source
              cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
            sourceRewriteBaseCallsFuel := by
              intro baseNames fuel
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
            sourceRewriteBaseCalls := by
              intro baseNames
              change
                L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                    baseNames
                    L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                    source = source
              cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
            sourceAnnotatedFuel := hAnnotatedFuel
            sourceAnnotated := hAnnotated
            sourceResolvedFuel := by
              intro fuel env
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
            sourceResolved := by
              intro env
              change
                L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env source =
                  source
              exact hResolvedFuel
                L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
            sourceEnumsResolvedFuel := hEnumsResolvedFuel
            sourceEnumsResolved := by
              intro env
              change
                L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env source =
                  source
              exact hEnumsResolvedFuel
                L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
            sourceStructsResolvedFuel := hStructsResolvedFuel
            sourceStructsResolved := by
              intro env typeEnv
              change
                L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env typeEnv source =
                  source
              exact hStructsResolvedFuel
                L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                env typeEnv
            sourceSelectorsResolvedFuel := by
              intro fuel env
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
            sourceSelectorsResolved := by
              intro env
              change
                L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                    L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                    env source =
                  source
              cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
            sourceFunctionAddressesResolvedFuel := by
              intro fuel env
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
            sourceFunctionAddressesResolved := by
              intro env
              change
                L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                    L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                    env source =
                  source
              cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
            sourceInterfaceIdsResolvedFuel := by
              intro fuel env
              cases fuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
            sourceInterfaceIdsResolved := by
              intro env
              change
                L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                    L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                    env source =
                  source
              cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel <;>
                simp [source,
                  L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
            returnCoreWithInternalCalls := by
              intro env functions returnTys
              simpa [source, core, rawValue]
                using
                  literalNumber_returnCoreWithInternalCalls
                    (raw := raw) hParseNumber env functions [] returnTys
            targetCoreExpr := core
            targetCore := by rfl
            targetValueEval := by
              simp [core, value, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.normWord]
            sourceValueEvalChecked := by
              intro context runtime hChecked
              simp [core, value, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.normWord]
            sourceValueEval := by
              intro runtime
              simp [core, value, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.normWord]
            sourceValueEvalWithRuntimeChecked := by
              intro context runtime hChecked
              simp [core, value,
                SolidCore.Solidity.Source.Expr.evalWithRuntime,
                SolidCore.Solidity.Source.normWord]
            sourceValueEvalWithRuntime := by
              intro runtime
              simp [core, value,
                SolidCore.Solidity.Source.Expr.evalWithRuntime,
                SolidCore.Solidity.Source.normWord] }
      else none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.add lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          match checkedAddChecked? lhsChecked.value rhsChecked.value with
          | some addChecked =>
              let value := addChecked.value
              let source :=
                L00_SourceSolidity.Expr.binary
                  L00_SourceSolidity.BinaryOp.add lhs rhs
              let expr :=
                L01_ValidSolidity.Expr.add
                  lhsChecked.expr rhsChecked.expr
              let targetCoreExpr :=
                  SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.add
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                addChecked.valueNorm
              have hContextChecked :
                  SolidCore.Solidity.Source.Context.empty.checked = true := by
                rfl
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                change
                  (do
                    let checkedValue ←
                      SolidCore.Solidity.Source.checkedAdd true
                        lhsChecked.value rhsChecked.value
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word checkedValue)) =
                    Except.ok (SolidCore.Solidity.Source.Value.word value)
                rw [addChecked.checked]
                rfl
              have hAnnotatedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                        fuel env source = source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                      lhsChecked.sourceAnnotatedFuel,
                      rhsChecked.sourceAnnotatedFuel]
              have hAnnotated :
                  ∀ env,
                    L00_SourceSolidity.Executable.Expr.annotateAbi
                        env source = source := by
                intro env
                change
                  L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                      L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                      env source = source
                exact hAnnotatedFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
              have hResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                        lhsChecked.sourceResolvedFuel fuel env,
                        rhsChecked.sourceResolvedFuel fuel env]
              have hEnumsResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                      lhsChecked.sourceEnumsResolvedFuel fuel env,
                      rhsChecked.sourceEnumsResolvedFuel fuel env]
              have hStructsResolvedFuel :
                  ∀ fuel env typeEnv,
                    L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                        fuel env typeEnv source =
                      source := by
                intro fuel env typeEnv
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                | succ fuel =>
                      simp [source,
                        L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                        lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                        rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
              match hMode : addSourceMode? source value with
              | some mode =>
                let sourceWitness :=
                  addSourceWitnessOfMode
                    lhsChecked rhsChecked addChecked hMode
                some
                    { expr := expr
                      resultTy := by
                        simp [expr]
                      value := value
                      valueNorm := hValueNorm
                      eval := by
                        unfold L01_ValidSolidity.Expr.Eval
                        simp [expr, L01_ValidSolidity.Expr.add,
                          L01_ValidSolidity.Expr.eval?,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore,
                          L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                          L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                        change
                          (match
                              SolidCore.Solidity.Source.Expr.eval
                                SolidCore.Solidity.Source.Context.empty
                                (SolidCore.Solidity.Source.Runtime.ofState
                                  SolidCore.Solidity.Source.State.empty)
                                targetCoreExpr with
                          | Except.ok coreValue =>
                              L00_SourceSolidity.Executable.CoreValue.asWord?
                                coreValue
                          | Except.error _ => none) = some value
                        rw [hTargetValueEval]
                        simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                          SolidCore.Solidity.Source.Value.asWord?,
                          hValueNorm]
                      core := sourceWitness.core
                      sourceCore := sourceWitness.sourceCore
                      sourceInlineConstantsFuel := by
                        intro fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceInlineConstants := by
                        change
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              [] source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceRewriteSuperCallsFuel := by
                        intro contractName fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteSuperCalls := by
                        intro contractName
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                              contractName
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteBaseCallsFuel := by
                        intro baseNames fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceRewriteBaseCalls := by
                        intro baseNames
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                              baseNames
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceAnnotatedFuel := hAnnotatedFuel
                      sourceAnnotated := hAnnotated
                      sourceResolvedFuel := hResolvedFuel
                      sourceResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceEnumsResolvedFuel := hEnumsResolvedFuel
                      sourceEnumsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hEnumsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceStructsResolvedFuel := hStructsResolvedFuel
                      sourceStructsResolved := by
                        intro env typeEnv
                        change
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env typeEnv source =
                            source
                        exact hStructsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv
                      sourceSelectorsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceSelectorsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                              L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceFunctionAddressesResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceFunctionAddressesResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                              L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceInterfaceIdsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      sourceInterfaceIdsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                              L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      returnCoreWithInternalCalls :=
                        sourceWitness.returnCoreWithInternalCalls
                      targetCoreExpr := targetCoreExpr
                      targetCore := by
                        simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.add,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore]
                      targetValueEval := hTargetValueEval
                      sourceValueEvalChecked :=
                        sourceWitness.sourceValueEvalChecked
                      sourceValueEval := sourceWitness.sourceValueEval
                      sourceValueEvalWithRuntimeChecked :=
                        sourceWitness.sourceValueEvalWithRuntimeChecked
                      sourceValueEvalWithRuntime :=
                        sourceWitness.sourceValueEvalWithRuntime }
                | none => none
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.sub lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          match checkedSubChecked? lhsChecked.value rhsChecked.value with
          | some subChecked =>
              let value := subChecked.value
              let source :=
                L00_SourceSolidity.Expr.binary
                  L00_SourceSolidity.BinaryOp.sub lhs rhs
              let expr :=
                L01_ValidSolidity.Expr.sub
                  lhsChecked.expr rhsChecked.expr
              let targetCoreExpr :=
                  SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.sub
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                subChecked.valueNorm
              have hContextChecked :
                  SolidCore.Solidity.Source.Context.empty.checked = true := by
                rfl
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                change
                  (do
                    let checkedValue ←
                      SolidCore.Solidity.Source.checkedSub true
                        lhsChecked.value rhsChecked.value
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word checkedValue)) =
                    Except.ok (SolidCore.Solidity.Source.Value.word value)
                rw [subChecked.checked]
                rfl
              have hAnnotatedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                        fuel env source = source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                      lhsChecked.sourceAnnotatedFuel,
                      rhsChecked.sourceAnnotatedFuel]
              have hAnnotated :
                  ∀ env,
                    L00_SourceSolidity.Executable.Expr.annotateAbi
                        env source = source := by
                intro env
                change
                  L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                      L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                      env source = source
                exact hAnnotatedFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
              have hResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                        lhsChecked.sourceResolvedFuel fuel env,
                        rhsChecked.sourceResolvedFuel fuel env]
              have hEnumsResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                      lhsChecked.sourceEnumsResolvedFuel fuel env,
                      rhsChecked.sourceEnumsResolvedFuel fuel env]
              have hStructsResolvedFuel :
                  ∀ fuel env typeEnv,
                    L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                        fuel env typeEnv source =
                      source := by
                intro fuel env typeEnv
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                | succ fuel =>
                      simp [source,
                        L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                        lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                        rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
              match hMode : subSourceMode? source value with
              | some mode =>
                let sourceWitness :=
                  subSourceWitnessOfMode
                    lhsChecked rhsChecked subChecked hMode
                some
                    { expr := expr
                      resultTy := by
                        simp [expr]
                      value := value
                      valueNorm := hValueNorm
                      eval := by
                        unfold L01_ValidSolidity.Expr.Eval
                        simp [expr, L01_ValidSolidity.Expr.sub,
                          L01_ValidSolidity.Expr.eval?,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore,
                          L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                          L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                        change
                          (match
                              SolidCore.Solidity.Source.Expr.eval
                                SolidCore.Solidity.Source.Context.empty
                                (SolidCore.Solidity.Source.Runtime.ofState
                                  SolidCore.Solidity.Source.State.empty)
                                targetCoreExpr with
                          | Except.ok coreValue =>
                              L00_SourceSolidity.Executable.CoreValue.asWord?
                                coreValue
                          | Except.error _ => none) = some value
                        rw [hTargetValueEval]
                        simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                          SolidCore.Solidity.Source.Value.asWord?,
                          hValueNorm]
                      core := sourceWitness.core
                      sourceCore := sourceWitness.sourceCore
                      sourceInlineConstantsFuel := by
                        intro fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceInlineConstants := by
                        change
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              [] source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceRewriteSuperCallsFuel := by
                        intro contractName fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteSuperCalls := by
                        intro contractName
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                              contractName
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteBaseCallsFuel := by
                        intro baseNames fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceRewriteBaseCalls := by
                        intro baseNames
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                              baseNames
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceAnnotatedFuel := hAnnotatedFuel
                      sourceAnnotated := hAnnotated
                      sourceResolvedFuel := hResolvedFuel
                      sourceResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceEnumsResolvedFuel := hEnumsResolvedFuel
                      sourceEnumsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hEnumsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceStructsResolvedFuel := hStructsResolvedFuel
                      sourceStructsResolved := by
                        intro env typeEnv
                        change
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env typeEnv source =
                            source
                        exact hStructsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv
                      sourceSelectorsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceSelectorsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                              L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceFunctionAddressesResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceFunctionAddressesResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                              L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceInterfaceIdsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      sourceInterfaceIdsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                              L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      returnCoreWithInternalCalls :=
                        sourceWitness.returnCoreWithInternalCalls
                      targetCoreExpr := targetCoreExpr
                      targetCore := by
                        simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.sub,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore]
                      targetValueEval := hTargetValueEval
                      sourceValueEvalChecked :=
                        sourceWitness.sourceValueEvalChecked
                      sourceValueEval := sourceWitness.sourceValueEval
                      sourceValueEvalWithRuntimeChecked :=
                        sourceWitness.sourceValueEvalWithRuntimeChecked
                      sourceValueEvalWithRuntime :=
                        sourceWitness.sourceValueEvalWithRuntime }
                | none => none
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.mul lhs rhs =>
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          match checkedMulChecked? lhsChecked.value rhsChecked.value with
          | some mulChecked =>
              let value := mulChecked.value
              let source :=
                L00_SourceSolidity.Expr.binary
                  L00_SourceSolidity.BinaryOp.mul lhs rhs
              let expr :=
                L01_ValidSolidity.Expr.mul
                  lhsChecked.expr rhsChecked.expr
              let targetCoreExpr :=
                  SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.mul
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                mulChecked.valueNorm
              have hContextChecked :
                  SolidCore.Solidity.Source.Context.empty.checked = true := by
                rfl
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                change
                  (do
                    let checkedValue ←
                      SolidCore.Solidity.Source.checkedMul true
                        lhsChecked.value rhsChecked.value
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word checkedValue)) =
                    Except.ok (SolidCore.Solidity.Source.Value.word value)
                rw [mulChecked.checked]
                rfl
              have hAnnotatedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                        fuel env source = source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                      lhsChecked.sourceAnnotatedFuel,
                      rhsChecked.sourceAnnotatedFuel]
              have hAnnotated :
                  ∀ env,
                    L00_SourceSolidity.Executable.Expr.annotateAbi
                        env source = source := by
                intro env
                change
                  L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                      L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                      env source = source
                exact hAnnotatedFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
              have hResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                        lhsChecked.sourceResolvedFuel fuel env,
                        rhsChecked.sourceResolvedFuel fuel env]
              have hEnumsResolvedFuel :
                  ∀ fuel env,
                    L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                        fuel env source =
                      source := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                | succ fuel =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                      lhsChecked.sourceEnumsResolvedFuel fuel env,
                      rhsChecked.sourceEnumsResolvedFuel fuel env]
              have hStructsResolvedFuel :
                  ∀ fuel env typeEnv,
                    L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                        fuel env typeEnv source =
                      source := by
                intro fuel env typeEnv
                cases fuel with
                | zero =>
                    simp [source,
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                | succ fuel =>
                      simp [source,
                        L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                        lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                        rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
              match hMode : mulSourceMode? source value with
              | some mode =>
                let sourceWitness :=
                  mulSourceWitnessOfMode
                    lhsChecked rhsChecked mulChecked hMode
                some
                    { expr := expr
                      resultTy := by
                        simp [expr]
                      value := value
                      valueNorm := hValueNorm
                      eval := by
                        unfold L01_ValidSolidity.Expr.Eval
                        simp [expr, L01_ValidSolidity.Expr.mul,
                          L01_ValidSolidity.Expr.eval?,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore,
                          L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                          L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                        change
                          (match
                              SolidCore.Solidity.Source.Expr.eval
                                SolidCore.Solidity.Source.Context.empty
                                (SolidCore.Solidity.Source.Runtime.ofState
                                  SolidCore.Solidity.Source.State.empty)
                                targetCoreExpr with
                          | Except.ok coreValue =>
                              L00_SourceSolidity.Executable.CoreValue.asWord?
                                coreValue
                          | Except.error _ => none) = some value
                        rw [hTargetValueEval]
                        simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                          SolidCore.Solidity.Source.Value.asWord?,
                          hValueNorm]
                      core := sourceWitness.core
                      sourceCore := sourceWitness.sourceCore
                      sourceInlineConstantsFuel := by
                        intro fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceInlineConstants := by
                        change
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              [] source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                              lhsChecked.sourceInlineConstantsFuel fuel,
                              rhsChecked.sourceInlineConstantsFuel fuel]
                      sourceRewriteSuperCallsFuel := by
                        intro contractName fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteSuperCalls := by
                        intro contractName
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                              contractName
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                              lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                              rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                      sourceRewriteBaseCallsFuel := by
                        intro baseNames fuel
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceRewriteBaseCalls := by
                        intro baseNames
                        change
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                              baseNames
                              L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                              source = source
                        cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                              lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                              rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                      sourceAnnotatedFuel := hAnnotatedFuel
                      sourceAnnotated := hAnnotated
                      sourceResolvedFuel := hResolvedFuel
                      sourceResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceEnumsResolvedFuel := hEnumsResolvedFuel
                      sourceEnumsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env source =
                            source
                        exact hEnumsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env
                      sourceStructsResolvedFuel := hStructsResolvedFuel
                      sourceStructsResolved := by
                        intro env typeEnv
                        change
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                              L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                              env typeEnv source =
                            source
                        exact hStructsResolvedFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv
                      sourceSelectorsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceSelectorsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                              L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                              lhsChecked.sourceSelectorsResolvedFuel fuel env,
                              rhsChecked.sourceSelectorsResolvedFuel fuel env]
                      sourceFunctionAddressesResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceFunctionAddressesResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                              L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                              lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                              rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                      sourceInterfaceIdsResolvedFuel := by
                        intro fuel env
                        cases fuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      sourceInterfaceIdsResolved := by
                        intro env
                        change
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                              L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                              env source =
                            source
                        cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                        | zero =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                        | succ fuel =>
                            simp [source,
                              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                              lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                              rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                      returnCoreWithInternalCalls :=
                        sourceWitness.returnCoreWithInternalCalls
                      targetCoreExpr := targetCoreExpr
                      targetCore := by
                        simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.mul,
                          L01_ValidSolidity.Expr.toCore?,
                          L01_ValidSolidity.BinaryOp.toCore?,
                          L01_ValidSolidity.Ty.uint256,
                          lhsChecked.targetCore, rhsChecked.targetCore]
                      targetValueEval := hTargetValueEval
                      sourceValueEvalChecked :=
                        sourceWitness.sourceValueEvalChecked
                      sourceValueEval := sourceWitness.sourceValueEval
                      sourceValueEvalWithRuntimeChecked :=
                        sourceWitness.sourceValueEvalWithRuntimeChecked
                      sourceValueEvalWithRuntime :=
                        sourceWitness.sourceValueEvalWithRuntime }
              | none => none
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.bitAnd lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          if hNotFolded : sourceBinaryBitAndNotFolded? source = some () then
            some (bitAndCheckedExpr lhsChecked rhsChecked hNotFolded)
          else
            none
      | _, _ => none
  | _ => none

def compileBoolExprChecked? :
    (source : L00_SourceSolidity.Expr) -> Option (CheckedBoolExpr source)
  | L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.bool value) =>
      let word := SolidCore.Solidity.Source.boolWord value
      let source := L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bool value)
      let expr := L01_ValidSolidity.Expr.bool value
      let core := SolidCore.Solidity.Source.Expr.word word
      some
        { expr := expr
          resultTy := by
            simp [expr]
          value := word
          valueNorm := by
            cases value <;> rfl
          eval := by
            unfold L01_ValidSolidity.Expr.Eval
            simp [expr, word, L01_ValidSolidity.Expr.eval?_bool]
          core := core
          sourceCore := by
            simpa [source, core, word]
              using (literalBool_sourceCore (value := value))
          sourceInlineConstantsFuel := by
            intro fuel
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
          sourceInlineConstants := by
            change
              L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                  L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                  [] source = source
            cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
          sourceRewriteSuperCallsFuel := by
            intro contractName fuel
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
          sourceRewriteSuperCalls := by
            intro contractName
            change
              L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                  contractName
                  L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                  source = source
            cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
          sourceRewriteBaseCallsFuel := by
            intro baseNames fuel
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
          sourceRewriteBaseCalls := by
            intro baseNames
            change
              L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                  baseNames
                  L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                  source = source
            cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
          sourceAnnotatedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
          sourceAnnotated := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                  env source = source
            cases L00_SourceSolidity.Executable.defaultAnnotateAbiFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
          sourceResolvedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
          sourceResolved := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                  env source = source
            cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
          sourceEnumsResolvedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
          sourceEnumsResolved := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                  env source = source
            cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
          sourceStructsResolvedFuel := by
            intro fuel env typeEnv
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
          sourceStructsResolved := by
            intro env typeEnv
            change
              L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                  env typeEnv source =
                source
            cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
          sourceSelectorsResolvedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
          sourceSelectorsResolved := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                  L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                  env source =
                source
            cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
          sourceFunctionAddressesResolvedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
          sourceFunctionAddressesResolved := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                  L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                  env source =
                source
            cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
          sourceInterfaceIdsResolvedFuel := by
            intro fuel env
            cases fuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
          sourceInterfaceIdsResolved := by
            intro env
            change
              L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                  L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                  env source =
                source
            cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel <;>
              simp [source,
                L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
          returnCoreWithInternalCalls := by
            intro env functions returnTys
            simpa [source, core, word]
              using
                literalBool_returnCoreWithInternalCalls
                  (value := value) env functions [] returnTys
          targetCoreExpr := core
          targetCore := by rfl
          targetValueEval := by
            cases value <;>
              simp [core, word, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.boolWord,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm, SharedSemantics.wordModulus]
          sourceValueEvalChecked := by
            intro context runtime hChecked
            cases value <;>
              simp [core, word, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.boolWord,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm, SharedSemantics.wordModulus]
          sourceValueEval := by
            intro runtime
            cases value <;>
              simp [core, word, SolidCore.Solidity.Source.Expr.eval,
                SolidCore.Solidity.Source.boolWord,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm, SharedSemantics.wordModulus]
          sourceValueEvalWithRuntimeChecked := by
            intro context runtime hChecked
            cases value <;>
              simp [core, word,
                SolidCore.Solidity.Source.Expr.evalWithRuntime,
                SolidCore.Solidity.Source.boolWord,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm, SharedSemantics.wordModulus]
          sourceValueEvalWithRuntime := by
            intro runtime
            cases value <;>
              simp [core, word,
                SolidCore.Solidity.Source.Expr.evalWithRuntime,
                SolidCore.Solidity.Source.boolWord,
                SolidCore.Solidity.Source.normWord,
                SharedSemantics.norm, SharedSemantics.wordModulus] }
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.lt lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          if hNotFolded : sourceBinaryLtNotFolded? source = some () then
              let value :=
                SharedSemantics.ltWord
                  lhsChecked.value rhsChecked.value
              let expr :=
                L01_ValidSolidity.Expr.ltOp
                  lhsChecked.expr rhsChecked.expr
              let core :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.lt
                  lhsChecked.core rhsChecked.core
              let targetCoreExpr :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.lt
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                norm_ltWord lhsChecked.value rhsChecked.value
              have hRat :
                  L00_SourceSolidity.Executable.Expr.numberLiteralRat?
                    source = none :=
                sourceBinaryLtNotFolded?_rat_none hNotFolded
              have hBool :
                  L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                    source = none :=
                sourceBinaryLtNotFolded?_bool_none hNotFolded
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                simp [SolidCore.Solidity.Source.BinaryOp.apply,
                  SolidCore.Solidity.Source.BinaryOp.applyWord, value]
              some
                { expr := expr
                  resultTy := by
                    rfl
                  value := value
                  valueNorm := hValueNorm
                  eval := by
                    unfold L01_ValidSolidity.Expr.Eval
                    simp [expr, L01_ValidSolidity.Expr.ltOp,
                      L01_ValidSolidity.Expr.eval?,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore,
                      L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                      L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                    change
                      (match
                          SolidCore.Solidity.Source.Expr.eval
                            SolidCore.Solidity.Source.Context.empty
                            (SolidCore.Solidity.Source.Runtime.ofState
                              SolidCore.Solidity.Source.State.empty)
                            targetCoreExpr with
                      | Except.ok coreValue =>
                          L00_SourceSolidity.Executable.CoreValue.asWord?
                            coreValue
                      | Except.error _ => none) = some value
                    rw [hTargetValueEval]
                    simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                      SolidCore.Solidity.Source.Value.asWord?,
                      hValueNorm]
                  core := core
                  sourceCore := by
                    simpa [source, core] using
                      binaryLt_sourceCore
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool
                  sourceInlineConstantsFuel := by
                    intro fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceInlineConstants := by
                    change
                      L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          [] source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceRewriteSuperCallsFuel := by
                    intro contractName fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteSuperCalls := by
                    intro contractName
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                          contractName
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteBaseCallsFuel := by
                    intro baseNames fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceRewriteBaseCalls := by
                    intro baseNames
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                          baseNames
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceAnnotatedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceAnnotated := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                          L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                          env source = source
                    cases L00_SourceSolidity.Executable.defaultAnnotateAbiFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceEnumsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceEnumsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceStructsResolvedFuel := by
                    intro fuel env typeEnv
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceStructsResolved := by
                    intro env typeEnv
                    change
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceSelectorsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceSelectorsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                          L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceFunctionAddressesResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceFunctionAddressesResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                          L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceInterfaceIdsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  sourceInterfaceIdsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                          L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  returnCoreWithInternalCalls := by
                    intro env functions returnTys
                    simpa [source, core] using
                      binaryLt_returnCoreWithInternalCalls
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool env functions [] returnTys
                  targetCoreExpr := targetCoreExpr
                  targetCore := by
                    simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.ltOp,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore]
                  targetValueEval := hTargetValueEval
                  sourceValueEvalChecked := by
                    intro context runtime hChecked
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    rw [rhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEval := by
                    intro runtime
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEval runtime]
                    rw [rhsChecked.sourceValueEval runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEvalWithRuntimeChecked := by
                    intro context runtime hChecked
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            context runtime rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            context.checked
                            SolidCore.Solidity.Source.BinaryOp.lt
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEvalWithRuntime := by
                    intro runtime
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntime runtime]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            SolidCore.Solidity.Source.Context.empty runtime
                            rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            SolidCore.Solidity.Source.Context.empty.checked
                            SolidCore.Solidity.Source.BinaryOp.lt
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntime runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      SolidCore.Solidity.Source.Context.empty, value] }
          else
            none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.gt lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          if hNotFolded : sourceBinaryGtNotFolded? source = some () then
              let value :=
                SharedSemantics.gtWord
                  lhsChecked.value rhsChecked.value
              let expr :=
                L01_ValidSolidity.Expr.gtOp
                  lhsChecked.expr rhsChecked.expr
              let core :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.gt
                  lhsChecked.core rhsChecked.core
              let targetCoreExpr :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.gt
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                norm_gtWord lhsChecked.value rhsChecked.value
              have hRat :
                  L00_SourceSolidity.Executable.Expr.numberLiteralRat?
                    source = none :=
                sourceBinaryGtNotFolded?_rat_none hNotFolded
              have hBool :
                  L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                    source = none :=
                sourceBinaryGtNotFolded?_bool_none hNotFolded
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                simp [SolidCore.Solidity.Source.BinaryOp.apply,
                  SolidCore.Solidity.Source.BinaryOp.applyWord, value]
              some
                { expr := expr
                  resultTy := by
                    rfl
                  value := value
                  valueNorm := hValueNorm
                  eval := by
                    unfold L01_ValidSolidity.Expr.Eval
                    simp [expr, L01_ValidSolidity.Expr.gtOp,
                      L01_ValidSolidity.Expr.eval?,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore,
                      L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                      L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                    change
                      (match
                          SolidCore.Solidity.Source.Expr.eval
                            SolidCore.Solidity.Source.Context.empty
                            (SolidCore.Solidity.Source.Runtime.ofState
                              SolidCore.Solidity.Source.State.empty)
                            targetCoreExpr with
                      | Except.ok coreValue =>
                          L00_SourceSolidity.Executable.CoreValue.asWord?
                            coreValue
                      | Except.error _ => none) = some value
                    rw [hTargetValueEval]
                    simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                      SolidCore.Solidity.Source.Value.asWord?,
                      hValueNorm]
                  core := core
                  sourceCore := by
                    simpa [source, core] using
                      binaryGt_sourceCore
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool
                  sourceInlineConstantsFuel := by
                    intro fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceInlineConstants := by
                    change
                      L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          [] source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceRewriteSuperCallsFuel := by
                    intro contractName fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteSuperCalls := by
                    intro contractName
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                          contractName
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteBaseCallsFuel := by
                    intro baseNames fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceRewriteBaseCalls := by
                    intro baseNames
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                          baseNames
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceAnnotatedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceAnnotated := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                          L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                          env source = source
                    cases L00_SourceSolidity.Executable.defaultAnnotateAbiFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceEnumsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceEnumsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceStructsResolvedFuel := by
                    intro fuel env typeEnv
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceStructsResolved := by
                    intro env typeEnv
                    change
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceSelectorsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceSelectorsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                          L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceFunctionAddressesResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceFunctionAddressesResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                          L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceInterfaceIdsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  sourceInterfaceIdsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                          L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  returnCoreWithInternalCalls := by
                    intro env functions returnTys
                    simpa [source, core] using
                      binaryGt_returnCoreWithInternalCalls
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool env functions [] returnTys
                  targetCoreExpr := targetCoreExpr
                  targetCore := by
                    simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.gtOp,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore]
                  targetValueEval := hTargetValueEval
                  sourceValueEvalChecked := by
                    intro context runtime hChecked
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    rw [rhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEval := by
                    intro runtime
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEval runtime]
                    rw [rhsChecked.sourceValueEval runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEvalWithRuntimeChecked := by
                    intro context runtime hChecked
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            context runtime rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            context.checked
                            SolidCore.Solidity.Source.BinaryOp.gt
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord, value]
                  sourceValueEvalWithRuntime := by
                    intro runtime
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntime runtime]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            SolidCore.Solidity.Source.Context.empty runtime
                            rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            SolidCore.Solidity.Source.Context.empty.checked
                            SolidCore.Solidity.Source.BinaryOp.gt
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntime runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      SolidCore.Solidity.Source.Context.empty, value] }
          else
            none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary L00_SourceSolidity.BinaryOp.eq lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs
      match compileExprChecked? lhs, compileExprChecked? rhs with
      | some lhsChecked, some rhsChecked =>
          if hNotFolded : sourceBinaryEqNotFolded? source = some () then
              let value :=
                SharedSemantics.eqWord
                  lhsChecked.value rhsChecked.value
              let expr :=
                L01_ValidSolidity.Expr.eqOp
                  lhsChecked.expr rhsChecked.expr
              let core :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.eq
                  lhsChecked.core rhsChecked.core
              let targetCoreExpr :=
                SolidCore.Solidity.Source.Expr.binary
                  SolidCore.Solidity.Source.BinaryOp.eq
                  lhsChecked.targetCoreExpr rhsChecked.targetCoreExpr
              have hValueNorm : SharedSemantics.norm value = value :=
                norm_eqWord lhsChecked.value rhsChecked.value
              have hRat :
                  L00_SourceSolidity.Executable.Expr.numberLiteralRat?
                    source = none :=
                sourceBinaryEqNotFolded?_rat_none hNotFolded
              have hBool :
                  L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                    source = none :=
                sourceBinaryEqNotFolded?_bool_none hNotFolded
              have hTargetValueEval :
                  SolidCore.Solidity.Source.Expr.eval
                      SolidCore.Solidity.Source.Context.empty
                      (SolidCore.Solidity.Source.Runtime.ofState
                        SolidCore.Solidity.Source.State.empty)
                      targetCoreExpr =
                    Except.ok
                      (SolidCore.Solidity.Source.Value.word value) := by
                simp [targetCoreExpr, SolidCore.Solidity.Source.Expr.eval]
                rw [lhsChecked.targetValueEval]
                rw [rhsChecked.targetValueEval]
                simp [SolidCore.Solidity.Source.BinaryOp.apply,
                  SolidCore.Solidity.Source.BinaryOp.applyWord,
                  boolWord_wordEq_eqWord, value]
              some
                { expr := expr
                  resultTy := by
                    rfl
                  value := value
                  valueNorm := hValueNorm
                  eval := by
                    unfold L01_ValidSolidity.Expr.Eval
                    simp [expr, L01_ValidSolidity.Expr.eqOp,
                      L01_ValidSolidity.Expr.eval?,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore,
                      L00_SourceSolidity.Executable.CoreExpr.evalWordInEmptyContext?,
                      L00_SourceSolidity.Executable.CoreExpr.evalWord?]
                    change
                      (match
                          SolidCore.Solidity.Source.Expr.eval
                            SolidCore.Solidity.Source.Context.empty
                            (SolidCore.Solidity.Source.Runtime.ofState
                              SolidCore.Solidity.Source.State.empty)
                            targetCoreExpr with
                      | Except.ok coreValue =>
                          L00_SourceSolidity.Executable.CoreValue.asWord?
                            coreValue
                      | Except.error _ => none) = some value
                    rw [hTargetValueEval]
                    simp [L00_SourceSolidity.Executable.CoreValue.asWord?,
                      SolidCore.Solidity.Source.Value.asWord?,
                      hValueNorm]
                  core := core
                  sourceCore := by
                    simpa [source, core] using
                      binaryEq_sourceCore
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool
                  sourceInlineConstantsFuel := by
                    intro fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceInlineConstants := by
                    change
                      L00_SourceSolidity.Executable.Expr.inlineConstantsFuel
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          [] source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.inlineConstantsFuel,
                          lhsChecked.sourceInlineConstantsFuel fuel,
                          rhsChecked.sourceInlineConstantsFuel fuel]
                  sourceRewriteSuperCallsFuel := by
                    intro contractName fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteSuperCalls := by
                    intro contractName
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel
                          contractName
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteSuperCallsFuel,
                          lhsChecked.sourceRewriteSuperCallsFuel contractName fuel,
                          rhsChecked.sourceRewriteSuperCallsFuel contractName fuel]
                  sourceRewriteBaseCallsFuel := by
                    intro baseNames fuel
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceRewriteBaseCalls := by
                    intro baseNames
                    change
                      L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel
                          baseNames
                          L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                          source = source
                    cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.rewriteBaseCallsFuel,
                          lhsChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                          rhsChecked.sourceRewriteBaseCallsFuel baseNames fuel]
                  sourceAnnotatedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceAnnotated := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.annotateAbiFuel
                          L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                          env source = source
                    cases L00_SourceSolidity.Executable.defaultAnnotateAbiFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.annotateAbiFuel,
                          lhsChecked.sourceAnnotatedFuel fuel env,
                          rhsChecked.sourceAnnotatedFuel fuel env]
                  sourceResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveUserTypesFuel,
                          lhsChecked.sourceResolvedFuel fuel env,
                          rhsChecked.sourceResolvedFuel fuel env]
                  sourceEnumsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceEnumsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveEnumsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveEnumsFuel,
                          lhsChecked.sourceEnumsResolvedFuel fuel env,
                          rhsChecked.sourceEnumsResolvedFuel fuel env]
                  sourceStructsResolvedFuel := by
                    intro fuel env typeEnv
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceStructsResolved := by
                    intro env typeEnv
                    change
                      L00_SourceSolidity.Executable.Expr.resolveStructsFuel
                          L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                          env typeEnv source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveUserTypesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveStructsFuel,
                          lhsChecked.sourceStructsResolvedFuel fuel env typeEnv,
                          rhsChecked.sourceStructsResolvedFuel fuel env typeEnv]
                  sourceSelectorsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceSelectorsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel
                          L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                          lhsChecked.sourceSelectorsResolvedFuel fuel env,
                          rhsChecked.sourceSelectorsResolvedFuel fuel env]
                  sourceFunctionAddressesResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceFunctionAddressesResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel
                          L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                          lhsChecked.sourceFunctionAddressesResolvedFuel fuel env,
                          rhsChecked.sourceFunctionAddressesResolvedFuel fuel env]
                  sourceInterfaceIdsResolvedFuel := by
                    intro fuel env
                    cases fuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  sourceInterfaceIdsResolved := by
                    intro env
                    change
                      L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel
                          L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                          env source =
                        source
                    cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                    | zero =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel]
                    | succ fuel =>
                        simp [source,
                          L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                          lhsChecked.sourceInterfaceIdsResolvedFuel fuel env,
                          rhsChecked.sourceInterfaceIdsResolvedFuel fuel env]
                  returnCoreWithInternalCalls := by
                    intro env functions returnTys
                    simpa [source, core] using
                      binaryEq_returnCoreWithInternalCalls
                        (hLhs := lhsChecked.sourceCore)
                        (hRhs := rhsChecked.sourceCore)
                        hRat hBool env functions [] returnTys
                  targetCoreExpr := targetCoreExpr
                  targetCore := by
                    simp [expr, targetCoreExpr, L01_ValidSolidity.Expr.eqOp,
                      L01_ValidSolidity.Expr.toCore?,
                      L01_ValidSolidity.BinaryOp.toCore?,
                      L01_ValidSolidity.Ty.bool,
                      lhsChecked.targetCore, rhsChecked.targetCore]
                  targetValueEval := hTargetValueEval
                  sourceValueEvalChecked := by
                    intro context runtime hChecked
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    rw [rhsChecked.sourceValueEvalChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      boolWord_wordEq_eqWord, value]
                  sourceValueEval := by
                    intro runtime
                    simp [core, SolidCore.Solidity.Source.Expr.eval]
                    rw [lhsChecked.sourceValueEval runtime]
                    rw [rhsChecked.sourceValueEval runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      boolWord_wordEq_eqWord, value]
                  sourceValueEvalWithRuntimeChecked := by
                    intro context runtime hChecked
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            context runtime rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            context.checked
                            SolidCore.Solidity.Source.BinaryOp.eq
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      boolWord_wordEq_eqWord, value]
                  sourceValueEvalWithRuntime := by
                    intro runtime
                    simp [core,
                      SolidCore.Solidity.Source.Expr.evalWithRuntime]
                    rw [lhsChecked.sourceValueEvalWithRuntime runtime]
                    change
                      (do
                        let rhsValue ←
                          SolidCore.Solidity.Source.Expr.evalWithRuntime
                            SolidCore.Solidity.Source.Context.empty runtime
                            rhsChecked.core
                        let applied ←
                          SolidCore.Solidity.Source.BinaryOp.apply
                            SolidCore.Solidity.Source.Context.empty.checked
                            SolidCore.Solidity.Source.BinaryOp.eq
                            (SolidCore.Solidity.Source.Value.word
                              lhsChecked.value)
                            rhsValue.fst
                        Except.ok (applied, rhsValue.snd)) =
                        Except.ok
                          (SolidCore.Solidity.Source.Value.word value,
                            runtime)
                    rw [rhsChecked.sourceValueEvalWithRuntime runtime]
                    simp [SolidCore.Solidity.Source.BinaryOp.apply,
                      SolidCore.Solidity.Source.BinaryOp.applyWord,
                      SolidCore.Solidity.Source.Context.empty,
                      boolWord_wordEq_eqWord, value] }
          else
            none
      | _, _ => none
  | _ => none

def compileExpr? (expr : L00_SourceSolidity.Expr) :
    Option L01_ValidSolidity.Expr :=
  match compileExprChecked? expr with
  | some checked => some checked.expr
  | none => none

structure CheckedStmt
    (functions : List L00_SourceSolidity.FunctionDecl)
    (source : L00_SourceSolidity.Stmt) where
  stmt : L01_ValidSolidity.Stmt
  returnedExpr : L01_ValidSolidity.Expr
  value : L01_ValidSolidity.Word
  valueNorm : SharedSemantics.norm value = value
  returned : stmt.returnedExpr? = some returnedExpr
  eval : returnedExpr.Eval value
  core : CoreStmt
  sourceCore :
    ∀ availableFunctions env returnTys,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv := [])
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := availableFunctions)
          (freeFunctions := [])
          (returnTys := returnTys)
          (stmt := source) = some core
  sourceInlineConstantsFuel :
    ∀ fuel,
      L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel
          fuel [] source = source
  sourceInlineConstants :
    L00_SourceSolidity.Executable.Stmt.inlineConstants [] source = source
  sourceRewriteSuperCallsFuel :
    ∀ contractName fuel,
      L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel
          contractName fuel source = source
  sourceRewriteSuperCalls :
    ∀ contractName,
      L00_SourceSolidity.Executable.Stmt.rewriteSuperCalls
          contractName source = source
  sourceRewriteBaseCallsFuel :
    ∀ baseNames fuel,
      L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel
          baseNames fuel source = source
  sourceRewriteBaseCalls :
    ∀ baseNames,
      L00_SourceSolidity.Executable.Stmt.rewriteBaseCalls baseNames source =
        source
  sourceAnnotatedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
          fuel env source = source
  sourceAnnotatedInSeqFuel :
    ∀ fuel env,
      (L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel
          fuel env source).fst = source
  sourceAnnotated :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.annotateAbi env source = source
  sourceResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
          fuel env source =
        source
  sourceResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.resolveUserTypes env source =
        source
  sourceEnumsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
          fuel env source =
        source
  sourceEnumsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.resolveEnums env source =
        source
  sourceStructsResolvedInSeqFuel :
    ∀ fuel env typeEnv,
      (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
          fuel env typeEnv source).fst =
        source
  sourceStructsResolved :
    ∀ env typeEnv,
      L00_SourceSolidity.Executable.Stmt.resolveStructs env typeEnv source =
        source
  sourceInterfaceIdsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel
          fuel env source =
        source
  sourceInterfaceIdsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.resolveInterfaceIds env source =
        source
  sourceSelectorsResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel
          fuel env source =
        source
  sourceSelectorsResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.resolveSelectors env source =
        source
  sourceFunctionAddressesResolvedFuel :
    ∀ fuel env,
      L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel
          fuel env source =
        source
  sourceFunctionAddressesResolved :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.resolveFunctionAddresses env source =
        source
  sourceListCore :
    ∀ availableFunctions env returnTys,
      L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?
          env [] [] availableFunctions [] returnTys [source] = some [core]
  sourceFuel : Nat
  sourceEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Stmt.eval sourceFuel
          SolidCore.Solidity.Source.Context.empty runtime core =
        some
          (SolidCore.Solidity.Source.Result.returned runtime
            [SolidCore.Solidity.Source.Value.word value])
  sourceEvalChecked :
    ∀ context runtime,
      context.checked = true ->
        SolidCore.Solidity.Source.Stmt.eval sourceFuel
            context runtime core =
          some
            (SolidCore.Solidity.Source.Result.returned runtime
              [SolidCore.Solidity.Source.Value.word value])

def compileStmtChecked? (functions : List L00_SourceSolidity.FunctionDecl) :
    (source : L00_SourceSolidity.Stmt) -> Option (CheckedStmt functions source)
  | L00_SourceSolidity.Stmt.returnValues (some sourceExpr) =>
      match compileExprChecked? sourceExpr with
      | some checked =>
          let core :=
            SolidCore.Solidity.Source.Stmt.returnValues [checked.core]
          have hAnnotatedInSeq :
              ∀ fuel env,
                (L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr))).fst =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.eq_1]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel,
                  checked.sourceAnnotatedFuel]
          have hAnnotatedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)) =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro fuel env
            simpa [L00_SourceSolidity.Executable.Stmt.annotateAbiFuel.eq_1]
              using hAnnotatedInSeq fuel env
          have hAnnotated :
              ∀ env,
                L00_SourceSolidity.Executable.Stmt.annotateAbi env
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)) =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro env
            change
              L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                  env
                  (L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr)) =
                L00_SourceSolidity.Stmt.returnValues
                  (some sourceExpr)
            exact hAnnotatedFuel
              L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
          have hResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)) =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel,
                  checked.sourceResolvedFuel fuel env]
          have hEnumsResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)) =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel,
                  checked.sourceEnumsResolvedFuel fuel env]
          have hStructsResolvedInSeqFuel :
              ∀ fuel env typeEnv,
                (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                    fuel env typeEnv
                    (L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr))).fst =
                  L00_SourceSolidity.Stmt.returnValues
                    (some sourceExpr) := by
            intro fuel env typeEnv
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel,
                  checked.sourceStructsResolvedFuel fuel env typeEnv]
          some
            { stmt := L01_ValidSolidity.Stmt.returnExpr checked.expr
              returnedExpr := checked.expr
              value := checked.value
              valueNorm := checked.valueNorm
              returned := by rfl
              eval := checked.eval
              core := core
              sourceCore := by
                intro availableFunctions env returnTys
                exact
                  checked.returnCoreWithInternalCalls
                    env availableFunctions returnTys
              sourceInlineConstantsFuel := by
                intro fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                      checked.sourceInlineConstantsFuel fuel]
              sourceInlineConstants := by
                change
                  L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      []
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                      checked.sourceInlineConstantsFuel fuel]
              sourceRewriteSuperCallsFuel := by
                intro contractName fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel,
                      checked.sourceRewriteSuperCallsFuel contractName fuel]
              sourceRewriteSuperCalls := by
                intro contractName
                change
                  L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel
                      contractName
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel,
                      checked.sourceRewriteSuperCallsFuel contractName fuel]
              sourceRewriteBaseCallsFuel := by
                intro baseNames fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel,
                      checked.sourceRewriteBaseCallsFuel baseNames fuel]
              sourceRewriteBaseCalls := by
                intro baseNames
                change
                  L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel
                      baseNames
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel,
                      checked.sourceRewriteBaseCallsFuel baseNames fuel]
              sourceAnnotatedFuel := hAnnotatedFuel
              sourceAnnotatedInSeqFuel := hAnnotatedInSeq
              sourceAnnotated := hAnnotated
              sourceResolvedFuel := hResolvedFuel
              sourceResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)
                exact hResolvedFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
              sourceEnumsResolvedFuel := hEnumsResolvedFuel
              sourceEnumsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)
                exact hEnumsResolvedFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
              sourceStructsResolvedInSeqFuel := hStructsResolvedInSeqFuel
              sourceStructsResolved := by
                intro env typeEnv
                change
                  (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env typeEnv
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr))).fst =
                    L00_SourceSolidity.Stmt.returnValues
                      (some sourceExpr)
                exact hStructsResolvedInSeqFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                  env typeEnv
              sourceInterfaceIdsResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                      checked.sourceInterfaceIdsResolvedFuel fuel env]
              sourceInterfaceIdsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel
                      L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                      env
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                      checked.sourceInterfaceIdsResolvedFuel fuel env]
              sourceSelectorsResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                      checked.sourceSelectorsResolvedFuel fuel env]
              sourceSelectorsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel
                      L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                      env
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                      checked.sourceSelectorsResolvedFuel fuel env]
              sourceFunctionAddressesResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                      checked.sourceFunctionAddressesResolvedFuel fuel env]
              sourceFunctionAddressesResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel
                      L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                      env
                      (L00_SourceSolidity.Stmt.returnValues
                        (some sourceExpr)) =
                    L00_SourceSolidity.Stmt.returnValues (some sourceExpr)
                cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                      checked.sourceFunctionAddressesResolvedFuel fuel env]
              sourceListCore := by
                intro availableFunctions env returnTys
                simp [
                  core,
                  L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?,
                  L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?,
                  checked.returnCoreWithInternalCalls
                    env availableFunctions returnTys]
              sourceFuel := 1
              sourceEval := by
                intro runtime
                simp [core, SolidCore.Solidity.Source.Stmt.eval,
                  SolidCore.Solidity.Source.Expr.evalListWithRuntime]
                rw [checked.sourceValueEvalWithRuntime runtime]
                all_goals rfl
              sourceEvalChecked := by
                intro context runtime hChecked
                simp [core, SolidCore.Solidity.Source.Stmt.eval,
                  SolidCore.Solidity.Source.Expr.evalListWithRuntime]
                rw [checked.sourceValueEvalWithRuntimeChecked
                  context runtime hChecked]
                all_goals rfl }
      | none => none
  | L00_SourceSolidity.Stmt.block [sourceStmt] =>
      match compileStmtChecked? functions sourceStmt with
      | some checked =>
          let core :=
            SolidCore.Solidity.Source.Stmt.block [checked.core]
          have hAnnotatedInSeq :
              ∀ fuel env,
                (L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.block [sourceStmt])).fst =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.eq_1]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.eq_3,
                  L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.annotateSeq.eq_1,
                  L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.annotateSeq.eq_2,
                  checked.sourceAnnotatedInSeqFuel]
          have hAnnotatedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro fuel env
            simpa [L00_SourceSolidity.Executable.Stmt.annotateAbiFuel.eq_1]
              using hAnnotatedInSeq fuel env
          have hAnnotated :
              ∀ env,
                L00_SourceSolidity.Executable.Stmt.annotateAbi env
                    (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro env
            change
              L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                  env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                L00_SourceSolidity.Stmt.block [sourceStmt]
            exact hAnnotatedFuel
              L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
          have hResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel,
                  checked.sourceResolvedFuel fuel env]
          have hEnumsResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel,
                  checked.sourceEnumsResolvedFuel fuel env]
          have hStructsResolvedInSeqFuel :
              ∀ fuel env typeEnv,
                (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                    fuel env typeEnv
                    (L00_SourceSolidity.Stmt.block [sourceStmt])).fst =
                  L00_SourceSolidity.Stmt.block [sourceStmt] := by
            intro fuel env typeEnv
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel,
                  L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel.resolveSeq.eq_1,
                  L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel.resolveSeq.eq_2,
                  checked.sourceStructsResolvedInSeqFuel fuel env typeEnv]
          some
            { stmt := L01_ValidSolidity.Stmt.block [] [checked.stmt]
              returnedExpr := checked.returnedExpr
              value := checked.value
              valueNorm := checked.valueNorm
              returned := by
                simp [L01_ValidSolidity.Stmt.returnedExpr?,
                  checked.returned]
              eval := checked.eval
              core := core
              sourceCore := by
                intro availableFunctions env returnTys
                have hBody :
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?
                        L00_SourceSolidity.Executable.defaultInternalCallInlineFuel
                        [] env [] [] availableFunctions [] returnTys [sourceStmt] =
                      some [checked.core] := by
                  simpa
                    [L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?]
                    using checked.sourceListCore
                      availableFunctions env returnTys
                simp [core,
                  L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                  L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?,
                  hBody]
              sourceInlineConstantsFuel := by
                intro fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                      checked.sourceInlineConstantsFuel fuel]
              sourceInlineConstants := by
                change
                  L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      [] (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                      checked.sourceInlineConstantsFuel fuel]
              sourceRewriteSuperCallsFuel := by
                intro contractName fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel,
                      checked.sourceRewriteSuperCallsFuel contractName fuel]
              sourceRewriteSuperCalls := by
                intro contractName
                change
                  L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel
                      contractName
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel,
                      checked.sourceRewriteSuperCallsFuel contractName fuel]
              sourceRewriteBaseCallsFuel := by
                intro baseNames fuel
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel,
                      checked.sourceRewriteBaseCallsFuel baseNames fuel]
              sourceRewriteBaseCalls := by
                intro baseNames
                change
                  L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel
                      baseNames
                      L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                      (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel,
                      checked.sourceRewriteBaseCallsFuel baseNames fuel]
              sourceAnnotatedFuel := hAnnotatedFuel
              sourceAnnotatedInSeqFuel := hAnnotatedInSeq
              sourceAnnotated := hAnnotated
              sourceResolvedFuel := hResolvedFuel
              sourceResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                exact hResolvedFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
              sourceEnumsResolvedFuel := hEnumsResolvedFuel
              sourceEnumsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                exact hEnumsResolvedFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel env
              sourceStructsResolvedInSeqFuel := hStructsResolvedInSeqFuel
              sourceStructsResolved := by
                intro env typeEnv
                change
                  (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                      L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                      env typeEnv
                      (L00_SourceSolidity.Stmt.block [sourceStmt])).fst =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                exact hStructsResolvedInSeqFuel
                  L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                  env typeEnv
              sourceInterfaceIdsResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                      checked.sourceInterfaceIdsResolvedFuel fuel env]
              sourceInterfaceIdsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel
                      L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                      env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                      checked.sourceInterfaceIdsResolvedFuel fuel env]
              sourceSelectorsResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                      checked.sourceSelectorsResolvedFuel fuel env]
              sourceSelectorsResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel
                      L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                      env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                      checked.sourceSelectorsResolvedFuel fuel env]
              sourceFunctionAddressesResolvedFuel := by
                intro fuel env
                cases fuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                      checked.sourceFunctionAddressesResolvedFuel fuel env]
              sourceFunctionAddressesResolved := by
                intro env
                change
                  L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel
                      L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                      env (L00_SourceSolidity.Stmt.block [sourceStmt]) =
                    L00_SourceSolidity.Stmt.block [sourceStmt]
                cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                | zero =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                | succ fuel =>
                    simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                      checked.sourceFunctionAddressesResolvedFuel fuel env]
              sourceListCore := by
                  intro availableFunctions env returnTys
                  have hBody :
                      L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?
                          L00_SourceSolidity.Executable.defaultInternalCallInlineFuel
                          [] env [] [] availableFunctions [] returnTys [sourceStmt] =
                        some [checked.core] := by
                    simpa
                      [L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?]
                      using checked.sourceListCore
                        availableFunctions env returnTys
                  simp [core,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?,
                    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                    hBody]
              sourceFuel := checked.sourceFuel + 1
              sourceEval := by
                intro runtime
                simp [core, SolidCore.Solidity.Source.Stmt.eval,
                  SolidCore.Solidity.Source.Stmt.evalList]
                rw [checked.sourceEval
                  (SolidCore.Solidity.Source.Runtime.pushScope runtime)]
                simp [SolidCore.Solidity.Source.Result.mapRuntime,
                  SolidCore.Solidity.Source.Runtime.pushScope,
                  SolidCore.Solidity.Source.Runtime.popScope]
              sourceEvalChecked := by
                intro context runtime hChecked
                simp [core, SolidCore.Solidity.Source.Stmt.eval,
                  SolidCore.Solidity.Source.Stmt.evalList]
                rw [checked.sourceEvalChecked context
                  (SolidCore.Solidity.Source.Runtime.pushScope runtime)
                  hChecked]
                simp [SolidCore.Solidity.Source.Result.mapRuntime,
                  SolidCore.Solidity.Source.Runtime.pushScope,
                  SolidCore.Solidity.Source.Runtime.popScope] }
      | none => none
  | L00_SourceSolidity.Stmt.ifElse condition thenBranch (some elseBranch) =>
      match compileBoolExprChecked? condition,
          compileStmtChecked? functions thenBranch,
          compileStmtChecked? functions elseBranch with
      | some conditionChecked, some thenChecked, some elseChecked =>
          have hAnnotatedInSeq :
              ∀ fuel env,
                (L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch))).fst =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.eq_1]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.annotateAbiInSeqFuel.eq_6,
                  conditionChecked.sourceAnnotatedFuel,
                  thenChecked.sourceAnnotatedInSeqFuel,
                  elseChecked.sourceAnnotatedInSeqFuel]
          have hAnnotatedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro fuel env
            simpa [L00_SourceSolidity.Executable.Stmt.annotateAbiFuel.eq_1]
              using hAnnotatedInSeq fuel env
          have hAnnotated :
              ∀ env,
                L00_SourceSolidity.Executable.Stmt.annotateAbi env
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro env
            change
              L00_SourceSolidity.Executable.Stmt.annotateAbiFuel
                  L00_SourceSolidity.Executable.defaultAnnotateAbiFuel
                  env
                  (L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch)) =
                L00_SourceSolidity.Stmt.ifElse
                  condition thenBranch (some elseBranch)
            exact hAnnotatedFuel
              L00_SourceSolidity.Executable.defaultAnnotateAbiFuel env
          have hResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel,
                  conditionChecked.sourceResolvedFuel fuel env,
                  thenChecked.sourceResolvedFuel fuel env,
                  elseChecked.sourceResolvedFuel fuel env]
          have hEnumsResolvedFuel :
              ∀ fuel env,
                L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                    fuel env
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro fuel env
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel,
                  conditionChecked.sourceEnumsResolvedFuel fuel env,
                  thenChecked.sourceEnumsResolvedFuel fuel env,
                  elseChecked.sourceEnumsResolvedFuel fuel env]
          have hStructsResolvedInSeqFuel :
              ∀ fuel env typeEnv,
                (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                    fuel env typeEnv
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch))).fst =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro fuel env typeEnv
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel,
                  conditionChecked.sourceStructsResolvedFuel fuel env typeEnv,
                  thenChecked.sourceStructsResolvedInSeqFuel fuel env typeEnv,
                  elseChecked.sourceStructsResolvedInSeqFuel fuel env typeEnv]
          have hRewriteSuperFuel :
              ∀ contractName fuel,
                L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel
                    contractName fuel
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro contractName fuel
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel,
                  conditionChecked.sourceRewriteSuperCallsFuel contractName fuel,
                  thenChecked.sourceRewriteSuperCallsFuel contractName fuel,
                  elseChecked.sourceRewriteSuperCallsFuel contractName fuel]
          have hRewriteSuper :
              ∀ contractName,
              L00_SourceSolidity.Executable.Stmt.rewriteSuperCalls
                  contractName
                  (L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch)) =
                L00_SourceSolidity.Stmt.ifElse
                  condition thenBranch (some elseBranch) := by
            intro contractName
            change
              L00_SourceSolidity.Executable.Stmt.rewriteSuperCallsFuel
                  contractName
                  L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                  (L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch)) =
                L00_SourceSolidity.Stmt.ifElse
                  condition thenBranch (some elseBranch)
            exact hRewriteSuperFuel
              contractName L00_SourceSolidity.Executable.defaultInlineConstantsFuel
          have hRewriteBaseFuel :
              ∀ baseNames fuel,
                L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel
                    baseNames fuel
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro baseNames fuel
            cases fuel with
            | zero =>
                simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel]
            | succ fuel =>
                simp [L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel,
                  conditionChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                  thenChecked.sourceRewriteBaseCallsFuel baseNames fuel,
                  elseChecked.sourceRewriteBaseCallsFuel baseNames fuel]
          have hRewriteBase :
              ∀ baseNames,
                L00_SourceSolidity.Executable.Stmt.rewriteBaseCalls
                    baseNames
                    (L00_SourceSolidity.Stmt.ifElse
                      condition thenBranch (some elseBranch)) =
                  L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch) := by
            intro baseNames
            change
              L00_SourceSolidity.Executable.Stmt.rewriteBaseCallsFuel
                  baseNames
                  L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                  (L00_SourceSolidity.Stmt.ifElse
                    condition thenBranch (some elseBranch)) =
                L00_SourceSolidity.Stmt.ifElse
                  condition thenBranch (some elseBranch)
            exact hRewriteBaseFuel
              baseNames L00_SourceSolidity.Executable.defaultInlineConstantsFuel
          if hCondition :
              SolidCore.Solidity.Source.wordTruthy
                conditionChecked.value then
            let core :=
              SolidCore.Solidity.Source.Stmt.ifElse
                conditionChecked.core thenChecked.core elseChecked.core
            some
              { stmt :=
                  L01_ValidSolidity.Stmt.ifElse conditionChecked.expr
                    thenChecked.stmt elseChecked.stmt
                returnedExpr := thenChecked.returnedExpr
                value := thenChecked.value
                valueNorm := thenChecked.valueNorm
                returned := by
                  have hEval := conditionChecked.eval
                  unfold L01_ValidSolidity.Expr.Eval at hEval
                  simp [L01_ValidSolidity.Stmt.returnedExpr?, hEval,
                    hCondition, thenChecked.returned]
                eval := thenChecked.eval
                core := core
                sourceCore := by
                  intro availableFunctions env returnTys
                  simp [core,
                    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                    conditionChecked.sourceCore,
                    thenChecked.sourceCore availableFunctions env returnTys,
                    elseChecked.sourceCore availableFunctions env returnTys]
                sourceInlineConstantsFuel := by
                  intro fuel
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                        conditionChecked.sourceInlineConstantsFuel fuel,
                        thenChecked.sourceInlineConstantsFuel fuel,
                        elseChecked.sourceInlineConstantsFuel fuel]
                sourceInlineConstants := by
                  change
                    L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel
                        L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                        []
                        (L00_SourceSolidity.Stmt.ifElse condition
                          thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse condition thenBranch
                        (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                        conditionChecked.sourceInlineConstantsFuel fuel,
                        thenChecked.sourceInlineConstantsFuel fuel,
                        elseChecked.sourceInlineConstantsFuel fuel]
                sourceRewriteSuperCallsFuel := hRewriteSuperFuel
                sourceRewriteSuperCalls := hRewriteSuper
                sourceRewriteBaseCallsFuel := hRewriteBaseFuel
                sourceRewriteBaseCalls := hRewriteBase
                sourceAnnotatedFuel := hAnnotatedFuel
                sourceAnnotatedInSeqFuel := hAnnotatedInSeq
                sourceAnnotated := hAnnotated
                sourceResolvedFuel := hResolvedFuel
                sourceResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hResolvedFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env
                sourceEnumsResolvedFuel := hEnumsResolvedFuel
                sourceEnumsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hEnumsResolvedFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env
                sourceStructsResolvedInSeqFuel := hStructsResolvedInSeqFuel
                sourceStructsResolved := by
                  intro env typeEnv
                  change
                    (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env typeEnv
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch))).fst =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hStructsResolvedInSeqFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env typeEnv
                sourceInterfaceIdsResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                        conditionChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        thenChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        elseChecked.sourceInterfaceIdsResolvedFuel fuel env]
                sourceInterfaceIdsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel
                        L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                        conditionChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        thenChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        elseChecked.sourceInterfaceIdsResolvedFuel fuel env]
                sourceSelectorsResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                        conditionChecked.sourceSelectorsResolvedFuel fuel env,
                        thenChecked.sourceSelectorsResolvedFuel fuel env,
                        elseChecked.sourceSelectorsResolvedFuel fuel env]
                sourceSelectorsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel
                        L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                        conditionChecked.sourceSelectorsResolvedFuel fuel env,
                        thenChecked.sourceSelectorsResolvedFuel fuel env,
                        elseChecked.sourceSelectorsResolvedFuel fuel env]
                sourceFunctionAddressesResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                        conditionChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        thenChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        elseChecked.sourceFunctionAddressesResolvedFuel fuel env]
                sourceFunctionAddressesResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel
                        L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                        conditionChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        thenChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        elseChecked.sourceFunctionAddressesResolvedFuel fuel env]
                sourceListCore := by
                  intro availableFunctions env returnTys
                  simp [core,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?,
                    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                    conditionChecked.sourceCore,
                    thenChecked.sourceCore availableFunctions env returnTys,
                    elseChecked.sourceCore availableFunctions env returnTys]
                sourceFuel := thenChecked.sourceFuel + 1
                sourceEval := by
                  intro runtime
                  simp [core, SolidCore.Solidity.Source.Stmt.eval,
                    conditionChecked.sourceValueEvalWithRuntime runtime,
                    SolidCore.Solidity.Source.Value.expectWord,
                    conditionChecked.valueNorm, hCondition,
                    thenChecked.sourceEval runtime]
                sourceEvalChecked := by
                  intro context runtime hChecked
                  simp [core, SolidCore.Solidity.Source.Stmt.eval,
                    conditionChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked,
                    SolidCore.Solidity.Source.Value.expectWord,
                    conditionChecked.valueNorm, hCondition,
                    thenChecked.sourceEvalChecked context runtime hChecked] }
          else
            let core :=
              SolidCore.Solidity.Source.Stmt.ifElse
                conditionChecked.core thenChecked.core elseChecked.core
            some
              { stmt :=
                  L01_ValidSolidity.Stmt.ifElse conditionChecked.expr
                    thenChecked.stmt elseChecked.stmt
                returnedExpr := elseChecked.returnedExpr
                value := elseChecked.value
                valueNorm := elseChecked.valueNorm
                returned := by
                  have hEval := conditionChecked.eval
                  unfold L01_ValidSolidity.Expr.Eval at hEval
                  simp [L01_ValidSolidity.Stmt.returnedExpr?, hEval,
                    hCondition, elseChecked.returned]
                eval := elseChecked.eval
                core := core
                sourceCore := by
                  intro availableFunctions env returnTys
                  simp [core,
                    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                    conditionChecked.sourceCore,
                    thenChecked.sourceCore availableFunctions env returnTys,
                    elseChecked.sourceCore availableFunctions env returnTys]
                sourceInlineConstantsFuel := by
                  intro fuel
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                        conditionChecked.sourceInlineConstantsFuel fuel,
                        thenChecked.sourceInlineConstantsFuel fuel,
                        elseChecked.sourceInlineConstantsFuel fuel]
                sourceInlineConstants := by
                  change
                    L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel
                        L00_SourceSolidity.Executable.defaultInlineConstantsFuel
                        []
                        (L00_SourceSolidity.Stmt.ifElse condition
                          thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse condition thenBranch
                        (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultInlineConstantsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.inlineConstantsFuel,
                        conditionChecked.sourceInlineConstantsFuel fuel,
                        thenChecked.sourceInlineConstantsFuel fuel,
                        elseChecked.sourceInlineConstantsFuel fuel]
                sourceRewriteSuperCallsFuel := hRewriteSuperFuel
                sourceRewriteSuperCalls := hRewriteSuper
                sourceRewriteBaseCallsFuel := hRewriteBaseFuel
                sourceRewriteBaseCalls := hRewriteBase
                sourceAnnotatedFuel := hAnnotatedFuel
                sourceAnnotatedInSeqFuel := hAnnotatedInSeq
                sourceAnnotated := hAnnotated
                sourceResolvedFuel := hResolvedFuel
                sourceResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveUserTypesFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hResolvedFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env
                sourceEnumsResolvedFuel := hEnumsResolvedFuel
                sourceEnumsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveEnumsFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hEnumsResolvedFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env
                sourceStructsResolvedInSeqFuel := hStructsResolvedInSeqFuel
                sourceStructsResolved := by
                  intro env typeEnv
                  change
                    (L00_SourceSolidity.Executable.Stmt.resolveStructsInSeqFuel
                        L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                        env typeEnv
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch))).fst =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  exact hStructsResolvedInSeqFuel
                    L00_SourceSolidity.Executable.defaultResolveUserTypesFuel
                    env typeEnv
                sourceInterfaceIdsResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                        conditionChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        thenChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        elseChecked.sourceInterfaceIdsResolvedFuel fuel env]
                sourceInterfaceIdsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel
                        L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveInterfaceIdsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                        conditionChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        thenChecked.sourceInterfaceIdsResolvedFuel fuel env,
                        elseChecked.sourceInterfaceIdsResolvedFuel fuel env]
                sourceSelectorsResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                        conditionChecked.sourceSelectorsResolvedFuel fuel env,
                        thenChecked.sourceSelectorsResolvedFuel fuel env,
                        elseChecked.sourceSelectorsResolvedFuel fuel env]
                sourceSelectorsResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel
                        L00_SourceSolidity.Executable.defaultResolveSelectorsFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveSelectorsFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                        conditionChecked.sourceSelectorsResolvedFuel fuel env,
                        thenChecked.sourceSelectorsResolvedFuel fuel env,
                        elseChecked.sourceSelectorsResolvedFuel fuel env]
                sourceFunctionAddressesResolvedFuel := by
                  intro fuel env
                  cases fuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                        conditionChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        thenChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        elseChecked.sourceFunctionAddressesResolvedFuel fuel env]
                sourceFunctionAddressesResolved := by
                  intro env
                  change
                    L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel
                        L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel
                        env
                        (L00_SourceSolidity.Stmt.ifElse
                          condition thenBranch (some elseBranch)) =
                      L00_SourceSolidity.Stmt.ifElse
                        condition thenBranch (some elseBranch)
                  cases L00_SourceSolidity.Executable.defaultResolveFunctionAddressesFuel with
                  | zero =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel]
                  | succ fuel =>
                      simp [L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                        conditionChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        thenChecked.sourceFunctionAddressesResolvedFuel fuel env,
                        elseChecked.sourceFunctionAddressesResolvedFuel fuel env]
                sourceListCore := by
                  intro availableFunctions env returnTys
                  simp [core,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCalls?,
                    L00_SourceSolidity.Executable.Stmt.listToCoreWithInternalCallsWithRefs?,
                    L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?,
                    conditionChecked.sourceCore,
                    thenChecked.sourceCore availableFunctions env returnTys,
                    elseChecked.sourceCore availableFunctions env returnTys]
                sourceFuel := elseChecked.sourceFuel + 1
                sourceEval := by
                  intro runtime
                  simp [core, SolidCore.Solidity.Source.Stmt.eval,
                    conditionChecked.sourceValueEvalWithRuntime runtime,
                    SolidCore.Solidity.Source.Value.expectWord,
                    conditionChecked.valueNorm, hCondition,
                    elseChecked.sourceEval runtime]
                sourceEvalChecked := by
                  intro context runtime hChecked
                  simp [core, SolidCore.Solidity.Source.Stmt.eval,
                    conditionChecked.sourceValueEvalWithRuntimeChecked
                      context runtime hChecked,
                    SolidCore.Solidity.Source.Value.expectWord,
                    conditionChecked.valueNorm, hCondition,
                    elseChecked.sourceEvalChecked context runtime hChecked] }
      | _, _, _ => none
  | _ => none

structure CheckedFunction (source : L00_SourceSolidity.FunctionDecl) where
  function : L01_ValidSolidity.FunctionDecl
  returnedExpr : L01_ValidSolidity.Expr
  value : L01_ValidSolidity.Word
  valueNorm : SharedSemantics.norm value = value
  returned : function.returnedExpr? = some returnedExpr
  eval : returnedExpr.Eval value
  sourceBody : L00_SourceSolidity.Stmt
  sourceBody_eq : source.body = some sourceBody
  core : CoreStmt
  sourceCore :
    ∀ env,
      L00_SourceSolidity.Executable.Stmt.toCoreWithInternalCalls?
          (internalFuel :=
            L00_SourceSolidity.Executable.defaultInternalCallInlineFuel)
          (storageRefEnv :=
            L00_SourceSolidity.Executable.Parameters.extendStorageRefEnv
              "_arg" [] source.params)
          (env := env)
          (storageNames := [])
          (modifiers := [])
          (functions := [source])
          (freeFunctions := [])
          (returnTys := source.returns.map L00_SourceSolidity.Parameter.ty)
          (stmt := sourceBody) = some core
  sourceFuel : Nat
  sourceEval :
    ∀ runtime : CoreRuntime,
      SolidCore.Solidity.Source.Stmt.eval sourceFuel
          SolidCore.Solidity.Source.Context.empty runtime core =
        some
          (SolidCore.Solidity.Source.Result.returned runtime
            [SolidCore.Solidity.Source.Value.word value])
  sourceCall :
    L00_SourceSolidity.Executable.FunctionDecl.call?
        sourceFuel [] [] SolidCore.Solidity.Source.Context.empty
        SolidCore.Solidity.Source.State.empty source [] =
      some
        (SolidCore.Solidity.Source.CallResult.returned
          SolidCore.Solidity.Source.State.empty
          [SolidCore.Solidity.Source.Value.word value])
  sourceEntryBehavior :
    ∀ contractName : L00_SourceSolidity.Name,
      L00_SourceSolidity.Executable.SourceUnit.entryBehavior?
          sourceFuel
          { items :=
              [L00_SourceSolidity.SourceItem.contract
                { kind := L00_SourceSolidity.ContractKind.contract
                  name := contractName
                  abstract := false
                  bases := []
                  items := [L00_SourceSolidity.ContractItem.function source] }] } =
        some (L00_SourceSolidity.Behavior.returnedWord value)

def compileFunctionChecked?
    : (fn : L00_SourceSolidity.FunctionDecl) ->
      Option (CheckedFunction fn)
  | fn@{ kind := L00_SourceSolidity.FunctionKind.function
         name := some _sourceName
         params := []
         returns :=
           [{ name := retName
              ty := L00_SourceSolidity.Ty.uint 256
              location := retLocation }]
         visibility := some L00_SourceSolidity.Visibility.public_
         mutability := L00_SourceSolidity.StateMutability.pure
         virtual := isVirtual
         override? := overrideSpec
         modifiers := []
         body := some body
         } =>
      match compileStmtChecked? [fn] body with
      | some checked =>
          some
            { function :=
                L01_ValidSolidity.FunctionDecl.withBody checked.stmt
              returnedExpr := checked.returnedExpr
              value := checked.value
              valueNorm := checked.valueNorm
              returned := by
                simp [L01_ValidSolidity.FunctionDecl.withBody,
                  L01_ValidSolidity.FunctionDecl.returnedExpr?,
                  L01_ValidSolidity.ReturnVar.isUint256,
                  L01_ValidSolidity.ReturnVar.word0,
                  L01_ValidSolidity.Ty.uint256,
                  L01_ValidSolidity.Ty.isUint256,
                  checked.returned]
              eval := checked.eval
              sourceBody := body
              sourceBody_eq := by rfl
              core := checked.core
              sourceCore := by
                intro env
                subst fn
                simpa using
                  checked.sourceCore
                    [ { kind := L00_SourceSolidity.FunctionKind.function
                        name := some _sourceName
                        params := []
                        returns :=
                          [{ name := retName
                             ty := L00_SourceSolidity.Ty.uint 256
                             location := retLocation }]
                        visibility := some L00_SourceSolidity.Visibility.public_
                        mutability := L00_SourceSolidity.StateMutability.pure
                        virtual := isVirtual
                        override? := overrideSpec
                        modifiers := []
                        body := some body } ]
                    env [L00_SourceSolidity.Ty.uint 256]
              sourceFuel := checked.sourceFuel
              sourceEval := checked.sourceEval
              sourceCall := by
                subst fn
                simp [L00_SourceSolidity.Executable.FunctionDecl.call?,
                  L00_SourceSolidity.Executable.FunctionDecl.toCore?,
                  L00_SourceSolidity.Executable.FunctionDecl.coreName?,
                  L00_SourceSolidity.Executable.Parameters.extendStorageRefEnv,
                  L00_SourceSolidity.Executable.Parameters.extendStorageRefEnvFrom,
                  L00_SourceSolidity.Executable.Parameters.toCoreBindings?,
                  L00_SourceSolidity.Executable.Parameter.toCoreBinding?,
                  L00_SourceSolidity.Executable.mapOptionIdx,
                    L00_SourceSolidity.Executable.Ty.toCore?,
                    L00_SourceSolidity.Executable.FunctionDecl.inlineConstants,
                    L00_SourceSolidity.Executable.FunctionDecl.resolveFunctionAddresses,
                    L00_SourceSolidity.Executable.Stmt.resolveFunctionAddresses,
                    L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                    L00_SourceSolidity.Executable.FunctionDecl.resolveSelectors,
                    L00_SourceSolidity.Executable.Stmt.resolveSelectors,
                    L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                    L00_SourceSolidity.Executable.Stmt.annotateAbi,
                    checked.sourceInlineConstants,
                    checked.sourceFunctionAddressesResolved,
                    checked.sourceFunctionAddressesResolvedFuel,
                    checked.sourceSelectorsResolved,
                    checked.sourceSelectorsResolvedFuel,
                    checked.sourceRewriteSuperCalls,
                    checked.sourceRewriteBaseCalls,
                    checked.sourceAnnotated,
                  checked.sourceAnnotatedFuel,
                  L00_SourceSolidity.Executable.FunctionDecl.superHelpers,
                  L00_SourceSolidity.Executable.functionExpandModifiersToCoreWithInternalCallsFull?,
                  L00_SourceSolidity.Executable.functionExpandModifiersToCoreWithInternalCalls?,
                  checked.sourceCore,
                  L00_SourceSolidity.Executable.ContractDecls.hasLibrary,
                  L00_SourceSolidity.Executable.ContractDecl.isLibrary,
                  SolidCore.Solidity.Source.FunctionDef.call?,
                  SolidCore.Solidity.Source.FunctionDef.initialFrame?,
                  SolidCore.Solidity.Source.BindingDecl.bindArgs?,
                  SolidCore.Solidity.Source.BindingDecl.defaultBinding]
                rw [checked.sourceEval]
                simp [SolidCore.Solidity.Source.FunctionDef.coerceReturnValues?,
                  SolidCore.Solidity.Source.Ty.coerceValue?]
                change
                  some
                    (SolidCore.Solidity.Source.CallResult.returned
                      SolidCore.Solidity.Source.State.empty
                      [SolidCore.Solidity.Source.Value.word checked.value]) =
                    some
                      (SolidCore.Solidity.Source.CallResult.returned
                        SolidCore.Solidity.Source.State.empty
                        [SolidCore.Solidity.Source.Value.word checked.value])
                rfl
              sourceEntryBehavior := by
                intro contractName
                subst fn
                simp [L00_SourceSolidity.Executable.SourceUnit.entryBehavior?,
                  L00_SourceSolidity.Executable.SourceUnit.entryNames?,
                  L00_SourceSolidity.Executable.SourceUnit.callContract?,
                  L00_SourceSolidity.Executable.SourceUnit.toCoreContract?,
                  L00_SourceSolidity.Executable.SourceUnit.resolveSourceTypes,
                  L00_SourceSolidity.Executable.SourceUnit.resolveUserTypes,
                  L00_SourceSolidity.Executable.SourceUnit.resolveEnums,
                  L00_SourceSolidity.Executable.SourceUnit.resolveStructs,
                  L00_SourceSolidity.Executable.SourceUnit.userTypeEnv,
                  L00_SourceSolidity.Executable.SourceUnit.freeUserValueTypes,
                  L00_SourceSolidity.Executable.SourceUnit.enumEnv,
                  L00_SourceSolidity.Executable.SourceUnit.freeEnums,
                  L00_SourceSolidity.Executable.SourceUnit.structEnv,
                  L00_SourceSolidity.Executable.SourceUnit.freeStructs,
                  L00_SourceSolidity.Executable.SourceUnit.freeFunctions,
                  L00_SourceSolidity.Executable.SourceUnit.freeErrors,
                  L00_SourceSolidity.Executable.SourceUnit.freeConstants,
                  L00_SourceSolidity.Executable.SourceUnit.findContract?,
                  L00_SourceSolidity.Executable.SourceUnit.contracts,
                  L00_SourceSolidity.Executable.SourceUnit.usingDecls,
                  L00_SourceSolidity.Executable.ContractDecls.interfaceIdEnv,
                  L00_SourceSolidity.Executable.ContractDecl.interfaceIdEntry?,
                  L00_SourceSolidity.Executable.ContractDecl.interfaceId?,
                  L00_SourceSolidity.Executable.ContractDecl.isInterface,
                  L00_SourceSolidity.Executable.ContractDecl.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.ContractItem.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.ContractDecl.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.ContractItem.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.StateVarDecl.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.ModifierDecl.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.ModifierInvocation.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.Stmt.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.Stmt.resolveFunctionAddressesFuel,
                  L00_SourceSolidity.Executable.Expr.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.Expr.resolveFunctionAddressesFuel,
                  L00_SourceSolidity.Executable.Arg.resolveFunctionAddresses,
                  L00_SourceSolidity.Executable.Arg.resolveFunctionAddressesFuel,
                  L00_SourceSolidity.Executable.CallOption.resolveFunctionAddressesFuel,
                  L00_SourceSolidity.Executable.TupleItem.resolveFunctionAddressesFuel,
                  L00_SourceSolidity.Executable.ContractDecl.resolveSelectors,
                  L00_SourceSolidity.Executable.ContractItem.resolveSelectors,
                  L00_SourceSolidity.Executable.StateVarDecl.resolveSelectors,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveSelectors,
                  L00_SourceSolidity.Executable.ModifierDecl.resolveSelectors,
                  L00_SourceSolidity.Executable.ModifierInvocation.resolveSelectors,
                  L00_SourceSolidity.Executable.Stmt.resolveSelectors,
                  L00_SourceSolidity.Executable.Stmt.resolveSelectorsFuel,
                  L00_SourceSolidity.Executable.Expr.resolveSelectors,
                  L00_SourceSolidity.Executable.Expr.resolveSelectorsFuel,
                  L00_SourceSolidity.Executable.Arg.resolveSelectors,
                  L00_SourceSolidity.Executable.Arg.resolveSelectorsFuel,
                  L00_SourceSolidity.Executable.CallOption.resolveSelectorsFuel,
                  L00_SourceSolidity.Executable.TupleItem.resolveSelectorsFuel,
                  L00_SourceSolidity.Executable.ModifierInvocation.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.Stmt.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.Stmt.resolveInterfaceIdsFuel,
                  L00_SourceSolidity.Executable.Expr.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.Expr.resolveInterfaceIdsFuel,
                  L00_SourceSolidity.Executable.Arg.resolveInterfaceIds,
                  L00_SourceSolidity.Executable.Arg.resolveInterfaceIdsFuel,
                  L00_SourceSolidity.Executable.CallOption.resolveInterfaceIdsFuel,
                  L00_SourceSolidity.Executable.TupleItem.resolveInterfaceIdsFuel,
                  L00_SourceSolidity.Executable.ContractDecl.toCoreWithBases?,
                  L00_SourceSolidity.Executable.ContractDecl.toCoreWithBasesAndUsing?,
                  L00_SourceSolidity.Executable.ContractDecl.storageOrder?,
                  L00_SourceSolidity.Executable.ContractDecl.dispatchOrder?,
                  L00_SourceSolidity.Executable.ContractDecl.storageOrderWithFuel?,
                  L00_SourceSolidity.Executable.ContractDecl.dispatchOrderWithFuel?,
                  L00_SourceSolidity.Executable.ContractDecl.baseDecls?,
                  L00_SourceSolidity.Executable.ContractDecl.findByName?,
                  L00_SourceSolidity.Executable.ContractDecls.nonempty,
                  L00_SourceSolidity.Executable.ContractDecls.nameInTail,
                  L00_SourceSolidity.Executable.ContractDecls.nameInAnyTail,
                  L00_SourceSolidity.Executable.ContractDecls.findMergeCandidate?,
                  L00_SourceSolidity.Executable.ContractDecls.removeName,
                  L00_SourceSolidity.Executable.ContractDecls.removeNameFromSeqs,
                  L00_SourceSolidity.Executable.ContractDecls.mergeLinearizationsWithFuel?,
                  L00_SourceSolidity.Executable.ContractDecls.afterName?,
                  L00_SourceSolidity.Executable.ContractDecls.contextualOrdinaryFunctions,
                  L00_SourceSolidity.Executable.ContractDecl.contextualOrdinaryFunctions,
                  L00_SourceSolidity.Executable.FunctionDecl.rewriteDispatchCalls,
                  L00_SourceSolidity.Executable.ContractDecl.contextualBaseHelpers,
                  L00_SourceSolidity.Executable.ContractDecls.contextualSuperHelpersFor?,
                  L00_SourceSolidity.Executable.ContractDecls.contextualSuperHelpers?,
                  L00_SourceSolidity.Executable.ContractDecl.toCoreFromOrders?,
                  L00_SourceSolidity.Executable.ContractDecl.toCoreStorageFieldsFrom,
                  L00_SourceSolidity.Executable.ContractDecl.toCoreImmutableFieldsFrom,
                  L00_SourceSolidity.Executable.ContractDecl.storageFieldsFrom,
                  L00_SourceSolidity.Executable.ContractDecl.directStateVars,
                  L00_SourceSolidity.Executable.ContractDecl.directModifiers,
                  L00_SourceSolidity.Executable.ContractDecl.directFunctions,
                  L00_SourceSolidity.Executable.ContractDecl.directOrdinaryFunctions,
                  L00_SourceSolidity.Executable.ContractDecl.directEvents,
                  L00_SourceSolidity.Executable.ContractDecl.directErrors,
                  L00_SourceSolidity.Executable.ContractDecl.directUserValueTypes,
                  L00_SourceSolidity.Executable.ContractDecl.directEnums,
                  L00_SourceSolidity.Executable.ContractDecl.directStructs,
                  L00_SourceSolidity.Executable.ContractDecl.directUsingDecls,
                  L00_SourceSolidity.Executable.ContractDecl.userTypeEnvFromContracts,
                  L00_SourceSolidity.Executable.ContractDecl.enumEnvFromContracts,
                  L00_SourceSolidity.Executable.ContractDecl.structEnvFromContracts,
                  L00_SourceSolidity.Executable.ContractDecl.resolveUserTypes,
                  L00_SourceSolidity.Executable.ContractDecl.resolveEnums,
                  L00_SourceSolidity.Executable.ContractDecl.resolveStructs,
                  L00_SourceSolidity.Executable.ContractItem.resolveStructsWithTypeEnv,
                  L00_SourceSolidity.Executable.ContractItem.resolveUserTypes,
                  L00_SourceSolidity.Executable.ContractItem.resolveEnums,
                  L00_SourceSolidity.Executable.ContractItem.resolveStructs,
                  L00_SourceSolidity.Executable.SourceItem.resolveUserTypes,
                  L00_SourceSolidity.Executable.SourceItem.resolveEnums,
                  L00_SourceSolidity.Executable.SourceItem.resolveStructs,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveStructsWithTypeEnv,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveUserTypes,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveEnums,
                  L00_SourceSolidity.Executable.FunctionDecl.resolveStructs,
                  L00_SourceSolidity.Executable.FunctionDecl.typeEnv,
                  L00_SourceSolidity.Executable.ModifierDecl.resolveStructsWithTypeEnv,
                  L00_SourceSolidity.Executable.ModifierInvocation.resolveStructs,
                  L00_SourceSolidity.Executable.StateVarDecl.resolveStructs,
                  L00_SourceSolidity.Executable.StateVarDecl.extendTypeEnv,
                  L00_SourceSolidity.Executable.StateVars.extendTypeEnv,
                  L00_SourceSolidity.Executable.StateVars.constantEnv,
                  L00_SourceSolidity.Executable.StateVars.allConstants,
                  L00_SourceSolidity.Executable.StateVars.constantsHaveInits,
                  L00_SourceSolidity.Executable.stateNamesFrom,
                  L00_SourceSolidity.Executable.Parameter.resolveUserTypes,
                  L00_SourceSolidity.Executable.Parameter.resolveEnums,
                  L00_SourceSolidity.Executable.Parameter.resolveStructs,
                  L00_SourceSolidity.Executable.Ty.resolveUserTypes,
                  L00_SourceSolidity.Executable.Ty.resolveEnums,
                  L00_SourceSolidity.Executable.Ty.resolveStructs,
                  L00_SourceSolidity.Executable.UserTypeEnv.extendDecls,
                  L00_SourceSolidity.Executable.UserTypeEnv.extendDecl,
                  L00_SourceSolidity.Executable.EnumEnv.extendDecls,
                  L00_SourceSolidity.Executable.EnumEnv.extendDecl,
                  L00_SourceSolidity.Executable.StructEnv.extendDecls,
                  L00_SourceSolidity.Executable.StructEnv.extendDecl,
                  L00_SourceSolidity.Executable.ContractDecl.directCoreFunctions?,
                  L00_SourceSolidity.Executable.FunctionDecl.isCoreEntrypoint,
                  L00_SourceSolidity.Executable.ContractDecl.libraryHelperFunctions,
                  L00_SourceSolidity.Executable.FunctionDecl.asLibraryHelper?,
                  L00_SourceSolidity.Executable.FunctionDecl.isInlineLibraryFunction,
                  L00_SourceSolidity.Executable.StateVarDecl.toCoreGetterIfPublic?,
                  L00_SourceSolidity.Executable.mapOption,
                  L00_SourceSolidity.Executable.filterMapOption,
                  L00_SourceSolidity.Executable.concatLists,
                  L00_SourceSolidity.Executable.concatMapList,
                  L00_SourceSolidity.Executable.appendUniqueContracts,
                  L00_SourceSolidity.Executable.nameIn,
                  L00_SourceSolidity.Executable.namesUnique,
                  SolidCore.Solidity.Source.Contract.call?,
                  SolidCore.Solidity.Source.Contract.context,
                  SolidCore.Solidity.Source.Context.empty,
                  SolidCore.Solidity.Source.Contract.findCallableFunctionByName?,
                  SolidCore.Solidity.Source.Contract.findFunction?,
                  SolidCore.Solidity.Source.Contract.findFunctionByName?,
                  L00_SourceSolidity.Executable.FunctionDecl.call?,
                  L00_SourceSolidity.Executable.FunctionDecl.toCore?,
                  L00_SourceSolidity.Executable.FunctionDecl.coreName?,
                  L00_SourceSolidity.Executable.FunctionDecl.isConstructor,
                  L00_SourceSolidity.Executable.Parameters.extendStorageRefEnv,
                  L00_SourceSolidity.Executable.Parameters.extendStorageRefEnvFrom,
                  L00_SourceSolidity.Executable.FunctionDecl.inlineConstants,
                  L00_SourceSolidity.Executable.Parameters.toCoreBindings?,
                  L00_SourceSolidity.Executable.Parameter.toCoreBinding?,
                  L00_SourceSolidity.Executable.mapOptionIdx,
                  L00_SourceSolidity.Executable.Ty.toCore?,
                  L00_SourceSolidity.Executable.Stmt.annotateAbi,
                  checked.sourceInlineConstants,
                  checked.sourceFunctionAddressesResolved,
                  checked.sourceFunctionAddressesResolvedFuel,
                  checked.sourceSelectorsResolved,
                  checked.sourceSelectorsResolvedFuel,
                  checked.sourceRewriteSuperCalls,
                  checked.sourceRewriteBaseCalls,
                  checked.sourceAnnotated,
                  checked.sourceAnnotatedFuel,
                  checked.sourceResolved,
                  checked.sourceEnumsResolved,
                  checked.sourceStructsResolved,
                  checked.sourceInterfaceIdsResolved,
                  checked.sourceInterfaceIdsResolvedFuel,
                  L00_SourceSolidity.Executable.FunctionDecl.superHelpers,
                  L00_SourceSolidity.Executable.functionExpandModifiersToCoreWithInternalCallsFull?,
                  L00_SourceSolidity.Executable.functionExpandModifiersToCoreWithInternalCalls?,
                  checked.sourceCore,
                  L00_SourceSolidity.Executable.ContractDecls.hasLibrary,
                  L00_SourceSolidity.Executable.ContractDecl.isLibrary,
                  SolidCore.Solidity.Source.FunctionDef.call?,
                  SolidCore.Solidity.Source.FunctionDef.initialFrame?,
                  SolidCore.Solidity.Source.BindingDecl.bindArgs?,
                  SolidCore.Solidity.Source.BindingDecl.defaultBinding]
                rw [checked.sourceEvalChecked]
                · simp [SolidCore.Solidity.Source.FunctionDef.coerceReturnValues?,
                    SolidCore.Solidity.Source.FunctionDef.coerceReturnValues?.coerce,
                    SolidCore.Solidity.Source.Ty.coerceValue?,
                    SolidCore.Solidity.Source.FunctionDef.acceptsValue,
                    SolidCore.Solidity.Source.wordEq,
                    L00_SourceSolidity.Executable.CoreCallResult.behavior?,
                    L00_SourceSolidity.Executable.CoreValue.asWord?,
                    SolidCore.Solidity.Source.Value.asWord?,
                    checked.valueNorm]
                · rfl }
      | none => none
  | _ => none

structure CheckedContract (source : L00_SourceSolidity.ContractDecl) where
  contract : L01_ValidSolidity.ContractDecl
  returnedExpr : L01_ValidSolidity.Expr
  value : L01_ValidSolidity.Word
  valueNorm : SharedSemantics.norm value = value
  returned : contract.returnedExpr? = some returnedExpr
  eval : returnedExpr.Eval value
  sourceFuel : Nat
  sourceEntryBehavior :
    L00_SourceSolidity.Executable.SourceUnit.entryBehavior?
        sourceFuel
        { items := [L00_SourceSolidity.SourceItem.contract source] } =
      some (L00_SourceSolidity.Behavior.returnedWord value)

def compileContractChecked?
    : (contract : L00_SourceSolidity.ContractDecl) ->
      Option (CheckedContract contract)
  | contract@{ kind := L00_SourceSolidity.ContractKind.contract
               abstract := false
               bases := []
               items := [L00_SourceSolidity.ContractItem.function fn]
               .. } =>
      match compileFunctionChecked? fn with
      | some checked =>
          some
            { contract :=
                L01_ValidSolidity.ContractDecl.withFunction
                  checked.function
              returnedExpr := checked.returnedExpr
              value := checked.value
              valueNorm := checked.valueNorm
              returned := by
                simp [L01_ValidSolidity.ContractDecl.withFunction,
                  L01_ValidSolidity.ContractDecl.returnedExpr?,
                  checked.returned]
              eval := checked.eval
              sourceFuel := checked.sourceFuel
              sourceEntryBehavior := by
                subst contract
                exact checked.sourceEntryBehavior _ }
      | none => none
  | _ => none

structure CheckedProgram (source : L00_SourceSolidity.SourceUnit) where
  program : L01_ValidSolidity.Program
  wf : L01_ValidSolidity.WF program
  returnedExpr : L01_ValidSolidity.Expr
  value : L01_ValidSolidity.Word
  valueNorm : SharedSemantics.norm value = value
  returned : program.returnedExpr? = some returnedExpr
  eval : returnedExpr.Eval value
  sourceSemantics :
    L00_SourceSolidity.Executable.Semantics source
      (L00_SourceSolidity.Behavior.returnedWord value)

def compileSourceChecked? :
    (source : L00_SourceSolidity.SourceUnit) ->
      Option (CheckedProgram source)
  | { items := [L00_SourceSolidity.SourceItem.contract contract] } =>
      match compileContractChecked? contract with
      | some checked =>
          some
            { program :=
                L01_ValidSolidity.Program.withContract
                  checked.contract
              wf := by exact {}
              returnedExpr := checked.returnedExpr
              value := checked.value
              valueNorm := checked.valueNorm
              returned := by
                simp [L01_ValidSolidity.Program.withContract,
                  L01_ValidSolidity.Program.returnedExpr?,
                  checked.returned]
              eval := checked.eval
              sourceSemantics :=
                L00_SourceSolidity.Executable.Semantics.entry
                  checked.sourceEntryBehavior }
      | none => none
  | _ => none

def structuralExprValue? :
    L00_SourceSolidity.Expr -> Option L01_ValidSolidity.Word
  | L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.number raw) =>
      if decimalLiteralAccepted? raw then
        some
          (SharedSemantics.norm
            (L00_SourceSolidity.Executable.parseDecimalNat raw))
      else
        none
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.add lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match checkedAddChecked? lhsValue rhsValue with
          | some checked =>
              match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
              | some rat =>
                  match rat.exactNat? with
                  | some raw =>
                      if SharedSemantics.norm raw = checked.value then
                        some checked.value
                      else
                        none
                  | none => none
              | none =>
                  match
                    L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                      source with
                  | none => some checked.value
                  | some _ => none
            | none => none
        | _, _ => none
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.mul lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match checkedMulChecked? lhsValue rhsValue with
          | some checked =>
              match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
              | some rat =>
                  match rat.exactNat? with
                  | some raw =>
                      if SharedSemantics.norm raw = checked.value then
                        some checked.value
                      else
                        none
                  | none => none
              | none =>
                  match
                    L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                      source with
                  | none => some checked.value
                  | some _ => none
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.sub lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match checkedSubChecked? lhsValue rhsValue with
          | some checked =>
              match L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
              | some rat =>
                  match rat.exactNat? with
                  | some raw =>
                      if SharedSemantics.norm raw = checked.value then
                        some checked.value
                      else
                        none
                  | none => none
              | none =>
                  match
                    L00_SourceSolidity.Executable.Expr.numberLiteralBool?
                      source with
                  | none => some checked.value
                  | some _ => none
          | none => none
      | _, _ => none
    | L00_SourceSolidity.Expr.binary
        L00_SourceSolidity.BinaryOp.bitAnd lhs rhs =>
        let source :=
          L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match sourceBinaryBitAndNotFolded? source with
          | some () => some (SharedSemantics.andWord lhsValue rhsValue)
          | none => none
      | _, _ => none
    | _ => none

theorem bitAndCheckedExpr_structuralExprValue?
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hNotFolded :
      sourceBinaryBitAndNotFolded?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) =
        some ()) :
    structuralExprValue?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.bitAnd lhs rhs) =
      some (bitAndCheckedExpr lhsChecked rhsChecked hNotFolded).value := by
  simp [structuralExprValue?, bitAndCheckedExpr, hLhsStructural,
    hRhsStructural, hNotFolded]

theorem addSourceMode?_structuralExprValue?
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {addChecked : CheckedAdd lhsChecked.value rhsChecked.value}
    {mode : AddSourceMode}
    (hMode :
      addSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.add lhs rhs)
          addChecked.value =
        some mode)
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hAddChecked :
      checkedAddChecked? lhsChecked.value rhsChecked.value =
        some addChecked) :
    structuralExprValue?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.add lhs rhs) =
      some addChecked.value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.add lhs rhs
  cases mode with
  | structural =>
      have hNotFolded : sourceBinaryAddNotFolded? source = some () :=
        addSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
        sourceBinaryAddNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinaryAddNotFolded?_bool_none hNotFolded
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hAddChecked, hRat, hBool]
  | folded rat raw =>
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (addSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (addSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = addChecked.value :=
        (addSourceMode?_folded hMode).right.right
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hAddChecked, hRat, hExact, hValue]

theorem structuralExprValue?_addSourceMode?_exists
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {addChecked : CheckedAdd lhsChecked.value rhsChecked.value}
    {value : L01_ValidSolidity.Word}
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hAddChecked :
      checkedAddChecked? lhsChecked.value rhsChecked.value =
        some addChecked)
    (hStructural :
      structuralExprValue?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.add lhs rhs) =
        some value) :
    ∃ mode : AddSourceMode,
      addSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.add lhs rhs)
          addChecked.value =
        some mode ∧
      addChecked.value = value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.add lhs rhs
  by_cases hNotFolded : sourceBinaryAddNotFolded? source = some ()
  · have hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
      sourceBinaryAddNotFolded?_rat_none hNotFolded
    have hBool :
        L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
      sourceBinaryAddNotFolded?_bool_none hNotFolded
    simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
      hAddChecked, hRat, hBool] at hStructural
    cases hStructural
    refine ⟨AddSourceMode.structural, ?_, rfl⟩
    simp [addSourceMode?, source, hNotFolded]
  · cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        cases hBool :
            L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
        | none =>
            have hImpossible :
                sourceBinaryAddNotFolded? source = some () := by
              simp [sourceBinaryAddNotFolded?, hRat, hBool]
            exact False.elim (hNotFolded hImpossible)
        | some _ =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hAddChecked, hRat, hBool] at hStructural
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hAddChecked, hRat, hExact] at hStructural
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = addChecked.value
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hAddChecked, hRat, hExact, hValue]
                at hStructural
              cases hStructural
              refine ⟨AddSourceMode.folded rat raw, ?_, rfl⟩
              simp [addSourceMode?, source, hNotFolded, hRat, hExact,
                hValue]
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hAddChecked, hRat, hExact, hValue]
                at hStructural

theorem subSourceMode?_structuralExprValue?
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {subChecked : CheckedSub lhsChecked.value rhsChecked.value}
    {mode : SubSourceMode}
    (hMode :
      subSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.sub lhs rhs)
          subChecked.value =
        some mode)
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hSubChecked :
      checkedSubChecked? lhsChecked.value rhsChecked.value =
        some subChecked) :
    structuralExprValue?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.sub lhs rhs) =
      some subChecked.value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.sub lhs rhs
  cases mode with
  | structural =>
      have hNotFolded : sourceBinarySubNotFolded? source = some () :=
        subSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
        sourceBinarySubNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinarySubNotFolded?_bool_none hNotFolded
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hSubChecked, hRat, hBool]
  | folded rat raw =>
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (subSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (subSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = subChecked.value :=
        (subSourceMode?_folded hMode).right.right
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hSubChecked, hRat, hExact, hValue]

theorem structuralExprValue?_subSourceMode?_exists
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {subChecked : CheckedSub lhsChecked.value rhsChecked.value}
    {value : L01_ValidSolidity.Word}
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hSubChecked :
      checkedSubChecked? lhsChecked.value rhsChecked.value =
        some subChecked)
    (hStructural :
      structuralExprValue?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.sub lhs rhs) =
        some value) :
    ∃ mode : SubSourceMode,
      subSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.sub lhs rhs)
          subChecked.value =
        some mode ∧
      subChecked.value = value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.sub lhs rhs
  by_cases hNotFolded : sourceBinarySubNotFolded? source = some ()
  · have hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
      sourceBinarySubNotFolded?_rat_none hNotFolded
    have hBool :
        L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
      sourceBinarySubNotFolded?_bool_none hNotFolded
    simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
      hSubChecked, hRat, hBool] at hStructural
    cases hStructural
    refine ⟨SubSourceMode.structural, ?_, rfl⟩
    simp [subSourceMode?, source, hNotFolded]
  · cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        cases hBool :
            L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
        | none =>
            have hImpossible :
                sourceBinarySubNotFolded? source = some () := by
              simp [sourceBinarySubNotFolded?, sourceBinaryAddNotFolded?,
                hRat, hBool]
            exact False.elim (hNotFolded hImpossible)
        | some _ =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hSubChecked, hRat, hBool] at hStructural
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hSubChecked, hRat, hExact] at hStructural
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = subChecked.value
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hSubChecked, hRat, hExact, hValue]
                at hStructural
              cases hStructural
              refine ⟨SubSourceMode.folded rat raw, ?_, rfl⟩
              simp [subSourceMode?, source, hNotFolded, hRat, hExact,
                hValue]
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hSubChecked, hRat, hExact, hValue]
                at hStructural

theorem mulSourceMode?_structuralExprValue?
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {mulChecked : CheckedMul lhsChecked.value rhsChecked.value}
    {mode : MulSourceMode}
    (hMode :
      mulSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.mul lhs rhs)
          mulChecked.value =
        some mode)
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hMulChecked :
      checkedMulChecked? lhsChecked.value rhsChecked.value =
        some mulChecked) :
    structuralExprValue?
        (L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.mul lhs rhs) =
      some mulChecked.value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.mul lhs rhs
  cases mode with
  | structural =>
      have hNotFolded : sourceBinaryMulNotFolded? source = some () :=
        mulSourceMode?_structural hMode
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
        sourceBinaryMulNotFolded?_rat_none hNotFolded
      have hBool :
          L00_SourceSolidity.Executable.Expr.numberLiteralBool? source =
            none :=
        sourceBinaryMulNotFolded?_bool_none hNotFolded
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hMulChecked, hRat, hBool]
  | folded rat raw =>
      have hRat :
          L00_SourceSolidity.Executable.Expr.numberLiteralRat? source =
            some rat :=
        (mulSourceMode?_folded hMode).left
      have hExact : rat.exactNat? = some raw :=
        (mulSourceMode?_folded hMode).right.left
      have hValue : SharedSemantics.norm raw = mulChecked.value :=
        (mulSourceMode?_folded hMode).right.right
      simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
        hMulChecked, hRat, hExact, hValue]

theorem structuralExprValue?_mulSourceMode?_exists
    {lhs rhs : L00_SourceSolidity.Expr}
    {lhsChecked : CheckedExpr lhs}
    {rhsChecked : CheckedExpr rhs}
    {mulChecked : CheckedMul lhsChecked.value rhsChecked.value}
    {value : L01_ValidSolidity.Word}
    (hLhsStructural :
      structuralExprValue? lhs = some lhsChecked.value)
    (hRhsStructural :
      structuralExprValue? rhs = some rhsChecked.value)
    (hMulChecked :
      checkedMulChecked? lhsChecked.value rhsChecked.value =
        some mulChecked)
    (hStructural :
      structuralExprValue?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.mul lhs rhs) =
        some value) :
    ∃ mode : MulSourceMode,
      mulSourceMode?
          (L00_SourceSolidity.Expr.binary
            L00_SourceSolidity.BinaryOp.mul lhs rhs)
          mulChecked.value =
        some mode ∧
      mulChecked.value = value := by
  let source :=
    L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.mul lhs rhs
  by_cases hNotFolded : sourceBinaryMulNotFolded? source = some ()
  · have hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source = none :=
      sourceBinaryMulNotFolded?_rat_none hNotFolded
    have hBool :
        L00_SourceSolidity.Executable.Expr.numberLiteralBool? source = none :=
      sourceBinaryMulNotFolded?_bool_none hNotFolded
    simp [structuralExprValue?, source, hLhsStructural, hRhsStructural,
      hMulChecked, hRat, hBool] at hStructural
    cases hStructural
    refine ⟨MulSourceMode.structural, ?_, rfl⟩
    simp [mulSourceMode?, source, hNotFolded]
  · cases hRat :
        L00_SourceSolidity.Executable.Expr.numberLiteralRat? source with
    | none =>
        cases hBool :
            L00_SourceSolidity.Executable.Expr.numberLiteralBool? source with
        | none =>
            have hImpossible :
                sourceBinaryMulNotFolded? source = some () := by
              simp [sourceBinaryMulNotFolded?, sourceBinaryAddNotFolded?,
                hRat, hBool]
            exact False.elim (hNotFolded hImpossible)
        | some _ =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hMulChecked, hRat, hBool] at hStructural
    | some rat =>
        cases hExact : rat.exactNat? with
        | none =>
            simp [structuralExprValue?, source, hLhsStructural,
              hRhsStructural, hMulChecked, hRat, hExact] at hStructural
        | some raw =>
            by_cases hValue : SharedSemantics.norm raw = mulChecked.value
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hMulChecked, hRat, hExact, hValue]
                at hStructural
              cases hStructural
              refine ⟨MulSourceMode.folded rat raw, ?_, rfl⟩
              simp [mulSourceMode?, source, hNotFolded, hRat, hExact,
                hValue]
            · simp [structuralExprValue?, source, hLhsStructural,
                hRhsStructural, hMulChecked, hRat, hExact, hValue]
                at hStructural

def structuralBoolExprValue? :
    L00_SourceSolidity.Expr -> Option L01_ValidSolidity.Word
  | L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.bool value) =>
      some (SolidCore.Solidity.Source.boolWord value)
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.lt lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.lt lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match sourceBinaryLtNotFolded? source with
          | some () =>
              some (SharedSemantics.ltWord lhsValue rhsValue)
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.gt lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.gt lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match sourceBinaryGtNotFolded? source with
          | some () =>
              some (SharedSemantics.gtWord lhsValue rhsValue)
          | none => none
      | _, _ => none
  | L00_SourceSolidity.Expr.binary
      L00_SourceSolidity.BinaryOp.eq lhs rhs =>
      let source :=
        L00_SourceSolidity.Expr.binary
          L00_SourceSolidity.BinaryOp.eq lhs rhs
      match structuralExprValue? lhs, structuralExprValue? rhs with
      | some lhsValue, some rhsValue =>
          match sourceBinaryEqNotFolded? source with
          | some () =>
              some (SharedSemantics.eqWord lhsValue rhsValue)
          | none => none
      | _, _ => none
  | _ => none

def structuralExprAccepted? (expr : L00_SourceSolidity.Expr) : Bool :=
  (structuralExprValue? expr).isSome

def structuralStmtValue? :
    L00_SourceSolidity.Stmt -> Option L01_ValidSolidity.Word
  | L00_SourceSolidity.Stmt.returnValues (some expr) =>
      structuralExprValue? expr
  | L00_SourceSolidity.Stmt.block [stmt] =>
      structuralStmtValue? stmt
  | L00_SourceSolidity.Stmt.ifElse condition thenBranch (some elseBranch) =>
      match structuralBoolExprValue? condition,
          structuralStmtValue? thenBranch,
          structuralStmtValue? elseBranch with
      | some conditionValue, some thenValue, some elseValue =>
          if SolidCore.Solidity.Source.wordTruthy conditionValue then
            some thenValue
          else
            some elseValue
      | _, _, _ => none
  | _ => none

def structuralStmtAccepted? (stmt : L00_SourceSolidity.Stmt) : Bool :=
  (structuralStmtValue? stmt).isSome

def structuralFunctionValue? :
    L00_SourceSolidity.FunctionDecl -> Option L01_ValidSolidity.Word
  | { kind := L00_SourceSolidity.FunctionKind.function
      name := some _
      params := []
      returns := [{ ty := L00_SourceSolidity.Ty.uint 256, .. }]
      visibility := some L00_SourceSolidity.Visibility.public_
      mutability := L00_SourceSolidity.StateMutability.pure
      modifiers := []
      body := some body
      .. } =>
      structuralStmtValue? body
  | _ => none

def structuralFunctionAccepted? (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  (structuralFunctionValue? fn).isSome

def structuralContractValue? :
    L00_SourceSolidity.ContractDecl -> Option L01_ValidSolidity.Word
  | { kind := L00_SourceSolidity.ContractKind.contract
      abstract := false
      bases := []
      items := [L00_SourceSolidity.ContractItem.function fn]
      .. } =>
      structuralFunctionValue? fn
  | _ => none

def structuralContractAccepted? (contract : L00_SourceSolidity.ContractDecl) : Bool :=
  (structuralContractValue? contract).isSome

def structuralSourceValue? :
    L00_SourceSolidity.SourceUnit -> Option L01_ValidSolidity.Word
  | { items := [L00_SourceSolidity.SourceItem.contract contract] } =>
      structuralContractValue? contract
  | _ => none

theorem compileExprChecked?_structuralExprValue? :
    ∀ {source : L00_SourceSolidity.Expr}
      {checked : CheckedExpr source},
      compileExprChecked? source = some checked ->
        structuralExprValue? source = some checked.value
  | L00_SourceSolidity.Expr.literal lit, checked, hCompile => by
      cases lit with
      | number raw =>
          by_cases hRaw : decimalLiteralAccepted? raw
          · simp [compileExprChecked?, structuralExprValue?, hRaw] at hCompile ⊢
            cases hCompile
            simp
          · simp [compileExprChecked?, hRaw] at hCompile
        | bool value =>
            simp [compileExprChecked?] at hCompile
        | unitNumber text unit =>
            simp [compileExprChecked?] at hCompile
        | string value =>
            simp [compileExprChecked?] at hCompile
      | hexString value =>
          simp [compileExprChecked?] at hCompile
      | unicodeString value =>
          simp [compileExprChecked?] at hCompile
      | address value =>
          simp [compileExprChecked?] at hCompile
      | bytes value =>
          simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.ident name, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.typeName ty, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.member source name, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.index source index, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.slice source start stop, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.call target args, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.callWithOptions target options args, checked,
      hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.newExpr ty args, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.tuple items, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.array items, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.enumFromUInt value source, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.unary op source, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.binary op lhs rhs, checked, hCompile => by
      cases op with
      | add =>
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
              | some rhsChecked =>
                  cases hAddChecked :
                      checkedAddChecked? lhsChecked.value rhsChecked.value with
                  | none =>
                      simp [compileExprChecked?, hLhs, hRhs, hAddChecked]
                        at hCompile
                    | some addChecked =>
                        let source :=
                          L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.add lhs rhs
                        simp [compileExprChecked?, source, hLhs, hRhs,
                          hAddChecked] at hCompile
                        split at hCompile
                        · rename_i mode hMode
                          cases hCompile
                          have hLhsStructural :
                              structuralExprValue? lhs =
                                some lhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hLhs
                          have hRhsStructural :
                              structuralExprValue? rhs =
                                some rhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hRhs
                          exact
                            addSourceMode?_structuralExprValue?
                              hMode hLhsStructural hRhsStructural
                              hAddChecked
                        · cases hCompile
      | sub =>
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, hLhs, hRhs] at hCompile
              | some rhsChecked =>
                  cases hSubChecked :
                      checkedSubChecked? lhsChecked.value rhsChecked.value with
                  | none =>
                      simp [compileExprChecked?, hLhs, hRhs, hSubChecked]
                        at hCompile
                    | some subChecked =>
                        let source :=
                          L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.sub lhs rhs
                        simp [compileExprChecked?, source, hLhs, hRhs,
                          hSubChecked] at hCompile
                        split at hCompile
                        · rename_i mode hMode
                          cases hCompile
                          have hLhsStructural :
                              structuralExprValue? lhs =
                                some lhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hLhs
                          have hRhsStructural :
                              structuralExprValue? rhs =
                                some rhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hRhs
                          exact
                            subSourceMode?_structuralExprValue?
                              hMode hLhsStructural hRhsStructural
                              hSubChecked
                        · cases hCompile
      | mul =>
            cases hLhs : compileExprChecked? lhs with
            | none =>
                simp [compileExprChecked?, hLhs] at hCompile
            | some lhsChecked =>
                cases hRhs : compileExprChecked? rhs with
                | none =>
                    simp [compileExprChecked?, hLhs, hRhs] at hCompile
                | some rhsChecked =>
                    cases hMulChecked :
                        checkedMulChecked? lhsChecked.value rhsChecked.value with
                    | none =>
                        simp [compileExprChecked?, hLhs, hRhs, hMulChecked]
                          at hCompile
                    | some mulChecked =>
                        let source :=
                          L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.mul lhs rhs
                        simp [compileExprChecked?, source, hLhs, hRhs,
                          hMulChecked] at hCompile
                        split at hCompile
                        · rename_i mode hMode
                          cases hCompile
                          have hLhsStructural :
                              structuralExprValue? lhs =
                                some lhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hLhs
                          have hRhsStructural :
                              structuralExprValue? rhs =
                                some rhsChecked.value :=
                            compileExprChecked?_structuralExprValue? hRhs
                          exact
                            mulSourceMode?_structuralExprValue?
                              hMode hLhsStructural hRhsStructural
                              hMulChecked
                        · cases hCompile
      | div =>
          simp [compileExprChecked?] at hCompile
      | mod =>
          simp [compileExprChecked?] at hCompile
      | exp =>
          simp [compileExprChecked?] at hCompile
      | bitAnd =>
          let source :=
            L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
          cases hLhs : compileExprChecked? lhs with
          | none =>
              simp [compileExprChecked?, source, hLhs] at hCompile
          | some lhsChecked =>
              cases hRhs : compileExprChecked? rhs with
              | none =>
                  simp [compileExprChecked?, source, hLhs, hRhs]
                    at hCompile
              | some rhsChecked =>
                  by_cases hNotFolded :
                      sourceBinaryBitAndNotFolded? source = some ()
                  · simp [compileExprChecked?, source, hLhs, hRhs,
                      hNotFolded] at hCompile
                    cases hCompile
                    have hLhsStructural :
                        structuralExprValue? lhs =
                          some lhsChecked.value :=
                      compileExprChecked?_structuralExprValue? hLhs
                    have hRhsStructural :
                        structuralExprValue? rhs =
                          some rhsChecked.value :=
                      compileExprChecked?_structuralExprValue? hRhs
                    exact
                      bitAndCheckedExpr_structuralExprValue?
                        hLhsStructural hRhsStructural hNotFolded
                  · simp [compileExprChecked?, source, hLhs, hRhs,
                      hNotFolded] at hCompile
      | bitOr =>
          simp [compileExprChecked?] at hCompile
      | bitXor =>
          simp [compileExprChecked?] at hCompile
      | shl =>
          simp [compileExprChecked?] at hCompile
      | shr =>
          simp [compileExprChecked?] at hCompile
      | sar =>
          simp [compileExprChecked?] at hCompile
      | lt =>
          simp [compileExprChecked?] at hCompile
      | gt =>
          simp [compileExprChecked?] at hCompile
      | le =>
          simp [compileExprChecked?] at hCompile
      | ge =>
          simp [compileExprChecked?] at hCompile
      | eq =>
          simp [compileExprChecked?] at hCompile
      | ne =>
          simp [compileExprChecked?] at hCompile
      | boolAnd =>
          simp [compileExprChecked?] at hCompile
      | boolOr =>
          simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.ternary condition thenExpr elseExpr, checked,
      hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.assign lhs op rhs, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
  | L00_SourceSolidity.Expr.payableConversion source, checked, hCompile => by
      simp [compileExprChecked?] at hCompile
theorem structuralExprValue?_compileExprChecked?_exists :
    ∀ {source : L00_SourceSolidity.Expr}
      {value : L01_ValidSolidity.Word},
      structuralExprValue? source = some value ->
        ∃ checked : CheckedExpr source,
          compileExprChecked? source = some checked ∧
            checked.value = value
  | L00_SourceSolidity.Expr.literal lit, value, hStructural => by
      cases lit with
      | number raw =>
          by_cases hRaw : decimalLiteralAccepted? raw
          · cases hCompile :
              compileExprChecked?
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number raw)) with
            | none =>
                simp [compileExprChecked?, hRaw] at hCompile
            | some checked =>
                refine
                  ⟨checked,
                    by simpa [compileExprChecked?, hRaw] using hCompile, ?_⟩
                have hCompileStructural :
                    structuralExprValue?
                        (L00_SourceSolidity.Expr.literal
                          (L00_SourceSolidity.Literal.number raw)) =
                      some checked.value :=
                  compileExprChecked?_structuralExprValue? hCompile
                rw [hStructural] at hCompileStructural
                cases hCompileStructural
                rfl
          · simp [structuralExprValue?, hRaw] at hStructural
        | bool value =>
            simp [structuralExprValue?] at hStructural
        | unitNumber text unit =>
            simp [structuralExprValue?] at hStructural
        | string value =>
            simp [structuralExprValue?] at hStructural
      | hexString value =>
          simp [structuralExprValue?] at hStructural
      | unicodeString value =>
          simp [structuralExprValue?] at hStructural
      | address value =>
          simp [structuralExprValue?] at hStructural
      | bytes value =>
          simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.ident name, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.typeName ty, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.member source name, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.index source index, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.slice source start stop, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.call target args, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.callWithOptions target options args, value,
      hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.newExpr ty args, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.tuple items, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.array items, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.enumFromUInt word source, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.unary op source, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.binary op lhs rhs, value, hStructural => by
      cases op with
      | add =>
          let source :=
            L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.add lhs rhs
          cases hLhsStructural : structuralExprValue? lhs with
          | none =>
              simp [structuralExprValue?, source, hLhsStructural]
                at hStructural
          | some lhsValue =>
              cases hRhsStructural : structuralExprValue? rhs with
              | none =>
                  simp [structuralExprValue?, source, hLhsStructural,
                    hRhsStructural] at hStructural
              | some rhsValue =>
                  cases hAddChecked :
                      checkedAddChecked? lhsValue rhsValue with
                  | none =>
                      simp [structuralExprValue?, source, hLhsStructural,
                        hRhsStructural, hAddChecked] at hStructural
                  | some addChecked =>
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hLhsStructural with
                        ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hRhsStructural with
                        ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                      cases hLhsValue
                      cases hRhsValue
                      rcases structuralExprValue?_addSourceMode?_exists
                          (lhsChecked := lhsChecked)
                          (rhsChecked := rhsChecked)
                          (addChecked := addChecked)
                          hLhsStructural hRhsStructural hAddChecked
                          hStructural with
                        ⟨mode, hMode, hValue⟩
                      simp [compileExprChecked?, source, hLhsCompile,
                        hRhsCompile, hAddChecked]
                      split
                      · refine ⟨_, rfl, ?_⟩
                        exact hValue
                      · rename_i hModeNone
                        rw [hMode] at hModeNone
                        cases hModeNone
      | sub =>
          let source :=
            L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.sub lhs rhs
          cases hLhsStructural : structuralExprValue? lhs with
          | none =>
              simp [structuralExprValue?, source, hLhsStructural]
                at hStructural
          | some lhsValue =>
              cases hRhsStructural : structuralExprValue? rhs with
              | none =>
                  simp [structuralExprValue?, source, hLhsStructural,
                    hRhsStructural] at hStructural
              | some rhsValue =>
                  cases hSubChecked :
                      checkedSubChecked? lhsValue rhsValue with
                  | none =>
                      simp [structuralExprValue?, source, hLhsStructural,
                        hRhsStructural, hSubChecked] at hStructural
                  | some subChecked =>
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hLhsStructural with
                        ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hRhsStructural with
                        ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                      cases hLhsValue
                      cases hRhsValue
                      rcases structuralExprValue?_subSourceMode?_exists
                          (lhsChecked := lhsChecked)
                          (rhsChecked := rhsChecked)
                          (subChecked := subChecked)
                          hLhsStructural hRhsStructural hSubChecked
                          hStructural with
                        ⟨mode, hMode, hValue⟩
                      simp [compileExprChecked?, source, hLhsCompile,
                        hRhsCompile, hSubChecked]
                      split
                      · refine ⟨_, rfl, ?_⟩
                        exact hValue
                      · rename_i hModeNone
                        rw [hMode] at hModeNone
                        cases hModeNone
      | mul =>
            let source :=
              L00_SourceSolidity.Expr.binary
                L00_SourceSolidity.BinaryOp.mul lhs rhs
            cases hLhsStructural : structuralExprValue? lhs with
            | none =>
                simp [structuralExprValue?, source, hLhsStructural]
                  at hStructural
            | some lhsValue =>
                cases hRhsStructural : structuralExprValue? rhs with
                | none =>
                    simp [structuralExprValue?, source, hLhsStructural,
                      hRhsStructural] at hStructural
                | some rhsValue =>
                    cases hMulChecked :
                        checkedMulChecked? lhsValue rhsValue with
                    | none =>
                        simp [structuralExprValue?, source, hLhsStructural,
                          hRhsStructural, hMulChecked] at hStructural
                    | some mulChecked =>
                        rcases structuralExprValue?_compileExprChecked?_exists
                            hLhsStructural with
                          ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                        rcases structuralExprValue?_compileExprChecked?_exists
                            hRhsStructural with
                          ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                        cases hLhsValue
                        cases hRhsValue
                        rcases structuralExprValue?_mulSourceMode?_exists
                            (lhsChecked := lhsChecked)
                            (rhsChecked := rhsChecked)
                            (mulChecked := mulChecked)
                            hLhsStructural hRhsStructural hMulChecked
                            hStructural with
                          ⟨mode, hMode, hValue⟩
                        simp [compileExprChecked?, source, hLhsCompile,
                          hRhsCompile, hMulChecked]
                        split
                        · refine ⟨_, rfl, ?_⟩
                          exact hValue
                        · rename_i hModeNone
                          rw [hMode] at hModeNone
                          cases hModeNone
      | div =>
          simp [structuralExprValue?] at hStructural
      | mod =>
          simp [structuralExprValue?] at hStructural
      | exp =>
          simp [structuralExprValue?] at hStructural
      | bitAnd =>
          let source :=
            L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.bitAnd lhs rhs
          cases hLhsStructural : structuralExprValue? lhs with
          | none =>
              simp [structuralExprValue?, source, hLhsStructural]
                at hStructural
          | some lhsValue =>
              cases hRhsStructural : structuralExprValue? rhs with
              | none =>
                  simp [structuralExprValue?, source, hLhsStructural,
                    hRhsStructural] at hStructural
              | some rhsValue =>
                  cases hNotFolded :
                      sourceBinaryBitAndNotFolded? source with
                  | none =>
                      simp [structuralExprValue?, source, hLhsStructural,
                        hRhsStructural, hNotFolded] at hStructural
                  | some unitValue =>
                      cases unitValue
                      simp [structuralExprValue?, source, hLhsStructural,
                        hRhsStructural, hNotFolded] at hStructural
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hLhsStructural with
                        ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                      rcases structuralExprValue?_compileExprChecked?_exists
                          hRhsStructural with
                        ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                      cases hLhsValue
                      cases hRhsValue
                      let checked :=
                        bitAndCheckedExpr lhsChecked rhsChecked
                          hNotFolded
                      refine ⟨checked, ?_, ?_⟩
                      · simp [compileExprChecked?, source, hLhsCompile,
                          hRhsCompile, hNotFolded, checked]
                      · simp [checked, bitAndCheckedExpr]
                        exact hStructural
      | bitOr =>
          simp [structuralExprValue?] at hStructural
      | bitXor =>
          simp [structuralExprValue?] at hStructural
      | shl =>
          simp [structuralExprValue?] at hStructural
      | shr =>
          simp [structuralExprValue?] at hStructural
      | sar =>
          simp [structuralExprValue?] at hStructural
      | lt =>
          simp [structuralExprValue?] at hStructural
      | gt =>
          simp [structuralExprValue?] at hStructural
      | le =>
          simp [structuralExprValue?] at hStructural
      | ge =>
          simp [structuralExprValue?] at hStructural
      | eq =>
          simp [structuralExprValue?] at hStructural
      | ne =>
          simp [structuralExprValue?] at hStructural
      | boolAnd =>
          simp [structuralExprValue?] at hStructural
      | boolOr =>
          simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.ternary condition thenExpr elseExpr, value,
      hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.assign lhs op rhs, value, hStructural => by
      simp [structuralExprValue?] at hStructural
  | L00_SourceSolidity.Expr.payableConversion source, value, hStructural => by
      simp [structuralExprValue?] at hStructural

theorem compileBoolExprChecked?_structuralBoolExprValue? :
    ∀ {source : L00_SourceSolidity.Expr}
      {checked : CheckedBoolExpr source},
      compileBoolExprChecked? source = some checked ->
        structuralBoolExprValue? source = some checked.value := by
  intro source checked hCompile
  cases source
  case literal lit =>
    cases lit <;>
      simp [compileBoolExprChecked?, structuralBoolExprValue?] at hCompile ⊢
    case bool value =>
      cases hCompile
      rfl
  case binary op lhs rhs =>
    cases op <;> simp [compileBoolExprChecked?] at hCompile
    case lt =>
      cases hLhs : compileExprChecked? lhs with
      | none =>
          simp [compileBoolExprChecked?, hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs : compileExprChecked? rhs with
          | none =>
              simp [compileBoolExprChecked?, hLhs, hRhs] at hCompile
          | some rhsChecked =>
              have hLhsStructural :
                  structuralExprValue? lhs = some lhsChecked.value :=
                compileExprChecked?_structuralExprValue? hLhs
              have hRhsStructural :
                  structuralExprValue? rhs = some rhsChecked.value :=
                compileExprChecked?_structuralExprValue? hRhs
              cases hNotFolded :
                  sourceBinaryLtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.lt lhs rhs) with
              | some unitValue =>
                  cases unitValue
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
                  cases hCompile
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded]
              | none =>
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
    case gt =>
      cases hLhs : compileExprChecked? lhs with
      | none =>
          simp [compileBoolExprChecked?, hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs : compileExprChecked? rhs with
          | none =>
              simp [compileBoolExprChecked?, hLhs, hRhs] at hCompile
          | some rhsChecked =>
              have hLhsStructural :
                  structuralExprValue? lhs = some lhsChecked.value :=
                compileExprChecked?_structuralExprValue? hLhs
              have hRhsStructural :
                  structuralExprValue? rhs = some rhsChecked.value :=
                compileExprChecked?_structuralExprValue? hRhs
              cases hNotFolded :
                  sourceBinaryGtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.gt lhs rhs) with
              | some unitValue =>
                  cases unitValue
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
                  cases hCompile
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded]
              | none =>
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
    case eq =>
      cases hLhs : compileExprChecked? lhs with
      | none =>
          simp [compileBoolExprChecked?, hLhs] at hCompile
      | some lhsChecked =>
          cases hRhs : compileExprChecked? rhs with
          | none =>
              simp [compileBoolExprChecked?, hLhs, hRhs] at hCompile
          | some rhsChecked =>
              have hLhsStructural :
                  structuralExprValue? lhs = some lhsChecked.value :=
                compileExprChecked?_structuralExprValue? hLhs
              have hRhsStructural :
                  structuralExprValue? rhs = some rhsChecked.value :=
                compileExprChecked?_structuralExprValue? hRhs
              cases hNotFolded :
                  sourceBinaryEqNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.eq lhs rhs) with
              | some unitValue =>
                  cases unitValue
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
                  cases hCompile
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded]
              | none =>
                  simp [compileBoolExprChecked?, hLhs, hRhs, hNotFolded]
                    at hCompile
  all_goals simp [compileBoolExprChecked?] at hCompile

theorem structuralBoolExprValue?_compileBoolExprChecked?_exists :
    ∀ {source : L00_SourceSolidity.Expr}
      {value : L01_ValidSolidity.Word},
      structuralBoolExprValue? source = some value ->
        ∃ checked : CheckedBoolExpr source,
          compileBoolExprChecked? source = some checked ∧
            checked.value = value := by
  intro source value hStructural
  cases source
  case literal lit =>
    cases lit <;>
      simp [structuralBoolExprValue?] at hStructural
    case bool boolValue =>
      cases hStructural
      cases hCompile :
          compileBoolExprChecked?
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.bool boolValue)) with
      | none =>
          simp [compileBoolExprChecked?] at hCompile
      | some checked =>
          refine
            ⟨checked,
              by simpa [compileBoolExprChecked?] using hCompile,
              ?_⟩
          have hCompileStructural :
              structuralBoolExprValue?
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.bool boolValue)) =
                some checked.value :=
            compileBoolExprChecked?_structuralBoolExprValue? hCompile
          simpa [structuralBoolExprValue?] using hCompileStructural.symm
  case binary op lhs rhs =>
    cases op <;> simp [structuralBoolExprValue?] at hStructural
    case lt =>
      cases hLhsStructural : structuralExprValue? lhs with
      | none =>
          simp [structuralBoolExprValue?, hLhsStructural] at hStructural
      | some lhsValue =>
          cases hRhsStructural : structuralExprValue? rhs with
          | none =>
              simp [structuralBoolExprValue?, hLhsStructural,
                hRhsStructural] at hStructural
          | some rhsValue =>
              cases hNotFolded :
                  sourceBinaryLtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.lt lhs rhs) with
              | none =>
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
              | some unitValue =>
                  cases unitValue
                  have hStructuralEq :
                      structuralBoolExprValue?
                          (L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.lt lhs rhs) =
                        some value := hStructural
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hLhsStructural with
                    ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hRhsStructural with
                    ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                  cases hLhsValue
                  cases hRhsValue
                  cases hCompile :
                      compileBoolExprChecked?
                        (L00_SourceSolidity.Expr.binary
                          L00_SourceSolidity.BinaryOp.lt lhs rhs) with
                  | none =>
                      simp [compileBoolExprChecked?, hLhsCompile,
                        hRhsCompile, hNotFolded] at hCompile
                  | some checked =>
                      refine
                        ⟨checked,
                          by
                            simpa [compileBoolExprChecked?, hLhsCompile,
                              hRhsCompile, hNotFolded] using hCompile,
                          ?_⟩
                      have hCompileStructural :
                          structuralBoolExprValue?
                              (L00_SourceSolidity.Expr.binary
                                L00_SourceSolidity.BinaryOp.lt lhs rhs) =
                            some checked.value :=
                        compileBoolExprChecked?_structuralBoolExprValue?
                          hCompile
                      rw [hStructuralEq] at hCompileStructural
                      cases hCompileStructural
                      rfl
    case gt =>
      cases hLhsStructural : structuralExprValue? lhs with
      | none =>
          simp [structuralBoolExprValue?, hLhsStructural] at hStructural
      | some lhsValue =>
          cases hRhsStructural : structuralExprValue? rhs with
          | none =>
              simp [structuralBoolExprValue?, hLhsStructural,
                hRhsStructural] at hStructural
          | some rhsValue =>
              cases hNotFolded :
                  sourceBinaryGtNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.gt lhs rhs) with
              | none =>
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
              | some unitValue =>
                  cases unitValue
                  have hStructuralEq :
                      structuralBoolExprValue?
                          (L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.gt lhs rhs) =
                        some value := hStructural
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hLhsStructural with
                    ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hRhsStructural with
                    ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                  cases hLhsValue
                  cases hRhsValue
                  cases hCompile :
                      compileBoolExprChecked?
                        (L00_SourceSolidity.Expr.binary
                          L00_SourceSolidity.BinaryOp.gt lhs rhs) with
                  | none =>
                      simp [compileBoolExprChecked?, hLhsCompile,
                        hRhsCompile, hNotFolded] at hCompile
                  | some checked =>
                      refine
                        ⟨checked,
                          by
                            simpa [compileBoolExprChecked?, hLhsCompile,
                              hRhsCompile, hNotFolded] using hCompile,
                          ?_⟩
                      have hCompileStructural :
                          structuralBoolExprValue?
                              (L00_SourceSolidity.Expr.binary
                                L00_SourceSolidity.BinaryOp.gt lhs rhs) =
                            some checked.value :=
                        compileBoolExprChecked?_structuralBoolExprValue?
                          hCompile
                      rw [hStructuralEq] at hCompileStructural
                      cases hCompileStructural
                      rfl
    case eq =>
      cases hLhsStructural : structuralExprValue? lhs with
      | none =>
          simp [structuralBoolExprValue?, hLhsStructural] at hStructural
      | some lhsValue =>
          cases hRhsStructural : structuralExprValue? rhs with
          | none =>
              simp [structuralBoolExprValue?, hLhsStructural,
                hRhsStructural] at hStructural
          | some rhsValue =>
              cases hNotFolded :
                  sourceBinaryEqNotFolded?
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.eq lhs rhs) with
              | none =>
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
              | some unitValue =>
                  cases unitValue
                  have hStructuralEq :
                      structuralBoolExprValue?
                          (L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.eq lhs rhs) =
                        some value := hStructural
                  simp [structuralBoolExprValue?, hLhsStructural,
                    hRhsStructural, hNotFolded] at hStructural
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hLhsStructural with
                    ⟨lhsChecked, hLhsCompile, hLhsValue⟩
                  rcases structuralExprValue?_compileExprChecked?_exists
                      hRhsStructural with
                    ⟨rhsChecked, hRhsCompile, hRhsValue⟩
                  cases hLhsValue
                  cases hRhsValue
                  cases hCompile :
                      compileBoolExprChecked?
                        (L00_SourceSolidity.Expr.binary
                          L00_SourceSolidity.BinaryOp.eq lhs rhs) with
                  | none =>
                      simp [compileBoolExprChecked?, hLhsCompile,
                        hRhsCompile, hNotFolded] at hCompile
                  | some checked =>
                      refine
                        ⟨checked,
                          by
                            simpa [compileBoolExprChecked?, hLhsCompile,
                              hRhsCompile, hNotFolded] using hCompile,
                          ?_⟩
                      have hCompileStructural :
                          structuralBoolExprValue?
                              (L00_SourceSolidity.Expr.binary
                                L00_SourceSolidity.BinaryOp.eq lhs rhs) =
                            some checked.value :=
                        compileBoolExprChecked?_structuralBoolExprValue?
                          hCompile
                      rw [hStructuralEq] at hCompileStructural
                      cases hCompileStructural
                      rfl
  all_goals simp [structuralBoolExprValue?] at hStructural

theorem compileStmtChecked?_structuralStmtValue? :
    ∀ {functions : List L00_SourceSolidity.FunctionDecl}
      {source : L00_SourceSolidity.Stmt}
      {checked : CheckedStmt functions source},
      compileStmtChecked? functions source = some checked ->
        structuralStmtValue? source = some checked.value
  | functions, L00_SourceSolidity.Stmt.returnValues maybeExpr, checked,
      hCompile => by
      cases maybeExpr with
      | none =>
          simp [compileStmtChecked?] at hCompile
      | some expr =>
          cases hExpr : compileExprChecked? expr with
          | none =>
              simp [compileStmtChecked?, hExpr] at hCompile
          | some exprChecked =>
              simp [compileStmtChecked?, hExpr] at hCompile
              cases hCompile
              have hExprStructural :
                  structuralExprValue? expr = some exprChecked.value :=
                compileExprChecked?_structuralExprValue? hExpr
              simpa [structuralStmtValue?, hExprStructural]
  | functions, L00_SourceSolidity.Stmt.block body, checked, hCompile => by
      cases body with
      | nil =>
          simp [compileStmtChecked?] at hCompile
      | cons stmt rest =>
          cases rest with
          | nil =>
              cases hStmt : compileStmtChecked? functions stmt with
              | none =>
                  simp [compileStmtChecked?, hStmt] at hCompile
              | some stmtChecked =>
                  simp [compileStmtChecked?, hStmt] at hCompile
                  cases hCompile
                  have hStmtStructural :
                      structuralStmtValue? stmt = some stmtChecked.value :=
                    compileStmtChecked?_structuralStmtValue? hStmt
                  simpa [structuralStmtValue?, hStmtStructural]
          | cons stmt' rest' =>
              simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.ifElse condition thenBranch maybeElse,
      checked, hCompile => by
      cases maybeElse with
      | none =>
          simp [compileStmtChecked?] at hCompile
      | some elseBranch =>
          cases hCondition : compileBoolExprChecked? condition with
          | none =>
              simp [compileStmtChecked?, hCondition] at hCompile
          | some conditionChecked =>
              cases hThen : compileStmtChecked? functions thenBranch with
              | none =>
                  simp [compileStmtChecked?, hCondition, hThen] at hCompile
              | some thenChecked =>
                  cases hElse : compileStmtChecked? functions elseBranch with
                  | none =>
                      simp [compileStmtChecked?, hCondition, hThen, hElse]
                        at hCompile
                  | some elseChecked =>
                      by_cases hTruthy :
                          SolidCore.Solidity.Source.wordTruthy
                            conditionChecked.value
                      · simp [compileStmtChecked?, hCondition, hThen, hElse,
                          hTruthy] at hCompile
                        cases hCompile
                        have hConditionStructural :
                            structuralBoolExprValue? condition =
                              some conditionChecked.value :=
                          compileBoolExprChecked?_structuralBoolExprValue?
                            hCondition
                        have hThenStructural :
                            structuralStmtValue? thenBranch =
                              some thenChecked.value :=
                          compileStmtChecked?_structuralStmtValue? hThen
                        have hElseStructural :
                            structuralStmtValue? elseBranch =
                              some elseChecked.value :=
                          compileStmtChecked?_structuralStmtValue? hElse
                        simp [structuralStmtValue?, hConditionStructural,
                          hThenStructural, hElseStructural, hTruthy]
                      · simp [compileStmtChecked?, hCondition, hThen, hElse,
                          hTruthy] at hCompile
                        cases hCompile
                        have hConditionStructural :
                            structuralBoolExprValue? condition =
                              some conditionChecked.value :=
                          compileBoolExprChecked?_structuralBoolExprValue?
                            hCondition
                        have hThenStructural :
                            structuralStmtValue? thenBranch =
                              some thenChecked.value :=
                          compileStmtChecked?_structuralStmtValue? hThen
                        have hElseStructural :
                            structuralStmtValue? elseBranch =
                              some elseChecked.value :=
                          compileStmtChecked?_structuralStmtValue? hElse
                        simp [structuralStmtValue?, hConditionStructural,
                          hThenStructural, hElseStructural, hTruthy]
  | functions, L00_SourceSolidity.Stmt.empty, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.varDecl bindings init, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.expr expr, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.whileLoop condition body, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.doWhile body condition, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.forLoop init condition post body,
      checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.tryCatch expr clauses, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.tryCatchReturns expr params success
      clauses, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.emitEvent expr, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.revertCall expr, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.break, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.continue, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.unchecked body, checked, hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.inlineAssembly source, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile
  | functions, L00_SourceSolidity.Stmt.modifierPlaceholder, checked,
      hCompile => by
      simp [compileStmtChecked?] at hCompile

theorem structuralStmtValue?_compileStmtChecked?_exists :
    ∀ {functions : List L00_SourceSolidity.FunctionDecl}
      {source : L00_SourceSolidity.Stmt}
      {value : L01_ValidSolidity.Word},
      structuralStmtValue? source = some value ->
        ∃ checked : CheckedStmt functions source,
          compileStmtChecked? functions source = some checked ∧
            checked.value = value
  | functions, L00_SourceSolidity.Stmt.returnValues maybeExpr, value,
      hStructural => by
      cases maybeExpr with
      | none =>
          simp [structuralStmtValue?] at hStructural
      | some expr =>
          rcases structuralExprValue?_compileExprChecked?_exists hStructural with
            ⟨exprChecked, hExprCompile, hExprValue⟩
          cases hCompile :
              compileStmtChecked? functions
                (L00_SourceSolidity.Stmt.returnValues (some expr)) with
          | none =>
              simp [compileStmtChecked?, hExprCompile] at hCompile
          | some checked =>
              refine
                ⟨checked,
                  by simpa [compileStmtChecked?, hExprCompile] using hCompile,
                  ?_⟩
              have hCompileStructural :
                  structuralStmtValue?
                      (L00_SourceSolidity.Stmt.returnValues (some expr)) =
                    some checked.value :=
                compileStmtChecked?_structuralStmtValue? hCompile
              rw [hStructural] at hCompileStructural
              injection hCompileStructural with hValue
              exact hValue.symm
  | functions, L00_SourceSolidity.Stmt.block body, value, hStructural => by
      cases body with
      | nil =>
          simp [structuralStmtValue?] at hStructural
      | cons stmt rest =>
          cases rest with
          | nil =>
              have hStmtStructural :
                  structuralStmtValue? stmt = some value := by
                simpa [structuralStmtValue?] using hStructural
              rcases structuralStmtValue?_compileStmtChecked?_exists
                  (functions := functions) hStmtStructural with
                ⟨stmtChecked, hStmtCompile, hStmtValue⟩
              cases hCompile :
                  compileStmtChecked? functions
                    (L00_SourceSolidity.Stmt.block [stmt]) with
              | none =>
                  simp [compileStmtChecked?, hStmtCompile] at hCompile
              | some checked =>
                  refine
                    ⟨checked,
                      by simpa [compileStmtChecked?, hStmtCompile]
                        using hCompile,
                      ?_⟩
                  have hCompileStructural :
                      structuralStmtValue?
                          (L00_SourceSolidity.Stmt.block [stmt]) =
                        some checked.value :=
                    compileStmtChecked?_structuralStmtValue? hCompile
                  rw [hStructural] at hCompileStructural
                  injection hCompileStructural with hValue
                  exact hValue.symm
          | cons stmt' rest' =>
              simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.ifElse condition thenBranch maybeElse,
      value, hStructural => by
      cases maybeElse with
      | none =>
          simp [structuralStmtValue?] at hStructural
      | some elseBranch =>
          cases hConditionStructural : structuralBoolExprValue? condition with
          | none =>
              simp [structuralStmtValue?, hConditionStructural] at hStructural
          | some conditionValue =>
              cases hThenStructural : structuralStmtValue? thenBranch with
              | none =>
                  simp [structuralStmtValue?, hConditionStructural,
                    hThenStructural] at hStructural
              | some thenValue =>
                  cases hElseStructural : structuralStmtValue? elseBranch with
                  | none =>
                      simp [structuralStmtValue?, hConditionStructural,
                        hThenStructural, hElseStructural] at hStructural
                  | some elseValue =>
                      by_cases hTruthy :
                          SolidCore.Solidity.Source.wordTruthy conditionValue
                      · simp [structuralStmtValue?, hConditionStructural,
                          hThenStructural, hElseStructural, hTruthy]
                          at hStructural
                        cases hStructural
                        rcases structuralBoolExprValue?_compileBoolExprChecked?_exists
                            hConditionStructural with
                          ⟨conditionChecked, hConditionCompile,
                            hConditionValue⟩
                        rcases structuralStmtValue?_compileStmtChecked?_exists
                            (functions := functions) hThenStructural with
                          ⟨thenChecked, hThenCompile, hThenValue⟩
                        rcases structuralStmtValue?_compileStmtChecked?_exists
                            (functions := functions) hElseStructural with
                          ⟨elseChecked, hElseCompile, hElseValue⟩
                        cases hConditionValue
                        cases hThenValue
                        cases hElseValue
                        cases hCompile :
                            compileStmtChecked? functions
                              (L00_SourceSolidity.Stmt.ifElse condition
                                thenBranch (some elseBranch)) with
                        | none =>
                            simp [compileStmtChecked?, hConditionCompile,
                              hThenCompile, hElseCompile, hTruthy]
                              at hCompile
                        | some checked =>
                            refine
                              ⟨checked,
                                by
                                  simpa [compileStmtChecked?,
                                    hConditionCompile, hThenCompile,
                                    hElseCompile, hTruthy] using hCompile,
                                ?_⟩
                            have hCompileStructural :
                                structuralStmtValue?
                                    (L00_SourceSolidity.Stmt.ifElse condition
                                      thenBranch (some elseBranch)) =
                                  some checked.value :=
                              compileStmtChecked?_structuralStmtValue?
                                hCompile
                            simp [structuralStmtValue?, hConditionStructural,
                              hThenStructural, hElseStructural, hTruthy]
                              at hCompileStructural
                            exact hCompileStructural.symm
                      · simp [structuralStmtValue?, hConditionStructural,
                          hThenStructural, hElseStructural, hTruthy]
                          at hStructural
                        cases hStructural
                        rcases structuralBoolExprValue?_compileBoolExprChecked?_exists
                            hConditionStructural with
                          ⟨conditionChecked, hConditionCompile,
                            hConditionValue⟩
                        rcases structuralStmtValue?_compileStmtChecked?_exists
                            (functions := functions) hThenStructural with
                          ⟨thenChecked, hThenCompile, hThenValue⟩
                        rcases structuralStmtValue?_compileStmtChecked?_exists
                            (functions := functions) hElseStructural with
                          ⟨elseChecked, hElseCompile, hElseValue⟩
                        cases hConditionValue
                        cases hThenValue
                        cases hElseValue
                        cases hCompile :
                            compileStmtChecked? functions
                              (L00_SourceSolidity.Stmt.ifElse condition
                                thenBranch (some elseBranch)) with
                        | none =>
                            simp [compileStmtChecked?, hConditionCompile,
                              hThenCompile, hElseCompile, hTruthy]
                              at hCompile
                        | some checked =>
                            refine
                              ⟨checked,
                                by
                                  simpa [compileStmtChecked?,
                                    hConditionCompile, hThenCompile,
                                    hElseCompile, hTruthy] using hCompile,
                                ?_⟩
                            have hCompileStructural :
                                structuralStmtValue?
                                    (L00_SourceSolidity.Stmt.ifElse condition
                                      thenBranch (some elseBranch)) =
                                  some checked.value :=
                              compileStmtChecked?_structuralStmtValue?
                                hCompile
                            simp [structuralStmtValue?, hConditionStructural,
                              hThenStructural, hElseStructural, hTruthy]
                              at hCompileStructural
                            exact hCompileStructural.symm
  | functions, L00_SourceSolidity.Stmt.empty, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.varDecl bindings init, value,
      hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.expr expr, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.whileLoop condition body, value,
      hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.doWhile body condition, value,
      hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.forLoop init condition post body,
      value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.tryCatch expr clauses, value,
      hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.tryCatchReturns expr params success
      clauses, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.emitEvent expr, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.revertCall expr, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.break, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.continue, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.unchecked body, value, hStructural => by
      simp [structuralStmtValue?] at hStructural
  | functions, L00_SourceSolidity.Stmt.inlineAssembly source, value,
      hStructural => by
      simp [structuralStmtValue?] at hStructural
    | functions, L00_SourceSolidity.Stmt.modifierPlaceholder, value,
        hStructural => by
        simp [structuralStmtValue?] at hStructural

theorem compileFunctionChecked?_structuralFunctionValue?
    {source : L00_SourceSolidity.FunctionDecl}
    {checked : CheckedFunction source}
    (hCompile : compileFunctionChecked? source = some checked) :
      structuralFunctionValue? source = some checked.value := by
  cases source with
  | mk kind name params returns visibility mutability virtualFlag overrideSpec
      modifiers body =>
      cases kind <;> try simp [compileFunctionChecked?] at hCompile
      case function =>
        cases name with
        | none =>
            simp [compileFunctionChecked?] at hCompile
        | some sourceName =>
            cases params with
            | nil =>
                cases returns with
                | nil =>
                    simp [compileFunctionChecked?] at hCompile
                | cons returnParam returnRest =>
                    cases returnRest with
                    | cons returnParam' returnRest' =>
                        simp [compileFunctionChecked?] at hCompile
                    | nil =>
                        cases returnParam with
                        | mk returnName returnTy returnLocation =>
                            cases returnTy <;> try
                              simp [compileFunctionChecked?] at hCompile
                            case uint bits =>
                              by_cases hBits : bits = 256
                              · subst bits
                                cases visibility with
                                | none =>
                                    simp [compileFunctionChecked?] at hCompile
                                | some visibilityValue =>
                                    cases visibilityValue <;> try
                                      simp [compileFunctionChecked?] at hCompile
                                    ·
                                      cases mutability <;> try
                                        simp [compileFunctionChecked?] at hCompile
                                      ·
                                        cases modifiers with
                                        | cons modifier rest =>
                                            simp [compileFunctionChecked?]
                                              at hCompile
                                        | nil =>
                                            cases body with
                                            | none =>
                                                simp [compileFunctionChecked?]
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
                                                  compileFunctionChecked? fn =
                                                    some checked at hCompile
                                                change
                                                  structuralFunctionValue? fn =
                                                    some checked.value
                                                cases hStmt :
                                                    compileStmtChecked? [fn]
                                                      body with
                                                | none =>
                                                    simp [fn,
                                                      compileFunctionChecked?,
                                                      hStmt] at hCompile
                                                | some stmtChecked =>
                                                    have hCompile' := hCompile
                                                    simp [fn,
                                                      compileFunctionChecked?,
                                                      hStmt] at hCompile'
                                                    cases hCompile'
                                                    have hStmtStructural :
                                                        structuralStmtValue?
                                                            body =
                                                          some
                                                            stmtChecked.value :=
                                                      compileStmtChecked?_structuralStmtValue?
                                                        hStmt
                                                    simpa [fn,
                                                      structuralFunctionValue?]
                                                      using hStmtStructural
                              · simp [compileFunctionChecked?, hBits]
                                  at hCompile
            | cons param rest =>
                simp [compileFunctionChecked?] at hCompile

theorem structuralFunctionValue?_compileFunctionChecked?_exists
    {source : L00_SourceSolidity.FunctionDecl}
    {value : L01_ValidSolidity.Word}
    (hStructural : structuralFunctionValue? source = some value) :
      ∃ checked : CheckedFunction source,
        compileFunctionChecked? source = some checked ∧
          checked.value = value := by
  cases source with
  | mk kind name params returns visibility mutability virtualFlag overrideSpec
      modifiers body =>
      cases kind <;> try simp [structuralFunctionValue?] at hStructural
      case function =>
        cases name with
        | none =>
            simp [structuralFunctionValue?] at hStructural
        | some sourceName =>
            cases params with
            | nil =>
                cases returns with
                | nil =>
                    simp [structuralFunctionValue?] at hStructural
                | cons returnParam returnRest =>
                    cases returnRest with
                    | cons returnParam' returnRest' =>
                        simp [structuralFunctionValue?] at hStructural
                    | nil =>
                        cases returnParam with
                        | mk returnName returnTy returnLocation =>
                            cases returnTy <;> try
                              simp [structuralFunctionValue?] at hStructural
                            case uint bits =>
                              by_cases hBits : bits = 256
                              · subst bits
                                cases visibility with
                                | none =>
                                    simp [structuralFunctionValue?]
                                      at hStructural
                                | some visibilityValue =>
                                    cases visibilityValue <;> try
                                      simp [structuralFunctionValue?]
                                        at hStructural
                                    ·
                                      cases mutability <;> try
                                        simp [structuralFunctionValue?]
                                          at hStructural
                                      ·
                                        cases modifiers with
                                        | cons modifier rest =>
                                            simp [structuralFunctionValue?]
                                              at hStructural
                                        | nil =>
                                            cases body with
                                            | none =>
                                                simp [structuralFunctionValue?]
                                                  at hStructural
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
                                                  structuralFunctionValue? fn =
                                                    some value at hStructural
                                                change
                                                  ∃ checked :
                                                    CheckedFunction fn,
                                                    compileFunctionChecked?
                                                        fn =
                                                      some checked ∧
                                                    checked.value = value
                                                have hStmtStructural :
                                                    structuralStmtValue? body =
                                                      some value := by
                                                  simpa [fn,
                                                    structuralFunctionValue?]
                                                    using hStructural
                                                rcases
                                                  structuralStmtValue?_compileStmtChecked?_exists
                                                    (functions := [fn])
                                                    hStmtStructural with
                                                  ⟨stmtChecked, hStmtCompile,
                                                    hStmtValue⟩
                                                cases hCompile :
                                                    compileFunctionChecked?
                                                      fn with
                                                | none =>
                                                    simp [fn,
                                                      compileFunctionChecked?,
                                                      hStmtCompile]
                                                      at hCompile
                                                | some checked =>
                                                    refine
                                                      ⟨checked, ?_, ?_⟩
                                                    · simpa [fn,
                                                        compileFunctionChecked?,
                                                        hStmtCompile]
                                                        using hCompile
                                                    · have hCompile' :=
                                                        hCompile
                                                      simp [fn,
                                                        compileFunctionChecked?,
                                                        hStmtCompile]
                                                        at hCompile'
                                                      cases hCompile'
                                                      exact hStmtValue
                              · simp [structuralFunctionValue?, hBits]
                                  at hStructural
            | cons param rest =>
                simp [structuralFunctionValue?] at hStructural

theorem compileContractChecked?_structuralContractValue?
    {source : L00_SourceSolidity.ContractDecl}
    {checked : CheckedContract source}
    (hCompile : compileContractChecked? source = some checked) :
      structuralContractValue? source = some checked.value := by
  cases source with
  | mk kind contractName abstract bases items =>
      cases kind <;> try simp [compileContractChecked?] at hCompile
      case contract =>
        cases abstract <;> try simp [compileContractChecked?] at hCompile
        case false =>
          cases bases with
          | cons base rest =>
              simp [compileContractChecked?] at hCompile
          | nil =>
              cases items with
              | nil =>
                  simp [compileContractChecked?] at hCompile
              | cons item rest =>
                  cases rest with
                  | cons item' rest' =>
                      simp [compileContractChecked?] at hCompile
                  | nil =>
                      cases item <;> try
                        simp [compileContractChecked?] at hCompile
                      case function fn =>
                        let contract : L00_SourceSolidity.ContractDecl :=
                          { kind := L00_SourceSolidity.ContractKind.contract
                            name := contractName
                            abstract := false
                            bases := []
                            items :=
                              [L00_SourceSolidity.ContractItem.function fn] }
                        change
                          compileContractChecked? contract =
                            some checked at hCompile
                        change
                          structuralContractValue? contract =
                            some checked.value
                        cases hFn : compileFunctionChecked? fn with
                        | none =>
                            simp [contract, compileContractChecked?, hFn]
                              at hCompile
                        | some fnChecked =>
                            have hCompile' := hCompile
                            simp [contract, compileContractChecked?, hFn]
                              at hCompile'
                            cases hCompile'
                            have hFnStructural :
                                structuralFunctionValue? fn =
                                  some fnChecked.value :=
                              compileFunctionChecked?_structuralFunctionValue?
                                hFn
                            simpa [contract, structuralContractValue?]
                              using hFnStructural

theorem structuralContractValue?_compileContractChecked?_exists
    {source : L00_SourceSolidity.ContractDecl}
    {value : L01_ValidSolidity.Word}
    (hStructural : structuralContractValue? source = some value) :
      ∃ checked : CheckedContract source,
        compileContractChecked? source = some checked ∧
          checked.value = value := by
  cases source with
  | mk kind contractName abstract bases items =>
      cases kind <;> try simp [structuralContractValue?] at hStructural
      case contract =>
        cases abstract <;> try simp [structuralContractValue?] at hStructural
        case false =>
          cases bases with
          | cons base rest =>
              simp [structuralContractValue?] at hStructural
          | nil =>
              cases items with
              | nil =>
                  simp [structuralContractValue?] at hStructural
              | cons item rest =>
                  cases rest with
                  | cons item' rest' =>
                      simp [structuralContractValue?] at hStructural
                  | nil =>
                      cases item <;> try
                        simp [structuralContractValue?] at hStructural
                      case function fn =>
                        let contract : L00_SourceSolidity.ContractDecl :=
                          { kind := L00_SourceSolidity.ContractKind.contract
                            name := contractName
                            abstract := false
                            bases := []
                            items :=
                              [L00_SourceSolidity.ContractItem.function fn] }
                        change
                          structuralContractValue? contract =
                            some value at hStructural
                        change
                          ∃ checked : CheckedContract contract,
                            compileContractChecked? contract =
                              some checked ∧
                            checked.value = value
                        have hFnStructural :
                            structuralFunctionValue? fn = some value := by
                          simpa [contract, structuralContractValue?]
                            using hStructural
                        rcases
                          structuralFunctionValue?_compileFunctionChecked?_exists
                            hFnStructural with
                          ⟨fnChecked, hFnCompile, hFnValue⟩
                        cases hCompile :
                            compileContractChecked? contract with
                        | none =>
                            simp [contract, compileContractChecked?,
                              hFnCompile] at hCompile
                        | some checked =>
                            refine ⟨checked, ?_, ?_⟩
                            · simpa [contract, compileContractChecked?,
                                hFnCompile] using hCompile
                            · have hCompile' := hCompile
                              simp [contract, compileContractChecked?,
                                hFnCompile] at hCompile'
                              cases hCompile'
                              exact hFnValue

theorem compileSourceChecked?_structuralSourceValue?
    {source : L00_SourceSolidity.SourceUnit}
    {checked : CheckedProgram source}
    (hCompile : compileSourceChecked? source = some checked) :
      structuralSourceValue? source = some checked.value := by
  cases source with
  | mk items =>
      cases items with
      | nil =>
          simp [compileSourceChecked?] at hCompile
      | cons item rest =>
          cases rest with
          | cons item' rest' =>
              simp [compileSourceChecked?] at hCompile
          | nil =>
              cases item <;> try simp [compileSourceChecked?] at hCompile
              case contract contract =>
                let sourceUnit : L00_SourceSolidity.SourceUnit :=
                  { items := [L00_SourceSolidity.SourceItem.contract contract] }
                change
                  compileSourceChecked? sourceUnit =
                    some checked at hCompile
                change
                  structuralSourceValue? sourceUnit =
                    some checked.value
                cases hContract : compileContractChecked? contract with
                | none =>
                    simp [sourceUnit, compileSourceChecked?, hContract]
                      at hCompile
                | some contractChecked =>
                    have hCompile' := hCompile
                    simp [sourceUnit, compileSourceChecked?, hContract]
                      at hCompile'
                    cases hCompile'
                    have hContractStructural :
                        structuralContractValue? contract =
                          some contractChecked.value :=
                      compileContractChecked?_structuralContractValue?
                        hContract
                    simpa [sourceUnit, structuralSourceValue?]
                      using hContractStructural

theorem structuralSourceValue?_compileSourceChecked?_exists
    {source : L00_SourceSolidity.SourceUnit}
    {value : L01_ValidSolidity.Word}
    (hStructural : structuralSourceValue? source = some value) :
      ∃ checked : CheckedProgram source,
        compileSourceChecked? source = some checked ∧
          checked.value = value := by
  cases source with
  | mk items =>
      cases items with
      | nil =>
          simp [structuralSourceValue?] at hStructural
      | cons item rest =>
          cases rest with
          | cons item' rest' =>
              simp [structuralSourceValue?] at hStructural
          | nil =>
              cases item <;> try simp [structuralSourceValue?] at hStructural
              case contract contract =>
                let sourceUnit : L00_SourceSolidity.SourceUnit :=
                  { items := [L00_SourceSolidity.SourceItem.contract contract] }
                change
                  structuralSourceValue? sourceUnit =
                    some value at hStructural
                change
                  ∃ checked : CheckedProgram sourceUnit,
                    compileSourceChecked? sourceUnit = some checked ∧
                    checked.value = value
                have hContractStructural :
                    structuralContractValue? contract = some value := by
                  simpa [sourceUnit, structuralSourceValue?]
                    using hStructural
                rcases
                  structuralContractValue?_compileContractChecked?_exists
                    hContractStructural with
                  ⟨contractChecked, hContractCompile, hContractValue⟩
                cases hCompile : compileSourceChecked? sourceUnit with
                | none =>
                    simp [sourceUnit, compileSourceChecked?,
                      hContractCompile] at hCompile
                | some checked =>
                    refine ⟨checked, ?_, ?_⟩
                    · simpa [sourceUnit, compileSourceChecked?,
                        hContractCompile] using hCompile
                    · have hCompile' := hCompile
                      simp [sourceUnit, compileSourceChecked?,
                        hContractCompile] at hCompile'
                      cases hCompile'
                      exact hContractValue

def accepted? (source : L00_SourceSolidity.SourceUnit) : Bool :=
  if source.items.isEmpty then
    true
  else
    (structuralSourceValue? source).isSome

def Accepted (source : L00_SourceSolidity.SourceUnit) : Prop :=
  accepted? source = true

theorem accepted?_eq_true_iff (source : L00_SourceSolidity.SourceUnit) :
    accepted? source = true ↔ Accepted source := by
  rfl

def check? (source : L00_SourceSolidity.SourceUnit) : Option Artifact :=
  if source.items.isEmpty then
    some
      { program := L01_ValidSolidity.Program.empty
        wf := L01_ValidSolidity.Program.empty_wf }
  else
    match compileSourceChecked? source with
    | some checked =>
        some
          { program := checked.program
            wf := checked.wf }
    | none => none

structure SoundnessBoundary
    (_source : L00_SourceSolidity.SourceUnit) (_artifact : Artifact)
    (behavior : L01_ValidSolidity.Behavior) :
    Prop where
  sourceAccepted : Accepted _source
  sourceSemantics :
    L00_SourceSolidity.Executable.Semantics _source behavior
  validSoliditySemantics :
    L01_ValidSolidity.Semantics _artifact.program
      behavior

theorem check?_sound
    {source : L00_SourceSolidity.SourceUnit} {artifact : Artifact}
    (hCheck : check? source = some artifact) :
    ∃ behavior, SoundnessBoundary source artifact behavior := by
  by_cases hEmpty : source.items.isEmpty
  · simp [check?, hEmpty] at hCheck
    cases hCheck
    exact
      ⟨L01_ValidSolidity.Behavior.stopped,
        { sourceAccepted := by simp [Accepted, accepted?, hEmpty]
          sourceSemantics := by
            cases source with
            | mk items =>
                cases items <;> simp at hEmpty
                exact L00_SourceSolidity.Executable.Semantics.empty rfl
          validSoliditySemantics :=
            L01_ValidSolidity.Program.empty_semantics }⟩
  · cases hChecked : compileSourceChecked? source with
    | none =>
        simp [check?, hEmpty, hChecked] at hCheck
    | some checked =>
        simp [check?, hEmpty, hChecked] at hCheck
        cases hCheck
        exact
          ⟨L01_ValidSolidity.Behavior.returnedWord checked.value,
            { sourceAccepted := by
                have hStructural :
                    structuralSourceValue? source = some checked.value :=
                  compileSourceChecked?_structuralSourceValue? hChecked
                simp [Accepted, accepted?, hEmpty, hStructural]
              sourceSemantics := checked.sourceSemantics
              validSoliditySemantics :=
                L01_ValidSolidity.Semantics.returnValue
                  ⟨checked.returnedExpr, checked.returned,
                    checked.eval⟩ }⟩

theorem check?_complete_for_accepted
    {source : L00_SourceSolidity.SourceUnit}
    (hAccepted : Accepted source) :
    ∃ artifact, check? source = some artifact := by
  by_cases hEmpty : source.items.isEmpty
  · exact
      ⟨{ program := L01_ValidSolidity.Program.empty
         wf := L01_ValidSolidity.Program.empty_wf },
        by simp [check?, hEmpty]⟩
  · cases hStructural : structuralSourceValue? source with
    | none =>
        simp [Accepted, accepted?, hEmpty, hStructural] at hAccepted
    | some value =>
        rcases structuralSourceValue?_compileSourceChecked?_exists
            hStructural with
          ⟨checked, hChecked, hValue⟩
        exact
          ⟨{ program := checked.program
             wf := checked.wf },
            by simp [check?, hEmpty, hChecked]⟩

end P01_SourceSolidityToValidSolidity
end Passes
end Spine
end SolidCore

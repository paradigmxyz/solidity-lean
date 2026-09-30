import SolidCore.Solidity.Interface.Expressions

namespace SolidCore.Solidity.Executable

set_option maxHeartbeats 1000000 in
/-- Bundled env-aware statement-lowering context: `Stmt.lowerCore?` takes it
as `Option` — `some` is the env-aware mode, `none` the env-free mode. -/
structure StmtLoweringCtx where
  storageRefEnv : StorageRefEnv
  env : TypeEnv
  externalCallKindEnv : ExternalCallKindEnv
  modifiers : List SourceModifierDecl
  functions : List FunctionDecl
  freeFunctions : List FunctionDecl
  returnTys : List Ty

/-- LIB-STORAGE-RETURN-USE, ARRAY-FIELD push/pop: peel an INDEX SPINE off an
    expression rooted at a direct call — `f(args)[i]…[k]` — returning the callee
    name, the call arguments, and the index expressions outermost-last. After the
    struct-member→index rewrite, `L.ref(s).a.push(v)` arrives as push on
    `<call>[fieldIndex]`, and deeper nests (`struct-in-struct` array fields,
    mapping-of-array values) add further indexes; the push/pop arms in
    `Stmt.lowerCore?` use this spine to route the operation through the captured
    storage-ref temp (`storageArrayPushRefPath`/`storageArrayPopRefPath`). -/
def Expr.callRootedIndexSpine? : Expr -> Option (Name × List Arg × List Expr)
  | Expr.index (Expr.call (Expr.ident name) args) index =>
      some (name, args, [index])
  | Expr.index base index => do
      let (name, args, indexes) ← Expr.callRootedIndexSpine? base
      some (name, args, indexes ++ [index])
  | _ => none

/-- Walk a callee's (resolved) return type down an index spine: a STRUCT peels
    by the rewritten literal FIELD index, an array by its element, a mapping by
    its value. Used by the ARRAY-FIELD push arm to recover the pushed value's
    element type so NARROW-PUSH (#183) operand-width cleanup applies through a
    returned storage ref exactly as it does for storage-ref locals; `none`
    keeps that shape's prior over-reject (never a silently-wrapping accept). -/
def Ty.peelIndexSpineTy? : Ty -> List Expr -> Option Ty
  | ty, [] => some ty
  | Ty.struct _ fieldTys, index :: rest => do
      let fieldIndex ←
        match index with
        | Expr.literal (Literal.number numeral) => numeral.toNat?
        | _ => none
      let fieldTy ← fieldTys[fieldIndex]?
      Ty.peelIndexSpineTy? fieldTy rest
  | Ty.array elemTy _, _ :: rest => Ty.peelIndexSpineTy? elemTy rest
  | Ty.mapping _ valueTy, _ :: rest => Ty.peelIndexSpineTy? valueTy rest
  | _, _ => none


set_option maxHeartbeats 2000000 in
mutual

def modifierParamBindingsToCoreWithEnv? (storageNames : List Name) :
    StorageRefEnv -> TypeEnv -> List Stmt -> Option (List CoreStmt)
  | _, _, [] => some []
  | storageRefEnv, env,
      Stmt.varDecl [binding] (some expr) :: rest => do
      let name ← binding.name
      let ty ← binding.ty
      let param : Parameter :=
        { name := some name, ty := ty, location := binding.location }
      let head ←
        Parameter.toStorageAwareCoreArgDecl?
          storageRefEnv storageNames env "_sol_mod" 0 param expr
      let tail ←
        modifierParamBindingsToCoreWithEnv? storageNames
          (VarBinding.extendStorageRefEnv storageRefEnv binding)
          (VarBinding.extendTypeEnv env binding) rest
      some (head :: tail)
  | _, _, _ => none
termination_by _ _ stmts => (1, 0, stmts.length, 0)

def modifierApplyToCoreWithEnv? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv)
    (storageNames returnNames : List Name)
    (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : CoreStmt) :
    Option CoreStmt := do
  let body ← decl.body
  let body := ModifierDecl.aliasParamsInBody decl body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  let prefixCore ←
    modifierParamBindingsToCoreWithEnv?
      storageNames storageRefEnv env prefixStmts
  let modifierEnv :=
    Parameters.extendTypeEnv "_mod" env (ModifierDecl.aliasedParams decl)
  let body := Stmt.annotateAbi modifierEnv body
  let bodyCore ←
    Stmt.toCoreReplacingModifierPlaceholder?
      storageNames returnNames inner body
  some (SolidCore.Solidity.Source.Stmt.block (prefixCore ++ [bodyCore]))
termination_by (2, 0, 0, 0)

def Stmt.toCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt) :
    Stmt -> Option CoreStmt
  | Stmt.modifierPlaceholder =>
      some (SolidCore.Solidity.Source.Stmt.captureReturn
        returnNames replacement)
  | Stmt.block body => do
      let coreBody ←
        Stmt.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.ifElse cond thenBranch elseBranch => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement thenBranch
      let elseCore ←
        match elseBranch with
        | some stmt =>
            Stmt.toCoreReplacingModifierPlaceholder?
              storageNames returnNames replacement stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      some (SolidCore.Solidity.Source.Stmt.ifElse
        condCore thenCore elseCore)
  | Stmt.whileLoop cond body => do
      let condCore ← Expr.toCore? storageNames cond
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
  | Stmt.doWhile body cond => do
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      let condCore ← Expr.toCore? storageNames cond
      some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
  | Stmt.forLoop init cond post body => do
      let initCore ←
        match init with
        | some stmt =>
            Stmt.toCoreReplacingModifierPlaceholder?
              storageNames returnNames replacement stmt
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let condCore ←
        match cond with
        | some expr => Expr.toCore? storageNames expr
        | none => some (SolidCore.Solidity.Source.Expr.word 1)
      let postCore ←
        match post with
        | some expr => Stmt.toCore? storageNames (Stmt.expr expr)
        | none => some SolidCore.Solidity.Source.Stmt.skip
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.forLoop
        initCore condCore postCore bodyCore)
  | Stmt.tryCatch expr clauses => do
      let catchCore ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clauses
      match Expr.toExternalCall? storageNames expr with
      | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) =>
          let checkTargetCode :=
            Expr.externalCallNeedsCodeCheckWithEnv [] [] expr
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              kind targetCore calldataCore valueCore gasCore? gasFirst
              checkTargetCode [] []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
            Expr.toContractCreation? storageNames expr
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? valueBeforeSalt []
              SolidCore.Solidity.Source.Stmt.skip catchCore)
  | Stmt.tryCatchReturns expr returns success clauses => do
      let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
      let returnAbiCleanups ←
        Tys.toCoreAbiCleanups? (returns.map Parameter.ty)
      let successCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement success
      let catchCore ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clauses
      match Expr.toExternalCall? storageNames expr with
      | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) =>
          let checkTargetCode :=
            Expr.externalCallNeedsCodeCheckWithEnv []
              (returns.map Parameter.ty) expr
          some
            (SolidCore.Solidity.Source.Stmt.tryExternalCall
              kind targetCore calldataCore valueCore gasCore? gasFirst
              checkTargetCode returnBindings returnAbiCleanups
              successCore catchCore)
      | none => do
          let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
            Expr.toContractCreation? storageNames expr
          some
            (SolidCore.Solidity.Source.Stmt.tryContractCreate
              contractName argsCore valueCore saltCore? valueBeforeSalt returnBindings
              successCore catchCore)
  | Stmt.unchecked body => do
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
  | other => Stmt.toCore? storageNames other
termination_by stmt => (1, 0, sizeOf stmt, 0)

def CatchClause.toCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match clause with
  | CatchClause.clause name params body => do
      let bindings ← Parameters.toCoreTryBindings? "_catch" params
      let bodyCore ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement body
      some
        (SolidCore.Solidity.Source.TryCatchClause.clause
          name bindings bodyCore)
termination_by (1, 0, sizeOf clause, 2)

def CatchClause.listToCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match clauses with
  | [] => some []
  | clause :: rest => do
      let head ←
        CatchClause.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement clause
      let tail ←
        CatchClause.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement rest
      some (head :: tail)
termination_by (1, 0, sizeOf clauses, 4)

def Stmt.listToCoreReplacingModifierPlaceholder?
    (storageNames returnNames : List Name) (replacement : CoreStmt)
    (stmts : List Stmt) : Option (List CoreStmt) :=
  match stmts with
  | [] => some []
  | stmt :: rest => do
      let head ←
        Stmt.toCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement stmt
      let tail ←
        Stmt.listToCoreReplacingModifierPlaceholder?
          storageNames returnNames replacement rest
      some (head :: tail)
termination_by (1, 0, sizeOf stmts, 2)

def functionExpandModifiersToCoreWithInternalCalls?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (invocations : List SourceModifierInvocation) (body : Stmt) :
    Option CoreStmt :=
  match invocations with
  | [] =>
      Stmt.toCoreWithInternalCalls?
        (internalFuel := internalFuel)
        (storageRefEnv := storageRefEnv)
        (env := env)
        (externalCallKindEnv := externalCallKindEnv)
        (storageNames := storageNames)
        (modifiers := available)
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := body)
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCoreWithInternalCalls?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          returnNames available functions freeFunctions returnTys rest body
      let modifierDecl ← modifierResolve? available invocation.target
      modifierApplyToCoreWithEnv? storageRefEnv env storageNames returnNames
        modifierDecl invocation inner
termination_by (3, internalFuel, sizeOf invocations + sizeOf body, 12)

/-- Elaborate call arguments to core expressions for the function-boundary
    representation: one core temp per parameter (source order, so left-to-right
    argument evaluation is preserved exactly as the inline path did), plus a pure
    `var` read per temp for the `internalCall` node's argument list. Stack-value
    params only (guaranteed by the `isBoundaryCallee` guard at the call
    site), so the storage/memory-ref branches of
    `Parameter.toStorageAwareCoreArgDecl?` are unreachable here. The temp names
    use a fresh (`_ic_arg_*`) prefix — never the parameter name — so an argument
    expression that reads a same-named caller local is not clobbered; the arm
    binds arguments to the callee's parameters positionally (`initialFrame?`), so
    the temp name is irrelevant to the callee. -/
def Parameters.boundaryArgDecls?
    (storageRefEnv : StorageRefEnv) (storageNames : List Name) (env : TypeEnv)
    (fallbackPrefix : String) :
    Nat -> List Parameter -> List Expr ->
    Option (List CoreStmt × List CoreExpr)
  | _, [], [] => some ([], [])
  | index, param :: params, arg :: args => do
      let name := fallbackPrefix ++ toString index
      -- One reference-preserving temp per parameter, source order (left-to-right
      -- argument evaluation preserved). `toStorageAwareCoreArgDecl?` picks the
      -- decl per data location: a `storage` ref lowers to a `storageAlias*`
      -- statement binding the temp to the storage pointer VALUE; a `memory` ref
      -- to a `memoryVarDecl` that *aliases* the caller's memory pointer when the
      -- argument is a bare memory variable; a value to a plain `varDecl`. The
      -- temp NAME is forced to `_ic_arg_<i>` (`param.name := none`) — never the
      -- parameter name — so it cannot shadow a same-named caller local read by a
      -- later argument. The `internalCall` node's argument list is the pure temp
      -- reads, evaluated reference-preservingly by the arm.
      let decl ←
        Parameter.toStorageAwareCoreArgDecl? storageRefEnv storageNames env
          fallbackPrefix index { param with name := none } arg
      let (tailDecls, tailVars) ←
        Parameters.boundaryArgDecls? storageRefEnv storageNames env
          fallbackPrefix (index + 1) params args
      some
        ( decl :: tailDecls
        , SolidCore.Solidity.Source.Expr.var name :: tailVars )
  | _, _, _ => none

/-- Function-boundary form of `internalCallParts?` for stack-value callees:
    declare per-arg core temps + default return temps, and emit a single
    `Stmt.internalCall` targeting the return temps. The callee body is NOT
    inlined here — it lives once in the function table under `internalTableKey?`,
    so recursion / deep nesting elaborate (no inline fuel consumed). Returns the
    same 4-tuple shape as `internalCallParts?` so every wrapper caller is
    unchanged: wrapping the node in `captureReturn` is a harmless passthrough
    (the node maps the callee's returns to `Result.normal` internally, so
    `captureReturn` never rewrites it). Reference-signature extension: the return
    decls are already storage-aware (`toStorageAwareDefaultCoreDecls?` emits a
    `storageAlias` target for a `storage`-ref return; `storageRefFlags` marks
    it), and the argument decls are reference-preserving temps
    (`boundaryArgDecls?`), so this handles value, `memory`-ref, and `storage`-ref
    signatures uniformly. -/
def FunctionDecl.boundaryCallParts?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv) (storageNames : List Name)
    (name : Name) (callee : FunctionDecl) (sourceArgs : List Expr) :
    Option (List CoreBindingDecl × List Bool × List CoreStmt × CoreStmt) := do
  if FunctionDecl.isBoundaryCallee callee then some () else none
  let tableKey ← FunctionDecl.internalTableKey? callee
  let returnPrefix := "_ret_" ++ name ++ "_"
  let runtimeReturns := Parameters.withRuntimeNames returnPrefix callee.returns
  let returnBindings ← Parameters.toCoreBindings? returnPrefix runtimeReturns
  let returnDecls ←
    Parameters.toStorageAwareDefaultCoreDecls? returnPrefix runtimeReturns
  let returnStorageRefs := Parameters.storageRefFlags runtimeReturns
  let (argDecls, argVars) ←
    Parameters.boundaryArgDecls? storageRefEnv storageNames env "_ic_arg_" 0
      callee.params sourceArgs
  let returnNames :=
    returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
  some
    ( returnBindings
    , returnStorageRefs
    , argDecls ++ returnDecls
    , SolidCore.Solidity.Source.Stmt.internalCall returnNames tableKey argVars )

/-- Stage C (boundary-completion arc): elaborate a call through an internal
    function POINTER — `name` is not a declared function but a fn-typed
    local/parameter/state variable. The pointer expression elaborates as an
    ordinary read (local `var` / storage load with the 64-bit mask); the call
    becomes `Stmt.internalCallPtr`, resolved by dispatch ID at run time (miss
    -> Panic 0x51). Same reference-preserving arg/return temp construction as
    `boundaryCallParts?`, with the parameter/return shapes taken from the
    function TYPE. -/
def FunctionDecl.ptrBoundaryCallCoreParts?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv) (storageNames : List Name)
    (fnTy : Ty) (fnCore : CoreExpr) (returnPrefix : String) (args : List Arg) :
    Option (List CoreBindingDecl × List Bool × List CoreStmt × CoreStmt) := do
  match fnTy with
  | Ty.functionWithLocations paramTys paramLocs returnTys returnLocs _
      visibility =>
      (match visibility with
      | Visibility.external_ => none
      | _ => do
        if paramTys.length == paramLocs.length &&
            returnTys.length == returnLocs.length then
          some ()
        else
          none
        let params := List.zipWith
          (fun ty loc =>
            ({ name := none, ty := ty, location := loc } : Parameter))
          paramTys paramLocs
        let returns := List.zipWith
          (fun ty loc =>
            ({ name := none, ty := ty, location := loc } : Parameter))
          returnTys returnLocs
        if params.all Parameter.isBoundaryLocation &&
            returns.all Parameter.isBoundaryReturnLocation then
          some ()
        else
          none
        let sourceArgs ←
          mapOption
            (fun (arg : Arg) =>
              match arg with
              | Arg.positional value => some value
              | Arg.named _ _ => none)
            args
        if params.length == sourceArgs.length then some () else none
        let runtimeReturns := Parameters.withRuntimeNames returnPrefix returns
        let returnBindings ←
          Parameters.toCoreBindings? returnPrefix runtimeReturns
        let returnDecls ←
          Parameters.toStorageAwareDefaultCoreDecls? returnPrefix runtimeReturns
        let returnStorageRefs := Parameters.storageRefFlags runtimeReturns
        let (argDecls, argVars) ←
          Parameters.boundaryArgDecls? storageRefEnv storageNames env
            "_ic_arg_" 0 params sourceArgs
        let returnNames :=
          returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
        some
          ( returnBindings
          , returnStorageRefs
          , argDecls ++ returnDecls
          , SolidCore.Solidity.Source.Stmt.internalCallPtr
              returnNames fnCore argVars ))
  | _ => none

def FunctionDecl.ptrBoundaryCallExprParts?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv) (storageNames : List Name)
    (callee : Expr) (returnPrefix : String) (args : List Arg) :
    Option (List CoreBindingDecl × List Bool × List CoreStmt × CoreStmt) := do
  let fnTy ← Expr.abiTyWithEnv? env callee
  let fnCore ←
    if Expr.abiArgNeedsEnvCleanup? callee then
      Expr.indexBaseCoreWithEnvCleanup? storageNames env callee
    else
      Expr.toCore? storageNames callee
  FunctionDecl.ptrBoundaryCallCoreParts? storageRefEnv env storageNames
    fnTy fnCore returnPrefix args

def FunctionDecl.ptrBoundaryCallParts?
    (storageRefEnv : StorageRefEnv) (env : TypeEnv) (storageNames : List Name)
    (name : Name) (args : List Arg) :
    Option (List CoreBindingDecl × List Bool × List CoreStmt × CoreStmt) :=
  FunctionDecl.ptrBoundaryCallExprParts? storageRefEnv env storageNames
    (Expr.ident name) ("_ret_" ++ name ++ "_") args

/-- Resolve an internal call site and emit its function-boundary parts. Since
    stage E of the boundary-completion arc this is boundary-ONLY: the resolved
    callee elaborates to `Stmt.internalCall` against the function table
    (`boundaryCallParts?`), an unresolvable name is tried as a call through an
    internal function POINTER (`ptrBoundaryCallParts?`), and the historical
    inline-splice path (α-renaming callee bodies into the caller under
    `defaultInternalCallInlineFuel`) is DELETED — no callee kind splices
    anymore. `internalFuel` is retained by the surrounding elaboration cluster
    only as the nested-call-argument hoisting bound (see
    `defaultInternalCallInlineFuel`'s doc). -/
def FunctionDecl.internalCallParts?
    (_internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (_externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (_modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg) :
    Option (List CoreBindingDecl × List Bool × List CoreStmt × CoreStmt) :=
  match FunctionDecl.findInternalCalleeWithArgs?
      functions env name args with
  | some (callee, sourceArgs) =>
      FunctionDecl.boundaryCallParts? storageRefEnv env storageNames name
        callee sourceArgs
  | none =>
      match FunctionDecl.findInternalCalleeWithArgs?
          freeFunctions env name args with
      | some (callee, sourceArgs) =>
          FunctionDecl.boundaryCallParts? storageRefEnv env storageNames name
            callee sourceArgs
      | none =>
          FunctionDecl.ptrBoundaryCallParts?
            storageRefEnv env storageNames name args

def FunctionDecl.internalStatementCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg) :
    Option CoreStmt := do
  let (returnBindings, _, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  let returnNames :=
    returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
  some
    (SolidCore.Solidity.Source.Stmt.block
      (prefixCore ++
        [SolidCore.Solidity.Source.Stmt.captureReturn returnNames bodyCore]))
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalSingleReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt := do
  let (returnBindings, _, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  match returnBindings with
  | [ret] =>
      let retName := ret.name
      some
        (SolidCore.Solidity.Source.Stmt.block
          (prefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [retName] bodyCore
            , useResult (SolidCore.Solidity.Source.Expr.var retName) ]))
  | _ => none
termination_by (3, internalFuel, 0, 2)

/-- Snapshot the first `count` arguments of a residual internal call into typed
    temporaries.  This is used when a later argument has been hoisted for an
    internal call: Solidity evaluates arguments left-to-right, so earlier state
    reads must occur before that later call can mutate storage. -/
def Args.snapshotPrefixBeforeLaterCall?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (storageNames : List Name) (fallbackPrefix : String) :
    Nat -> Nat -> List Arg ->
      Option (List CoreStmt × List (Name × Ty) × List Arg)
  | 0, _, args => some ([], [], args)
  | _ + 1, _, [] => none
  | count + 1, counter, arg :: rest => do
      let argExpr :=
        match arg with
        | Arg.positional expr => expr
        | Arg.named _ expr => expr
      let argTy ←
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env argExpr
      let argCoreTy ← Ty.toCore? argTy
      let argCore ←
        match Expr.toCoreAsWithEnv? storageNames env argTy argExpr with
        | some core => some core
        | none => Expr.toCore? storageNames argExpr
      let tempName := internalCallArgTempName fallbackPrefix counter
      let (restPre, restEnv, restArgs) ←
        Args.snapshotPrefixBeforeLaterCall?
          functions freeFunctions env storageNames fallbackPrefix
          count (counter + 1) rest
      some
        ( CoreTy.tempDeclStmt argCoreTy tempName (some argCore) :: restPre
        , (tempName, argTy) :: restEnv
        , Arg.withExpr (Expr.ident tempName) arg :: restArgs )
termination_by count _ _ => count

def FunctionDecl.internalSingleReturnCallExprCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (expr : Expr)
    (useResult : CoreExpr -> CoreStmt) (depth : Nat := 0) :
    Option CoreStmt := do
  let (name, args, convert) ← Expr.internalSingleReturnCallConversion? expr
  -- Named-argument order (R1): reorder NAMED arguments into the callee's
  -- parameter-declaration order BEFORE peeling their nested calls into sibling
  -- temps, so `g({b: t(1), a: t(2)})` evaluates the `a` expression `t(2)` first
  -- (solc reorders named args to parameter order, then evaluates L2R). Argument
  -- binding was already correct via `orderedArgs?`; this fixes only the
  -- side-effecting-argument evaluation order. Positional calls are unchanged.
  let args := Expr.reorderNamedInternalCallArgs functions freeFunctions env
    (Expr.ident name) args
  -- #196 NESTED-CALL-TEMP-SHADOW: the hoisted-argument temp prefix is
  -- depth-suffixed. Every recursion level of this hoister previously claimed
  -- the SAME `_sol_internal_call_arg_eval0` name; the inner block's redeclared
  -- temp shadowed the outer one, so the inner call chain's result was
  -- assigned to the inner (scope-popped) shadow and the outer call read its
  -- never-assigned default — chains >= 3 deep computed garbage wherever this
  -- hoister fires. Depth 0 keeps the historical name byte-identically.
  let argTempPrefix :=
    if depth == 0 then "_sol_internal_call_arg"
    else "_sol_internal_call_arg_d" ++ toString depth
  match internalFuel with
  | fuel + 1 =>
      match
          Args.replaceInternalSingleReturnCallExprArg?
            argTempPrefix 0 args with
      | some (argIndex, argExpr, argTmp, replacedArgs) => do
          let argTy ←
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env argExpr
          let argCoreTy ← Ty.toCore? argTy
          let (priorPre, priorEnv, replacedArgs) ←
            Args.snapshotPrefixBeforeLaterCall?
              functions freeFunctions env storageNames
              (argTempPrefix ++ "_prior") argIndex 0 replacedArgs
          let envWithArgTmp := (argTmp, argTy) :: (priorEnv ++ env)
          let argCore ←
            FunctionDecl.internalSingleReturnCallExprCore?
              fuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions argExpr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var argTmp)
                  retExpr)
              (depth := depth + 1)
          let outerCore ←
            FunctionDecl.internalSingleReturnCallCore?
              fuel storageRefEnv envWithArgTmp externalCallKindEnv storageNames
              modifiers functions freeFunctions name replacedArgs
              (fun retExpr => useResult (convert retExpr))
          some
            (SolidCore.Solidity.Source.Stmt.block
              (priorPre ++
                [ SolidCore.Solidity.Source.Stmt.varDecl argCoreTy argTmp none
                , argCore
                , outerCore ]))
      | none =>
          FunctionDecl.internalSingleReturnCallCore?
            (fuel + 1) storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name args
            (fun retExpr => useResult (convert retExpr))
  | 0 =>
      FunctionDecl.internalSingleReturnCallCore?
        0 storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions name args
        (fun retExpr => useResult (convert retExpr))
termination_by (3, internalFuel, 0, 6)

def FunctionDecl.abiInternalSingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (fallbackPrefix : String) (expr : Expr)
    (useReplaced : Expr -> Option CoreStmt) : Option CoreStmt := do
  let (callExpr, tmpName, replacedExpr) ←
    Expr.replaceAbiInternalSingleReturnCall?
      functions env fallbackPrefix 0 expr
  let (_, retTy) ←
    match Expr.actualInternalSingleReturnCall? functions env callExpr with
    | some found => some found
    | none => Expr.actualInternalSingleReturnCall? freeFunctions env callExpr
  let tmpTy ← Ty.toCore? retTy
  let callCore ←
    FunctionDecl.internalSingleReturnCallExprCore?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions callExpr
      (fun retExpr =>
        SolidCore.Solidity.Source.Stmt.assign
          (SolidCore.Solidity.Source.LValue.var tmpName) retExpr)
  let replacedCore ← useReplaced replacedExpr
  some
    (SolidCore.Solidity.Source.Stmt.block
      [ SolidCore.Solidity.Source.Stmt.varDecl tmpTy tmpName none
      , callCore
      , replacedCore ])
termination_by (3, internalFuel, sizeOf expr + 1, 8)

def FunctionDecl.internalSingleStorageReturnRefCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (useRef : Name -> CoreStmt) : Option CoreStmt := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  match returnBindings, returnStorageRefs with
  | [ret], [true] =>
      let retName := ret.name
      some
        (SolidCore.Solidity.Source.Stmt.block
          (prefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [retName] bodyCore
            , useRef retName ]))
  | _, _ => none
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalSingleStorageReturnRefCorePieces?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (useRef : Name -> CoreStmt) : Option (List CoreStmt) := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  match returnBindings, returnStorageRefs with
  | [ret], [true] =>
      let retName := ret.name
      some
        (prefixCore ++
          [ SolidCore.Solidity.Source.Stmt.captureReturn
              [retName] bodyCore
          , useRef retName ])
  | _, _ => none
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalTwoSingleReturnCallsCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (firstName : Name) (firstArgs : List Arg)
    (secondName : Name) (secondArgs : List Arg)
    (firstTmp : Name) (useResults : CoreExpr -> CoreExpr -> CoreStmt) :
    Option CoreStmt := do
  let (firstBindings, _, firstPrefixCore, firstBodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions firstName firstArgs
  let (secondBindings, _, secondPrefixCore, secondBodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions secondName secondArgs
  match firstBindings, secondBindings with
  | [firstRet], [secondRet] =>
      let firstRetName := firstRet.name
      let secondRetName := secondRet.name
      some
        (SolidCore.Solidity.Source.Stmt.block
          (firstPrefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [firstRetName] firstBodyCore
            -- Aggregate-aware temp (see `CoreTy.tempDeclStmt`): a nested-
            -- dynamic first return (`uint256[][]`, `string[]`, struct with
            -- dynamic fields) is a memory POINTER; the historical plain
            -- `varDecl` copy spuriously Panic(0)'d on its nested memory
            -- refs where solc+EVM alias the pointer and encode the full
            -- payload (revert `Err(mk(), f())` / `emit E(mk(), f())`).
            , CoreTy.tempDeclStmt
                firstRet.ty firstTmp
                (some (SolidCore.Solidity.Source.Expr.var firstRetName)) ] ++
            secondPrefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [secondRetName] secondBodyCore
            , useResults
                (SolidCore.Solidity.Source.Expr.var firstTmp)
                (SolidCore.Solidity.Source.Expr.var secondRetName) ]))
  | _, _ => none
termination_by (3, internalFuel, 0, 2)

/-- Right-first twin of `internalTwoSingleReturnCallsCore?` for ORDINARY BINARY
    OPERANDS only: solc legacy evaluates the RIGHT operand's call FIRST, then
    the LEFT (ExpressionCompiler.cpp:614-615). The SECOND call runs first and
    its result is parked in `secondTmp`; argument-like positions
    (require/emit/revert two-arg forms) must keep using the left-to-right
    original. -/
def FunctionDecl.internalTwoSingleReturnCallsRightFirstCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (firstName : Name) (firstArgs : List Arg)
    (secondName : Name) (secondArgs : List Arg)
    (secondTmp : Name) (useResults : CoreExpr -> CoreExpr -> CoreStmt) :
    Option CoreStmt := do
  let (firstBindings, _, firstPrefixCore, firstBodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions firstName firstArgs
  let (secondBindings, _, secondPrefixCore, secondBodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions secondName secondArgs
  match firstBindings, secondBindings with
  | [firstRet], [secondRet] =>
      let firstRetName := firstRet.name
      let secondRetName := secondRet.name
      some
        (SolidCore.Solidity.Source.Stmt.block
          (secondPrefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [secondRetName] secondBodyCore
            -- Aggregate-aware temp (see the left-first twin above).
            , CoreTy.tempDeclStmt
                secondRet.ty secondTmp
                (some (SolidCore.Solidity.Source.Expr.var secondRetName)) ] ++
            firstPrefixCore ++
            [ SolidCore.Solidity.Source.Stmt.captureReturn
                [firstRetName] firstBodyCore
            , useResults
                (SolidCore.Solidity.Source.Expr.var firstRetName)
                (SolidCore.Solidity.Source.Expr.var secondTmp) ]))
  | _, _ => none
termination_by (3, internalFuel, 0, 2)

/-- §3c COLLAPSE + #201 (D/E) unification: the ONE lowering for every
    CALL-BEARING `emit E(...)` / `revert Err(...)` argument shape. The two
    families were isomorphic copy-paste (~10 dispatcher arms), and the copy
    had DIVERGED: the emit arms lowered their pure companion arguments
    env-aware (`Expr.abiArgCoreWithEnvCleanup?`, so narrow checked
    arithmetic Panics 0x11) while the revert arms lowered them env-less
    (`Expr.toCore?`, losing the Panic — `revert Err(a + b, bump())` with
    `uint8 a,b` encoded 300 where solc+EVM Panic 0x11). Both channels now
    route through THIS helper; they differ only by the terminal statement
    (`mkStmt`), the temp-name prefix, and whether the flagged-single-call
    env fallback applies (the builtin `revert(...)` statement keeps its
    historical env-less path).

    Returns `none` when the argument list has NO call-bearing shape this
    helper owns (the caller then runs its call-free catch-all exactly as
    before); `some verdict` is the final answer for an owned shape,
    including `some none` = lowering declined (the historical per-arm
    behavior). Temps for aggregate-typed pure companions are declared via
    `CoreTy.tempDeclStmt` (pointer-aliasing, see there). -/
def FunctionDecl.eventErrorCallArgsCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (tmpPrefix : String) (singleCallEnvFallback : Bool)
    (mkStmt : List CoreExpr -> CoreStmt) (fallbackStmt : Stmt)
    (args : List Arg) : Option (Option CoreStmt) :=
  match args with
  | [Arg.positional (Expr.call (Expr.ident name) callArgs)] =>
      some
        (match FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name callArgs
            (fun retExpr => mkStmt [retExpr]) with
        | some coreStmt => some coreStmt
        | none =>
            -- #201 (D): the single argument is a HASH/abi builtin call with
            -- a flagged argument (`emit EH(keccak256(abi.encodePacked(a +
            -- b)))` — `name` is then `keccak256`, never a user function),
            -- which the internal-call hoist above declines; lower it
            -- env-aware so the operand-width Panic 0x11 fires. Unflagged
            -- shapes keep the env-less fallback byte-identically.
            match (if singleCallEnvFallback &&
                  Args.anyAbiArgNeedsEnvCleanup
                    [Arg.positional (Expr.call (Expr.ident name) callArgs)] then
                (Args.toCoreExprsWithEnvCleanup? storageNames env
                    [Arg.positional
                      (Expr.call (Expr.ident name) callArgs)]).map
                  mkStmt
              else none) with
            | some coreStmt => some coreStmt
            | none => Stmt.toCore? storageNames fallbackStmt)
  | [ Arg.positional (Expr.call (Expr.ident firstName) firstArgs)
    , Arg.positional (Expr.call (Expr.ident secondName) secondArgs) ] =>
      some
        (match FunctionDecl.internalTwoSingleReturnCallsCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions firstName firstArgs
            secondName secondArgs (tmpPrefix ++ "_first")
            (fun firstExpr secondExpr => mkStmt [firstExpr, secondExpr]) with
        | some coreStmt => some coreStmt
        | none => do
            let secondCore ←
              Expr.toCore? storageNames
                (Expr.call (Expr.ident secondName) secondArgs)
            match FunctionDecl.internalSingleReturnCallCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions firstName firstArgs
                (fun retExpr => mkStmt [retExpr, secondCore]) with
            | some coreStmt => some coreStmt
            | none => Stmt.toCore? storageNames fallbackStmt)
  | [ Arg.positional (Expr.call (Expr.ident name) callArgs)
    , Arg.positional rhs ] =>
      some (do
        -- #201 (D/E): the pure argument lowers env-aware when flagged
        -- (narrow checked arithmetic / builtin-with-flagged-args), else
        -- byte-identical.
        let rhsCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env rhs
        match FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name callArgs
            (fun retExpr => mkStmt [retExpr, rhsCore]) with
        | some coreStmt => some coreStmt
        | none => Stmt.toCore? storageNames fallbackStmt)
  | [ Arg.positional lhs
    , Arg.positional (Expr.call (Expr.ident name) callArgs) ] =>
      some (do
        -- #201 (D/E): a flagged FIRST argument (`emit EMix(a + b, bump())` /
        -- `revert Err(a + b, bump())`, `uint8 a,b`) lowers env-aware INTO
        -- the pre-call temp, so its Panic 0x11 fires BEFORE the hoisted
        -- call runs (solc evaluates the arguments left-to-right);
        -- unflagged arguments keep `Expr.toCore?` byte-identically.
        let lhsCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env lhs
        let lhsTy ← Expr.abiTyWithEnv? env lhs
        let lhsCoreTy ← Ty.toCore? lhsTy
        let lhsTmp := tmpPrefix ++ "_lhs"
        match FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name callArgs
            (fun retExpr =>
              mkStmt [SolidCore.Solidity.Source.Expr.var lhsTmp, retExpr]) with
        | some coreStmt =>
            some
              (SolidCore.Solidity.Source.Stmt.block
                [ CoreTy.tempDeclStmt lhsCoreTy lhsTmp (some lhsCore)
                , coreStmt ])
        | none => Stmt.toCore? storageNames fallbackStmt)
  | [ Arg.positional first
    , Arg.positional second
    , Arg.positional (Expr.call (Expr.ident name) callArgs) ] =>
      some (do
        -- #201 (D/E): flagged pure arguments lower env-aware into their
        -- pre-call temps (Panic 0x11 before the hoisted call), unflagged
        -- byte-identical.
        let firstCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env first
        let secondCore ←
          Expr.abiArgCoreWithEnvCleanup? storageNames env second
        let firstTy ← Expr.abiTyWithEnv? env first
        let secondTy ← Expr.abiTyWithEnv? env second
        let firstCoreTy ← Ty.toCore? firstTy
        let secondCoreTy ← Ty.toCore? secondTy
        let firstTmp := tmpPrefix ++ "_first"
        let secondTmp := tmpPrefix ++ "_second"
        match FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name callArgs
            (fun retExpr =>
              mkStmt
                [ SolidCore.Solidity.Source.Expr.var firstTmp
                , SolidCore.Solidity.Source.Expr.var secondTmp
                , retExpr ]) with
        | some coreStmt =>
            some
              (SolidCore.Solidity.Source.Stmt.block
                [ CoreTy.tempDeclStmt firstCoreTy firstTmp (some firstCore)
                , CoreTy.tempDeclStmt secondCoreTy secondTmp (some secondCore)
                , coreStmt ])
        | none => Stmt.toCore? storageNames fallbackStmt)
  | _ => none
termination_by (3, internalFuel, 0, 7)

def FunctionDecl.internalAssignReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (targetNames : List Name) : Option CoreStmt := do
  let (returnBindings, _, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  if targetNames.length == returnBindings.length then
    let returnNames :=
      returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
    some
      (SolidCore.Solidity.Source.Stmt.block
        (prefixCore ++
          [ SolidCore.Solidity.Source.Stmt.captureReturn
              returnNames bodyCore ] ++
          CoreBindingDecls.assignToVars targetNames returnBindings))
  else
    none
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalTupleAssignReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (targets : List (Option CoreLValue))
    (lhsPrefix : List CoreStmt := []) : Option CoreStmt := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  if returnStorageRefs.any id then
    none
  else
    some ()
  if targets.length == returnBindings.length then
    let returnNames :=
      returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
    -- solc evaluates the tuple-assignment RHS (the multi-return call) BEFORE the
    -- LHS index expressions. `prefixCore ++ captureReturn` runs the RHS call and
    -- captures its returns; `lhsPrefix` (the hoisted LHS index-call temps, empty
    -- when the LHS has no call-valued index) then runs; finally the (pure temp
    -- read) targets are assigned. Store order among distinct targets is
    -- unobservable.
    some
      (SolidCore.Solidity.Source.Stmt.block
        (prefixCore ++
          [ SolidCore.Solidity.Source.Stmt.captureReturn
              returnNames bodyCore ] ++
          lhsPrefix ++
          CoreBindingDecls.assignToTargets targets returnBindings))
  else
    none
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalTupleVarDeclAssignReturnCallCorePieces?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (bindings : List VarBinding) : Option (List CoreStmt) := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  if returnStorageRefs.any id then
    none
  else
    some ()
  if bindings.length == returnBindings.length then
    some ()
  else
    none
  let decls ← VarBindings.toCoreTupleDecls? bindings
  let targets ← VarBindings.toCoreTupleTargets? bindings
  let returnNames :=
    returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
  some
    (decls ++ prefixCore ++
      [SolidCore.Solidity.Source.Stmt.captureReturn
        returnNames bodyCore] ++
      CoreBindingDecls.assignToTargets targets returnBindings)
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalReturnCallCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (returnTys : List Ty) : Option CoreStmt := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  if returnStorageRefs.any id then
    none
  else
    some ()
  if returnTys.length == returnBindings.length then
    let returnNames :=
      returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
    some
      (SolidCore.Solidity.Source.Stmt.block
        (prefixCore ++
          [ SolidCore.Solidity.Source.Stmt.captureReturn
              returnNames bodyCore
          , SolidCore.Solidity.Source.Stmt.returnValues
              (returnNames.map SolidCore.Solidity.Source.Expr.var) ]))
  else
    none
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalVarDeclAssignReturnCallCorePieces?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (name : Name) (args : List Arg)
    (bindings : List VarBinding) : Option (List CoreStmt) := do
  let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
    FunctionDecl.internalCallParts?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions name args
  if !(returnStorageRefs.any id) then
    none
  else
    some ()
  if bindings.length == returnBindings.length then
    some ()
  else
    none
  let decls ←
    VarBindings.toCoreDeclsExceptStorageReturns?
      bindings returnStorageRefs
  let assigns ←
    VarBindings.assignFromReturnBindingsWithStorageRefs?
      bindings returnBindings returnStorageRefs
  let returnNames :=
    returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
  some
    (decls ++ prefixCore ++
      [SolidCore.Solidity.Source.Stmt.captureReturn
        returnNames bodyCore] ++
      assigns)
termination_by (3, internalFuel, 0, 2)

def FunctionDecl.internalUnarySingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (op : UnaryOp) (expr : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt :=
  match Expr.internalSingleReturnCallConversion? expr with
  | some (name, args, convert) => do
      let coreOp ← UnaryOp.toCore? op
      FunctionDecl.internalSingleReturnCallCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions name args
        (fun retExpr =>
          useResult
            (SolidCore.Solidity.Source.Expr.unary coreOp
              (convert retExpr)))
  | none =>
      match expr with
  | expr@(Expr.call (Expr.member _ _) _) =>
      match op with
      | UnaryOp.logicalNot => do
          let coreOp ← UnaryOp.toCore? op
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv Ty.bool expr
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.unary coreOp retExpr))
      | _ => none
  | expr@(Expr.callWithOptions (Expr.member _ _) _ _) =>
      match op with
      | UnaryOp.logicalNot => do
          let coreOp ← UnaryOp.toCore? op
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv Ty.bool expr
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.unary coreOp retExpr))
      | _ => none
  | _ => none
termination_by (3, internalFuel, 0, 4)

def FunctionDecl.internalTypeConversionSingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (targetTy : Ty) (expr : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt :=
  match Expr.internalSingleReturnCallConversion? expr with
  | some (name, args, innerConvert) => do
      let convert ← Ty.internalCallConversionCore? targetTy
      match internalFuel with
      | fuel + 1 =>
          match
              Args.replaceInternalSingleReturnCallExprArg?
                "_sol_internal_call_arg" 0 args with
          | some (argIndex, argExpr, argTmp, replacedArgs) =>
              match
                  Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env argExpr with
              | some argTy => do
                  let argCoreTy ← Ty.toCore? argTy
                  let (priorPre, priorEnv, replacedArgs) ←
                    Args.snapshotPrefixBeforeLaterCall?
                      functions freeFunctions env storageNames
                      "_sol_internal_call_arg_prior" argIndex 0 replacedArgs
                  let envWithArgTmp := (argTmp, argTy) :: (priorEnv ++ env)
                  let argCore ←
                    FunctionDecl.internalSingleReturnCallExprCore?
                      fuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions argExpr
                      (fun retExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var argTmp)
                          retExpr)
                      (depth := 1)
                  let outerCore ←
                    FunctionDecl.internalSingleReturnCallCore?
                      fuel storageRefEnv envWithArgTmp externalCallKindEnv
                      storageNames modifiers functions freeFunctions name
                      replacedArgs
                      (fun retExpr =>
                        useResult (convert (innerConvert retExpr)))
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      (priorPre ++
                        [ SolidCore.Solidity.Source.Stmt.varDecl
                            argCoreTy argTmp none
                        , argCore
                        , outerCore ]))
              | none =>
                  FunctionDecl.internalSingleReturnCallCore?
                    (fuel + 1) storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions name args
                    (fun retExpr =>
                      useResult (convert (innerConvert retExpr)))
          | none =>
              FunctionDecl.internalSingleReturnCallCore?
                (fuel + 1) storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions name args
                (fun retExpr => useResult (convert (innerConvert retExpr)))
      | 0 =>
          FunctionDecl.internalSingleReturnCallCore?
            0 storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name args
            (fun retExpr => useResult (convert (innerConvert retExpr)))
  | none =>
      match expr with
      | expr@(Expr.call (Expr.member _ _) _)
      | expr@(Expr.callWithOptions (Expr.member _ _) _ _) =>
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv targetTy expr useResult
      | expr@(Expr.call (Expr.ident _) _)
      | expr@(Expr.callWithOptions (Expr.ident _) _ _) =>
          Expr.externalFunctionValueCallSingleReturnCore?
            storageNames env expr
            (fun resultExpr =>
              useResult (Ty.implicitCleanupCore targetTy resultExpr))
      | _ => none
termination_by (3, internalFuel, 0, 4)

def FunctionDecl.internalTernaryConditionSingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (cond thenExpr elseExpr : Expr)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt :=
  match cond with
  | Expr.call (Expr.ident name) args => do
      let thenCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env thenExpr
      let elseCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env elseExpr
      FunctionDecl.internalSingleReturnCallCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions name args
        (fun condExpr =>
          useResult
            (SolidCore.Solidity.Source.Expr.ternary
              condExpr thenCore elseCore))
  | Expr.call (Expr.member _ _) _
  | Expr.callWithOptions (Expr.member _ _) _ _ => do
      -- #131 SHORTCIRCUIT-CALL-POS: EXTERNAL single-return call in the ternary
      -- CONDITION (`t.f() ? a : b`). Mirror the internal-condition arm above but
      -- lower the condition through the external-call hoister (evaluate the call
      -- into a temp, then a core `ternary` on the temp). Branches must be pure
      -- (`Expr.toCore?` — no calls), so the untaken branch has no side effect and
      -- the core `ternary` reproduces the value.
      let thenCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env thenExpr
      let elseCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env elseExpr
      Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
        storageNames env externalCallKindEnv Ty.bool cond
        (fun condExpr =>
          useResult
            (SolidCore.Solidity.Source.Expr.ternary
              condExpr thenCore elseCore))
  | _ => none
termination_by (3, internalFuel, 0, 4)

def FunctionDecl.internalTernaryBranchSingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (cond thenExpr elseExpr : Expr)
    (useResult : CoreExpr -> CoreStmt) : Option CoreStmt := do
  let condCore ← Expr.toCoreAsWithEnv? storageNames env Ty.bool cond
  match Expr.internalSingleReturnCallConversion? thenExpr,
      Expr.internalSingleReturnCallConversion? elseExpr with
  | some (thenName, thenArgs, thenConvert),
    some (elseName, elseArgs, elseConvert) => do
      let thenCore ←
        FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions thenName thenArgs
          (fun retExpr => useResult (thenConvert retExpr))
      let elseCore ←
        FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions elseName elseArgs
          (fun retExpr => useResult (elseConvert retExpr))
      some
        (SolidCore.Solidity.Source.Stmt.ifElse
          condCore thenCore elseCore)
  | some (thenName, thenArgs, thenConvert), none => do
      let elseCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env elseExpr
      let thenCore ←
        FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions thenName thenArgs
          (fun retExpr => useResult (thenConvert retExpr))
      some
        (SolidCore.Solidity.Source.Stmt.ifElse
          condCore thenCore (useResult elseCore))
  | none, some (elseName, elseArgs, elseConvert) => do
      let thenCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env thenExpr
      let elseCore ←
        FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions elseName elseArgs
          (fun retExpr => useResult (elseConvert retExpr))
      some
        (SolidCore.Solidity.Source.Stmt.ifElse
          condCore (useResult thenCore) elseCore)
  | none, none => none
termination_by (3, internalFuel, 0, 4)

def FunctionDecl.internalExprSingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (expr : Expr) (useResult : CoreExpr -> CoreStmt) : Option CoreStmt :=
  match expr with
  | Expr.call (Expr.ident name) args =>
      FunctionDecl.internalSingleReturnCallExprCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions
        (Expr.call (Expr.ident name) args) useResult
  | Expr.unary op inner =>
      FunctionDecl.internalUnarySingleReturnUseCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions op inner useResult
  | Expr.call (Expr.typeName targetTy) [Arg.positional inner] =>
      match FunctionDecl.internalTypeConversionSingleReturnUseCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions targetTy inner useResult with
      | some coreStmt => some coreStmt
      | none =>
          match inner, internalFuel with
          | Expr.binary op lhs rhs, fuel + 1 => do
              let convert ← Ty.internalCallConversionCore? targetTy
              FunctionDecl.internalBinarySingleReturnUseCore?
                fuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions op lhs rhs
                (fun resultExpr => useResult (convert resultExpr))
          | _, _ => none
  | Expr.slice base (some startExpr) none => do
      let baseCore ← Expr.toCore? storageNames base
      FunctionDecl.internalExprSingleReturnUseCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions startExpr
        (fun startCore =>
          useResult
            (SolidCore.Solidity.Source.Expr.slice
              baseCore (some startCore) none))
  | Expr.slice base none (some stopExpr) => do
      let baseCore ← Expr.toCore? storageNames base
      FunctionDecl.internalExprSingleReturnUseCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions stopExpr
        (fun stopCore =>
          useResult
            (SolidCore.Solidity.Source.Expr.slice
              baseCore none (some stopCore)))
  | Expr.slice base (some startExpr) (some stopExpr) =>
      -- `[a:b]` with an internal-call bound (the single-bound arms above cover
      -- only `[a:]`/`[:b]`; this shape used to over-reject). Call-in-START:
      -- hoist the start call; the (call-free, `toCore?`-lowerable) stop still
      -- evaluates after it, matching solc's start-before-stop order.
      -- Call-in-STOP: only when start is a pure leaf (ident/literal), so
      -- hoisting the stop call past it cannot reorder an observable effect or
      -- panic. Anything else stays a fail-closed over-reject.
      (match
          (do
            let baseCore ← Expr.toCore? storageNames base
            let stopCore ← Expr.toCore? storageNames stopExpr
            FunctionDecl.internalExprSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions startExpr
              (fun startCore =>
                useResult
                  (SolidCore.Solidity.Source.Expr.slice
                    baseCore (some startCore) (some stopCore)))) with
      | some coreStmt => some coreStmt
      | none =>
          match startExpr with
          | Expr.ident _ | Expr.literal _ => do
              let baseCore ← Expr.toCore? storageNames base
              let startCore ← Expr.toCore? storageNames startExpr
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions stopExpr
                (fun stopCore =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.slice
                      baseCore (some startCore) (some stopCore)))
          | _ => none)
  | Expr.member base "length" =>
      match
          Expr.abiTyWithInternalFunctionsEnv?
            functions freeFunctions env base with
      | some ty =>
          match Ty.fixedBytesSize? ty with
          | some size =>
              some (useResult (SolidCore.Solidity.Source.Expr.word size))
          | none =>
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions base
                (fun baseCore =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.length baseCore))
      | none => none
  | Expr.ternary cond thenExpr elseExpr =>
      match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions cond thenExpr elseExpr
          useResult with
      | some coreStmt => some coreStmt
      | none =>
          FunctionDecl.internalTernaryBranchSingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions cond thenExpr elseExpr
            useResult
  | Expr.binary op lhs rhs =>
      FunctionDecl.internalBinarySingleReturnUseCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions op lhs rhs useResult
  | Expr.index (Expr.call (Expr.ident name) args) index => do
      -- A struct member on a returned memory value is resolved to an index
      -- whose BASE is the call. Capture the aggregate return first, then read
      -- the indexed field from that same memory reference.
      let indexCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env index
      FunctionDecl.internalSingleReturnCallExprCore?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions
        (Expr.call (Expr.ident name) args)
        (fun baseCore =>
          useResult (SolidCore.Solidity.Source.Expr.index baseCore indexCore))
  | Expr.index base (Expr.call (Expr.ident iname) iargs) =>
      -- OVERREJECT-CALLPOS-BATCH (B): an internal single-return call used as a
      -- mapping/array INDEX in a NON-return read position (`uint x = m[f()]`,
      -- `y = m[f()]`, `z = m[f()] + 1`, `t.h(m[f()])`). The pure index-read
      -- lowering (`Expr.toCore?`) has no internal-call fallback for the index
      -- operand, so this used to over-reject. The base is a pure storage/local
      -- reference (`indexReadCoreBuilder?`), so its evaluation has no side
      -- effect; hoist the index call into a temp and build the read from the
      -- temp — matching solc legacy `arr[f()]` order (base is a reference, then
      -- the index call runs; verified via `--ir`). Non-internal-call indices
      -- never reach here (the constructor pattern requires a direct call), and a
      -- base containing its own call makes `indexReadCoreBuilder?` return `none`,
      -- so the caller preserves the prior over-reject rather than emit unsound
      -- code.
      match Expr.indexReadCoreBuilderWithEnvCleanup? storageNames env base with
      | some buildRead =>
          FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions iname iargs
            (fun idxCore => useResult (buildRead idxCore))
      | none => none
  | Expr.call callee args =>
      -- Call through an internal function POINTER whose callee is NOT a bare
      -- identifier (e.g. an element of a function-pointer array: `arr[i](x)`).
      -- The named-callee call shapes are handled by the earlier arms; here the
      -- callee is any other expression. `ptrBoundaryCallExprParts?` declines
      -- (→ `none`) unless `callee` types as an internal function pointer, so
      -- non-pointer call shapes stay over-rejected exactly as before.
      match FunctionDecl.ptrBoundaryCallExprParts?
          storageRefEnv env storageNames callee "_ret_fp_" args with
      | some (returnBindings, _, prefixCore, bodyCore) =>
          match returnBindings with
          | [ret] =>
              some
                (SolidCore.Solidity.Source.Stmt.block
                  (prefixCore ++
                    [ SolidCore.Solidity.Source.Stmt.captureReturn
                        [ret.name] bodyCore
                    , useResult (SolidCore.Solidity.Source.Expr.var ret.name) ]))
          | _ => none
      | none =>
          -- The callee is itself an internal single-return call that RETURNS an
          -- internal function pointer, immediately called (`pick(true)(x)` — a
          -- returned pointer directly invoked). `ptrBoundaryCallExprParts?`
          -- declines because the pure read lowering (`Expr.toCore?`) cannot
          -- evaluate a call-valued callee; hoist the callee call into a temp
          -- fn-ptr (same single-return machinery as any nested call) and then
          -- dispatch through that temp with `ptrBoundaryCallCoreParts?`. The
          -- structural pre-check requires the callee to type as an internal
          -- function pointer with a well-formed single-return boundary shape, so
          -- non-pointer / multi-return callees stay over-rejected as before.
          match Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env callee with
          | some fnTy =>
              match FunctionDecl.ptrBoundaryCallCoreParts?
                  storageRefEnv env storageNames fnTy
                  (SolidCore.Solidity.Source.Expr.var "_ret_fp_ptr")
                  "_ret_fp_" args with
              | some (returnBindings, _, _, _) =>
                  match returnBindings with
                  | [ret] =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions callee
                        (fun ptrCore =>
                          match FunctionDecl.ptrBoundaryCallCoreParts?
                              storageRefEnv env storageNames fnTy ptrCore
                              "_ret_fp_" args with
                          | some (_, _, prefixCore, bodyCore) =>
                              SolidCore.Solidity.Source.Stmt.block
                                (prefixCore ++
                                  [ SolidCore.Solidity.Source.Stmt.captureReturn
                                      [ret.name] bodyCore
                                  , useResult
                                      (SolidCore.Solidity.Source.Expr.var
                                        ret.name) ])
                          | none => useResult ptrCore)
                  | _ => none
              | none => none
          | none => none
  | _ => none
termination_by (3, internalFuel, sizeOf expr, 10)

def FunctionDecl.internalBinarySingleReturnUseCore?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (op : BinaryOp) (lhs rhs : Expr) (useResult : CoreExpr -> CoreStmt) :
    Option CoreStmt :=
  let lhsCall? := Expr.internalSingleReturnCallConversion? lhs
  let rhsCall? := Expr.internalSingleReturnCallConversion? rhs
  match lhsCall?, rhsCall? with
  | some (firstName, firstArgs, firstConvert),
    some (secondName, secondArgs, secondConvert) => do
      let coreOp ← BinaryOp.toCore? op
      let lhsTmp := "_sol_bin_lhs"
      match op with
      | BinaryOp.boolAnd
      | BinaryOp.boolOr => do
          let callCore ←
            FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions secondName secondArgs
              (fun retExpr =>
                useResult
                  (SolidCore.Solidity.Source.Expr.binary coreOp
                    (SolidCore.Solidity.Source.Expr.var lhsTmp)
                    (secondConvert retExpr)))
          let skipCore :=
            match op with
            | BinaryOp.boolAnd =>
                useResult (SolidCore.Solidity.Source.Expr.word 0)
            | _ =>
                useResult (SolidCore.Solidity.Source.Expr.word 1)
          let branchCore :=
            match op with
            | BinaryOp.boolAnd =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  callCore skipCore
            | _ =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  skipCore callCore
          FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions firstName firstArgs
            (fun retExpr =>
              SolidCore.Solidity.Source.Stmt.block
                [ SolidCore.Solidity.Source.Stmt.varDecl
                    SolidCore.Solidity.Source.Ty.bool lhsTmp
                    (some (firstConvert retExpr))
                , branchCore ])
      | _ =>
          -- Ordinary operators: solc legacy evaluates the RIGHT operand's
          -- call FIRST, then the LEFT (ExpressionCompiler.cpp:614-615), so
          -- hoist the RHS call into a temp and run the LHS call second.
          match
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env rhs with
          | some rhsTy =>
              let rhsCoreTy ← Ty.toCore? rhsTy
              let rhsTmp := "_sol_bin_rhs"
              let lhsCallCore ←
                FunctionDecl.internalSingleReturnCallCore?
                  internalFuel storageRefEnv env externalCallKindEnv
                  storageNames modifiers functions freeFunctions
                  firstName firstArgs
                  (fun retExpr =>
                    useResult
                      (SolidCore.Solidity.Source.Expr.binary coreOp
                        (firstConvert retExpr)
                        (SolidCore.Solidity.Source.Expr.var rhsTmp)))
              FunctionDecl.internalSingleReturnCallCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions secondName secondArgs
                (fun retExpr =>
                  SolidCore.Solidity.Source.Stmt.block
                    [ SolidCore.Solidity.Source.Stmt.varDecl
                        rhsCoreTy rhsTmp (some (secondConvert retExpr))
                    , lhsCallCore ])
          | none =>
              match lhs, rhs with
              | Expr.call (Expr.ident rawFirstName) rawFirstArgs,
                Expr.call (Expr.ident rawSecondName) rawSecondArgs =>
                  match FunctionDecl.internalTwoSingleReturnCallsRightFirstCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions
                      rawFirstName rawFirstArgs rawSecondName rawSecondArgs
                      "_sol_bin_rhs"
                      (fun firstExpr secondExpr =>
                        useResult
                          (SolidCore.Solidity.Source.Expr.binary
                            coreOp firstExpr secondExpr)) with
                  | some coreStmt => some coreStmt
                  | none => do
                      let rhsCore ←
                        Expr.toCore? storageNames
                          (Expr.call (Expr.ident rawSecondName) rawSecondArgs)
                      FunctionDecl.internalSingleReturnCallCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions
                        rawFirstName rawFirstArgs
                        (fun retExpr =>
                          useResult
                            (SolidCore.Solidity.Source.Expr.binary
                              coreOp retExpr rhsCore))
              | _, _ => none
  | some (name, args, convert), none => do
      let coreOp ← BinaryOp.toCore? op
      match Expr.abiArgCoreWithEnvCleanup? storageNames env rhs with
      | some rhsCore =>
          -- LEFT operand is a call, RIGHT is core-lowerable. Ordinary
          -- operators: solc evaluates the RIGHT operand FIRST
          -- (ExpressionCompiler.cpp:614-615), so park the RHS value in a temp
          -- before running the LEFT call. Short-circuit ops keep the
          -- left-first guarded shape (the runtime boolAnd/boolOr arm guards
          -- the pure RHS).
          match op with
          | BinaryOp.boolAnd | BinaryOp.boolOr =>
              FunctionDecl.internalSingleReturnCallCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions name args
                (fun retExpr =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.binary
                      coreOp (convert retExpr) rhsCore))
          | _ =>
              match
                  Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env rhs with
              | some rhsTy => do
                  let rhsCoreTy ← Ty.toCore? rhsTy
                  let rhsTmp := "_sol_bin_rhs"
                  let callCore ←
                    FunctionDecl.internalSingleReturnCallCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions name args
                      (fun retExpr =>
                        useResult
                          (SolidCore.Solidity.Source.Expr.binary
                            coreOp (convert retExpr)
                            (SolidCore.Solidity.Source.Expr.var rhsTmp)))
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [ SolidCore.Solidity.Source.Stmt.varDecl
                          rhsCoreTy rhsTmp (some rhsCore)
                      , callCore ])
              | none =>
                  -- RHS type unresolvable: keep the previous (left-call-first)
                  -- shape rather than decline.
                  FunctionDecl.internalSingleReturnCallCore?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions name args
                    (fun retExpr =>
                      useResult
                        (SolidCore.Solidity.Source.Expr.binary
                          coreOp (convert retExpr) rhsCore))
      | none =>
          -- #131 SHORTCIRCUIT-CALL-POS (call-in-pure-operand): the LEFT operand is
          -- a direct internal single-return call and the RIGHT operand is NOT
          -- directly `toCore?`-able because it itself contains a call (e.g.
          -- `h() && (j()+1>0)`). Only sound for the short-circuiting `&&`/`||`:
          -- evaluate the left call into a bool temp, then hoist the right operand's
          -- inner call(s) INSIDE the guarded branch (via
          -- `internalExprSingleReturnUseCore?`), so the right call runs exactly
          -- when the left temp selects it. Any other operator → `none` (the right
          -- call would be evaluated eagerly, changing effects/order).
          match op with
          | BinaryOp.boolAnd
          | BinaryOp.boolOr => do
              let lhsTmp := "_sol_bin_lhs"
              let rhsCallCore ←
                FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions rhs
                  (fun rhsResult =>
                    useResult
                      (SolidCore.Solidity.Source.Expr.binary coreOp
                        (SolidCore.Solidity.Source.Expr.var lhsTmp) rhsResult))
              let skipCore :=
                match op with
                | BinaryOp.boolAnd =>
                    useResult (SolidCore.Solidity.Source.Expr.word 0)
                | _ =>
                    useResult (SolidCore.Solidity.Source.Expr.word 1)
              let branchCore :=
                match op with
                | BinaryOp.boolAnd =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      (SolidCore.Solidity.Source.Expr.var lhsTmp)
                      rhsCallCore skipCore
                | _ =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      (SolidCore.Solidity.Source.Expr.var lhsTmp)
                      skipCore rhsCallCore
              FunctionDecl.internalSingleReturnCallCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions name args
                (fun retExpr =>
                  SolidCore.Solidity.Source.Stmt.block
                    [ SolidCore.Solidity.Source.Stmt.varDecl
                        SolidCore.Solidity.Source.Ty.bool lhsTmp
                        (some (convert retExpr))
                    , branchCore ])
          | _ =>
              -- R1 residue fix (direct-call LHS + nested-call RHS): the LEFT
              -- operand is a direct internal single-return call and the RIGHT
              -- operand carries its own nested call (so it is NOT directly
              -- `toCore?`-able — e.g. `f() + g() * 10`). Ordinary operators:
              -- solc evaluates the RIGHT operand FIRST
              -- (ExpressionCompiler.cpp:614-615). Lower the RHS expression into
              -- a temp, then run the LEFT call and form the residual binary
              -- reading the temp. Falls back to `none` (the prior over-reject)
              -- when the RHS type does not resolve or the emission fails to
              -- lower. Short-circuit ops keep the guarded left-first shape
              -- above.
              -- NESTING-UNIQUE temp (see the mirror residue arm in the
              -- `none, some` branch): suffix by the LHS's rendered size, since
              -- the only emissions spanning this decl and its read come from
              -- the LEFT call's argument hoists (strict subterms of `lhs`).
              (do
                let rhsTy ←
                  Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env rhs
                let rhsCoreTy ← Ty.toCore? rhsTy
                let rhsTmp :=
                  "_sol_bin_rhs_" ++ toString ((toString (repr lhs)).length)
                let lhsCallCore ←
                  FunctionDecl.internalSingleReturnCallCore?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions name args
                    (fun retExpr =>
                      useResult
                        (SolidCore.Solidity.Source.Expr.binary coreOp
                          (convert retExpr)
                          (SolidCore.Solidity.Source.Expr.var rhsTmp)))
                FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions rhs
                  (fun rhsResult =>
                    SolidCore.Solidity.Source.Stmt.block
                      [ SolidCore.Solidity.Source.Stmt.varDecl
                          rhsCoreTy rhsTmp (some rhsResult)
                      , lhsCallCore ]))
  | none, some _ => do
      let coreOp ← BinaryOp.toCore? op
      let lhsTy ←
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env lhs
      let lhsCoreTy ← Ty.toCore? lhsTy
      let lhsTmp := "_sol_bin_lhs"
      let rhsCallCore ←
        FunctionDecl.internalSingleReturnCallExprCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions rhs
          (fun retExpr =>
            useResult
              (SolidCore.Solidity.Source.Expr.binary coreOp
                (SolidCore.Solidity.Source.Expr.var lhsTmp)
                retExpr))
      let lhsThen (lhsCore : CoreExpr) : CoreStmt :=
        match op with
        | BinaryOp.boolAnd
        | BinaryOp.boolOr =>
            let skipCore :=
              match op with
              | BinaryOp.boolAnd =>
                  useResult (SolidCore.Solidity.Source.Expr.word 0)
              | _ =>
                  useResult (SolidCore.Solidity.Source.Expr.word 1)
            let branchCore :=
              match op with
              | BinaryOp.boolAnd =>
                  SolidCore.Solidity.Source.Stmt.ifElse
                    (SolidCore.Solidity.Source.Expr.var lhsTmp)
                    rhsCallCore skipCore
              | _ =>
                  SolidCore.Solidity.Source.Stmt.ifElse
                    (SolidCore.Solidity.Source.Expr.var lhsTmp)
                    skipCore rhsCallCore
            SolidCore.Solidity.Source.Stmt.block
              [ SolidCore.Solidity.Source.Stmt.varDecl
                  lhsCoreTy lhsTmp (some lhsCore)
              , branchCore ]
        | _ =>
            SolidCore.Solidity.Source.Stmt.block
              [ SolidCore.Solidity.Source.Stmt.varDecl
                  lhsCoreTy lhsTmp (some lhsCore)
              , rhsCallCore ]
      match op, Expr.abiArgCoreWithEnvCleanup? storageNames env lhs with
      | BinaryOp.boolAnd, some lhsCore => some (lhsThen lhsCore)
      | BinaryOp.boolOr, some lhsCore => some (lhsThen lhsCore)
      | _, some lhsCore =>
          -- Ordinary operators with a core-lowerable LEFT operand: solc
          -- evaluates the RIGHT operand's call FIRST
          -- (ExpressionCompiler.cpp:614-615). Leave the pure LEFT operand in
          -- the residual binary, whose runtime arm is right-then-left.
          FunctionDecl.internalSingleReturnCallExprCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions rhs
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.binary coreOp
                  lhsCore retExpr))
      | BinaryOp.boolAnd, none =>
          FunctionDecl.internalExprSingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions lhs lhsThen
      | BinaryOp.boolOr, none =>
          FunctionDecl.internalExprSingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions lhs lhsThen
      | _, none =>
          -- R1 residue fix: NON-core LEFT operand (contains its own calls)
          -- beside a RIGHT direct call, ordinary operator. solc evaluates the
          -- RIGHT operand FIRST (ExpressionCompiler.cpp:614-615), so park the
          -- RHS call's value in a temp, then hoist the LHS calls. Falls back
          -- to the previous left-first shape when the RHS type does not
          -- resolve or the right-first emission fails to lower.
          let rightFirst? : Option CoreStmt := do
            let rhsTy ←
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env rhs
            let rhsCoreTy ← Ty.toCore? rhsTy
            -- NESTING-UNIQUE temp: suffix by the LHS's rendered size. Any
            -- emission nested
            -- between this decl and its read comes from a strict SUBTERM of
            -- `lhs`, whose rendering (hence suffix) is strictly smaller;
            -- legacy `_sol_bin_*` names are never suffixed, so no shadow can
            -- capture the read. (`sizeOf` is noncomputable for `Expr`; the
            -- derived `repr` length is the computable strictly-monotone
            -- stand-in.)
            let rhsTmp := "_sol_bin_rhs_" ++ toString ((toString (repr lhs)).length)
            let lhsCallCore ←
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions lhs
                (fun lhsResult =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.binary coreOp
                      lhsResult
                      (SolidCore.Solidity.Source.Expr.var rhsTmp)))
            FunctionDecl.internalSingleReturnCallExprCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions rhs
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.block
                  [ SolidCore.Solidity.Source.Stmt.varDecl
                      rhsCoreTy rhsTmp (some retExpr)
                  , lhsCallCore ])
          match rightFirst? with
          | some coreStmt => some coreStmt
          | none =>
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions lhs lhsThen
  | none, none =>
    -- CLUSTER-B #7 (extcall-binary): before the generic nested-internal-call
    -- path, try hoisting a single EXTERNAL/member call out of one operand (the
    -- other operand pure). Declines (→ `none`) for every non-external shape, so
    -- the existing internal-call handling below is reached unchanged and no
    -- previously-accepted program regresses.
    match
        externalBinarySingleReturnUseCore?
          env externalCallKindEnv storageNames functions freeFunctions
          op lhs rhs useResult with
    | some coreStmt => some coreStmt
    | none => do
      let coreOp ← BinaryOp.toCore? op
      let lhsTy ←
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env lhs
      let lhsCoreTy ← Ty.toCore? lhsTy
      let lhsTmp := "_sol_bin_" ++ BinaryOp.tempTag op ++ "_lhs"
      match
          FunctionDecl.internalExprSingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions rhs
            (fun retExpr =>
              useResult
                (SolidCore.Solidity.Source.Expr.binary coreOp
                  (SolidCore.Solidity.Source.Expr.var lhsTmp)
                  retExpr)) with
      | some rhsCallCore =>
          let lhsThen (lhsCore : CoreExpr) : CoreStmt :=
            match op with
            | BinaryOp.boolAnd
            | BinaryOp.boolOr =>
            let skipCore :=
              match op with
              | BinaryOp.boolAnd =>
                  useResult (SolidCore.Solidity.Source.Expr.word 0)
              | _ =>
                  useResult (SolidCore.Solidity.Source.Expr.word 1)
              let branchCore :=
                match op with
                | BinaryOp.boolAnd =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      (SolidCore.Solidity.Source.Expr.var lhsTmp)
                      rhsCallCore skipCore
                | _ =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      (SolidCore.Solidity.Source.Expr.var lhsTmp)
                      skipCore rhsCallCore
              SolidCore.Solidity.Source.Stmt.block
                [ SolidCore.Solidity.Source.Stmt.varDecl
                    lhsCoreTy lhsTmp (some lhsCore)
                , branchCore ]
            | _ =>
                SolidCore.Solidity.Source.Stmt.block
                  [ SolidCore.Solidity.Source.Stmt.varDecl
                      lhsCoreTy lhsTmp (some lhsCore)
                  , rhsCallCore ]
          match op, Expr.toCore? storageNames lhs with
          | BinaryOp.boolAnd, some lhsCore => some (lhsThen lhsCore)
          | BinaryOp.boolOr, some lhsCore => some (lhsThen lhsCore)
          | _, some lhsCore =>
              -- Ordinary operators with a core-lowerable LEFT operand: solc
              -- evaluates the RIGHT operand's nested call(s) FIRST
              -- (ExpressionCompiler.cpp:614-615); the pure LEFT operand stays
              -- in the residual binary (runtime arm is right-then-left).
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions rhs
                (fun retExpr =>
                  useResult
                    (SolidCore.Solidity.Source.Expr.binary coreOp
                      lhsCore retExpr))
          | BinaryOp.boolAnd, none =>
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions lhs lhsThen
          | BinaryOp.boolOr, none =>
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions lhs lhsThen
          | _, none =>
              -- R1 residue fix (both-sides-hoisted generic path): NON-core
              -- LEFT operand with its own calls beside a call-bearing RHS,
              -- ordinary operator. solc evaluates the RIGHT operand's call(s)
              -- FIRST (ExpressionCompiler.cpp:614-615), so hoist the RHS into
              -- a temp, then hoist the LHS calls. Falls back to the previous
              -- left-first shape when the RHS type does not resolve or the
              -- right-first emission fails to lower.
              -- NESTING-UNIQUE temp (see the direct-RHS-call residue arm).
              let rhsTmp :=
                "_sol_bin_" ++ BinaryOp.tempTag op ++ "_rhs_" ++
                  toString ((toString (repr lhs)).length)
              let rightFirst? : Option CoreStmt := do
                let rhsTy ←
                  Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env rhs
                let rhsCoreTy ← Ty.toCore? rhsTy
                let lhsCallCore ←
                  FunctionDecl.internalExprSingleReturnUseCore?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions lhs
                    (fun lhsResult =>
                      useResult
                        (SolidCore.Solidity.Source.Expr.binary coreOp
                          lhsResult
                          (SolidCore.Solidity.Source.Expr.var rhsTmp)))
                FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv
                  storageNames modifiers functions freeFunctions rhs
                  (fun rhsResult =>
                    SolidCore.Solidity.Source.Stmt.block
                      [ SolidCore.Solidity.Source.Stmt.varDecl
                          rhsCoreTy rhsTmp (some rhsResult)
                      , lhsCallCore ])
              match rightFirst? with
              | some coreStmt => some coreStmt
              | none =>
                  FunctionDecl.internalExprSingleReturnUseCore?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions lhs lhsThen
      | none =>
          match Expr.toCore? storageNames lhs with
          | some _ => none
          | none => do
              let rhsCore ← Expr.toCore? storageNames rhs
              let previousShape? : Option CoreStmt :=
                FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv
                  storageNames modifiers functions freeFunctions lhs
                  (fun lhsCore =>
                    useResult
                      (SolidCore.Solidity.Source.Expr.binary
                        coreOp lhsCore rhsCore))
              match op with
              | BinaryOp.boolAnd => previousShape?
              | BinaryOp.boolOr => previousShape?
              | _ =>
                  -- R1 residue fix (lhs-hoisted + pure-rhs fallback): the LEFT
                  -- operand's calls used to run before the pure RHS was read;
                  -- solc evaluates the RIGHT operand FIRST
                  -- (ExpressionCompiler.cpp:614-615), so park the pure RHS
                  -- value in a temp before hoisting the LHS calls. Falls back
                  -- to the previous left-first shape when the RHS type does
                  -- not resolve. Short-circuit ops keep the guarded left-first
                  -- shape above.
                  let rightFirst? : Option CoreStmt := do
                    let rhsTy ←
                      Expr.abiTyWithInternalFunctionsEnv?
                        functions freeFunctions env rhs
                    let rhsCoreTy ← Ty.toCore? rhsTy
                    -- NESTING-UNIQUE temp (see the direct-RHS-call residue
                    -- arm).
                    let rhsTmp :=
                      "_sol_bin_" ++ BinaryOp.tempTag op ++ "_rhs_" ++
                        toString ((toString (repr lhs)).length)
                    let lhsCallCore ←
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions lhs
                        (fun lhsCore =>
                          useResult
                            (SolidCore.Solidity.Source.Expr.binary coreOp
                              lhsCore
                              (SolidCore.Solidity.Source.Expr.var rhsTmp)))
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        [ SolidCore.Solidity.Source.Stmt.varDecl
                            rhsCoreTy rhsTmp (some rhsCore)
                        , lhsCallCore ])
                  match rightFirst? with
                  | some coreStmt => some coreStmt
                  | none => previousShape?
termination_by (3, internalFuel, sizeOf (Expr.binary op lhs rhs), 8)

def FunctionDecl.conditionUseCoreWithInternalCalls?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (cond : Expr) (useCond : CoreExpr -> CoreStmt) :
    Option CoreStmt :=
  match cond with
  | Expr.call (Expr.typeName targetTy) [Arg.positional inner] =>
      match
          FunctionDecl.internalTypeConversionSingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions targetTy inner useCond with
      | some coreStmt => some coreStmt
      | none => do
          let condCore ← Expr.toCore? storageNames cond
          some (useCond condCore)
  | Expr.binary op lhs rhs =>
      match
          FunctionDecl.internalBinarySingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions op lhs rhs useCond with
      | some coreStmt => some coreStmt
      | none => do
          match Expr.binaryToCoreWithEnv? storageNames env op lhs rhs with
          | some condCore => some (useCond condCore)
          | none => do
              let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
              some (useCond condCore)
  | Expr.call (Expr.ident name) args =>
      match
          FunctionDecl.internalSingleReturnCallCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions name args useCond with
      | some coreStmt => some coreStmt
      | none => do
          let condCore ← Expr.toCore? storageNames cond
          some (useCond condCore)
  | Expr.call (Expr.member _ _) _ =>
      match
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv Ty.bool cond useCond with
      | some coreStmt => some coreStmt
      | none => do
          let condCore ← Expr.toCore? storageNames cond
          some (useCond condCore)
  | Expr.callWithOptions (Expr.member _ _) _ _ =>
      match
          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
            storageNames env externalCallKindEnv Ty.bool cond useCond with
      | some coreStmt => some coreStmt
      | none => do
          let condCore ← Expr.toCore? storageNames cond
          some (useCond condCore)
  | Expr.unary op inner =>
      match
          FunctionDecl.internalUnarySingleReturnUseCore?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions op inner useCond with
      | some coreStmt => some coreStmt
      | none => do
          -- R2 (Stage C): `!cond` recurses env-aware at `Ty.bool` (a nested
          -- comparison keeps its operand-width cleanup), falling back to the
          -- env-less lowering.
          let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
          some (useCond condCore)
  | _ => do
      let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
      some (useCond condCore)
termination_by (3, internalFuel, sizeOf cond, 12)

/-- CALLPOS-FAMILY: hoist EVERY direct internal-call argument — including
    MULTIPLE call arguments in one call (`f(g(), h())`) and NESTED call
    arguments (`f(g(h()))`, `f(f(g()))`) — into ordered prefix temps, so the
    residual call carries only pure/temp-read arguments. Generalises the older
    single-`Args.replaceDirectInternalCallArg?` hoist, which peeled only the
    FIRST direct-call argument and left the two-call-arg / nested-inner-call
    shapes over-rejecting. solc legacy evaluates function-call arguments
    left-to-right, and a nested call before the call that consumes it (verified
    via `--ir`); the emitted prefix reproduces that order (a call's own
    argument hoists precede the temp that consumes them; earlier arguments
    precede later ones). Returns the prefix decl/assign statements, the
    (temp, ty) env extension, and the residual argument list; `none` if any
    hoisted call fails to lower (preserving the prior over-reject) — the FUEL
    argument is the structural recursion bound (peeled one per arg/nesting
    level). -/
def FunctionDecl.hoistDirectInternalCallArgsAux?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (fallbackPrefix : String) :
    Nat -> Nat -> List Arg ->
      Option (Nat × List CoreStmt × List (Name × Ty) × List Arg)
  | 0, _, _ => none
  | _, counter, [] => some (counter, [], [], [])
  | Nat.succ fuel, counter, arg :: rest =>
      match Arg.directInternalCall? arg with
      | some (callName, callArgs) => do
          -- Hoist this call's OWN (possibly call-bearing) arguments first, so
          -- the inner temps are evaluated before the temp that consumes them.
          let (c1, innerPre, innerEnv, innerReplacedArgs) ←
            FunctionDecl.hoistDirectInternalCallArgsAux?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions fallbackPrefix
              fuel counter callArgs
          let tempName := internalCallArgTempName fallbackPrefix c1
          let argRetTy ←
            FunctionDecl.directOrPtrCallArgReturnTy?
              functions freeFunctions env callName callArgs
          let argCoreTy ← Ty.toCore? argRetTy
          let assignCore ←
            FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv (innerEnv ++ env) externalCallKindEnv
              storageNames modifiers functions freeFunctions
              callName innerReplacedArgs
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var tempName) retExpr)
          let thisPre :=
            innerPre ++
              [ SolidCore.Solidity.Source.Stmt.varDecl argCoreTy tempName none
              , assignCore ]
          let (c3, restPre, restEnv, restReplaced) ←
            FunctionDecl.hoistDirectInternalCallArgsAux?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions fallbackPrefix
              fuel (c1 + 1) rest
          some
            ( c3
            , thisPre ++ restPre
            , (tempName, argRetTy) :: (innerEnv ++ restEnv)
            , Arg.withExpr (Expr.ident tempName) arg :: restReplaced )
      | none =>
          -- #173 TERNARY-CALL-IN-ARG: a ternary argument whose condition or a
          -- branch holds a non-pure call. The residual pure-argument lowering
          -- cannot lower such a ternary, so route it through the SAME guarded-
          -- branch ternary-call hoister used for binary operands / conditions /
          -- returns (`internalExprSingleReturnUseCore?`): it binds the ternary
          -- result to a temp, hoisting each branch's inner call into the
          -- corresponding guarded arm (the untaken branch's call is never run).
          -- The temp read replaces the argument in place, preserving solc's
          -- left-to-right argument evaluation order. A ternary with pure
          -- branches makes the hoister decline (`none`), falling through to the
          -- unchanged pure-argument path.
          let ternaryHoist? : Option (Nat × List CoreStmt × List (Name × Ty) × List Arg) := do
            let (tcond, tthen, telse) ← Arg.ternaryParts? arg
            let ternaryExpr := Expr.ternary tcond tthen telse
            let argRetTy ←
              Expr.abiTyWithInternalFunctionsEnv?
                functions freeFunctions env ternaryExpr
            let argCoreTy ← Ty.toCore? argRetTy
            let tempName := internalCallArgTempName fallbackPrefix counter
            let assignCore ←
              FunctionDecl.internalExprSingleReturnUseCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions ternaryExpr
                (fun retExpr =>
                  SolidCore.Solidity.Source.Stmt.assign
                    (SolidCore.Solidity.Source.LValue.var tempName) retExpr)
            let (c3, restPre, restEnv, restReplaced) ←
              FunctionDecl.hoistDirectInternalCallArgsAux?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions fallbackPrefix
                fuel (counter + 1) rest
            let thisPre :=
              [ SolidCore.Solidity.Source.Stmt.varDecl argCoreTy tempName none
              , assignCore ]
            some
              ( c3
              , thisPre ++ restPre
              , (tempName, argRetTy) :: restEnv
              , Arg.withExpr (Expr.ident tempName) arg :: restReplaced )
          match ternaryHoist? with
          | some result => some result
          | none => do
              let (c3, restPre, restEnv, restReplaced) ←
                FunctionDecl.hoistDirectInternalCallArgsAux?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions fallbackPrefix
                  fuel counter rest
              if restPre.isEmpty then
                some (c3, restPre, restEnv, arg :: restReplaced)
              else do
                -- A later call can mutate state observed by this earlier,
                -- otherwise-pure argument. Snapshot the argument before the
                -- later call prefix so `combine(trace, mutate())` passes the
                -- pre-mutation value of `trace`, matching Solidity's
                -- left-to-right argument evaluation.
                let argExpr :=
                  match arg with
                  | Arg.positional expr => expr
                  | Arg.named _ expr => expr
                let argTy ←
                  Expr.abiTyWithInternalFunctionsEnv?
                    functions freeFunctions env argExpr
                let argCoreTy ← Ty.toCore? argTy
                let argCore ←
                  match
                      Expr.toCoreAsWithEnv?
                        storageNames env argTy argExpr with
                  | some core => some core
                  | none => Expr.toCore? storageNames argExpr
                let tempName :=
                  internalCallArgTempName fallbackPrefix counter
                let thisPre :=
                  [CoreTy.tempDeclStmt argCoreTy tempName (some argCore)]
                some
                  ( c3
                  , thisPre ++ restPre
                  , (tempName, argTy) :: restEnv
                  , Arg.withExpr (Expr.ident tempName) arg :: restReplaced )

/-- Wrapper over `hoistDirectInternalCallArgsAux?`: run the hoist over an
    argument list and surface the prefix pieces / temp env / residual args only
    when at least one direct-call argument was actually hoisted (otherwise
    `none`, so the caller keeps its existing pure-argument lowering path). -/
def FunctionDecl.hoistDirectInternalCallArgs?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (fallbackPrefix : String)
    (args : List Arg) :
    Option (List CoreStmt × List (Name × Ty) × List Arg) := do
  let (_, prefixPieces, tempEnv, replacedArgs) ←
    FunctionDecl.hoistDirectInternalCallArgsAux?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions fallbackPrefix 64 0 args
  if prefixPieces.isEmpty then none
  else some (prefixPieces, tempEnv, replacedArgs)

/-- `addmod` and `mulmod` are the two legacy-codegen builtins whose argument
    effects run right-to-left. Hoist their nested calls in that order, then put
    the rewritten arguments back into their original positional slots. -/
def FunctionDecl.hoistDirectInternalCallArgsForCallee?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (fallbackPrefix : String)
    (calleeName : Name) (args : List Arg) :
    Option (List CoreStmt × List (Name × Ty) × List Arg) := do
  let reverseOrder := calleeName == "addmod" || calleeName == "mulmod"
  let orderedArgs := if reverseOrder then args.reverse else args
  let (prefixPieces, tempEnv, replacedOrdered) ←
    FunctionDecl.hoistDirectInternalCallArgs?
      internalFuel storageRefEnv env externalCallKindEnv storageNames
      modifiers functions freeFunctions fallbackPrefix orderedArgs
  let replacedArgs :=
    if reverseOrder then replacedOrdered.reverse else replacedOrdered
  some (prefixPieces, tempEnv, replacedArgs)

/-- NARROW-STRUCT-CTOR (#184): lower a value against `targetTy` with the
    env-aware `toCoreAsWithEnv?`, EXCEPT a struct-literal-tuple RHS (the shape
    `Expr.resolveStructsFuel` produces for `S(a+c, 0)` — an `Expr.tuple` of
    per-field explicit casts). `toCoreAsWithEnv?` has no `Expr.tuple` arm, so it
    falls to the env-less direct path, which treats each `uint8(a+c)` field as a
    plain TRUNCATING cast and silently wraps a narrow checked-arithmetic field
    to 256 bits (→ 44 instead of Panic 0x11). Lower each field env-aware against
    its own field type instead — exactly as the (already-correct) struct-return
    path does via `TupleItems.toCoreExprsAsWithEnv?` — so `uint8(a+c)` reaches
    the H2 narrow-cast arm (checked operand-width cleanup → Panic 0x11), while a
    genuine `uint8(w)` field still truncates. A struct value is represented as an
    `Expr.tuple` of field cores (see the env-less `Expr.tuple` arm of
    `Expr.toCore?`), so the output shape is unchanged. -/
def Expr.structCtorTupleCoreAsWithEnv? (storageNames : List Name)
    (env : TypeEnv) (targetTy : Ty) (rhs : Expr) : Option CoreExpr :=
  match targetTy, rhs with
  | Ty.struct _ fieldTys, Expr.tuple items =>
      if fieldTys.length == items.length then
        match TupleItems.toCoreExprsAsWithEnv? storageNames env fieldTys items with
        | some coreExprs =>
            some (SolidCore.Solidity.Source.Expr.tuple coreExprs)
        | none => Expr.toCoreAsWithEnv? storageNames env targetTy rhs
      else
        Expr.toCoreAsWithEnv? storageNames env targetTy rhs
  | _, _ => Expr.toCoreAsWithEnv? storageNames env targetTy rhs

/-- STAGE-D #194: env-aware LVALUE lowering — identical to `Expr.toCoreLValue?`
    except a NARROW (`uintN`/`intN`, N < 256) index KEY that carries checked
    arithmetic (`arr[a + b] = v`, `mp[a + b] = v`, `arr2[1][a + b] = v`,
    `bs[a + b] = …`, `uint8 a=200,b=100`) is lowered at ITS OWN type through the
    env-aware recursion, so the operand-width cleanup Panics 0x11 on overflow
    BEFORE the slot is computed — mirroring exactly what R2 did for the READ side
    (`Expr.index` arm of `Expr.toCoreAsWithEnvFuel?` via `indexReadCoreBuilder?`).
    The env-less write path ran the key bare at 256 bits, writing at index 300
    (wrong state + missing Panic). Keys that need no cleanup (plain idents,
    literals) and wide keys (`narrowIntCastTarget?` `none` ⇒ inner `do` fails)
    keep the byte-identical env-less lowering. -/
def Expr.toCoreLValueWithEnv? (storageNames : List Name) (env : TypeEnv) :
    Expr -> Option CoreLValue
  | Expr.index base key =>
      -- Re-lower every index KEY env-aware, including keys nested in the base.
      -- The original implementation handled the outermost key only, so
      -- `m[a+b][0] = v` still lowered the `a+b` key env-less inside the base.
      -- Recursing into the base preserves the same lvalue shape while applying
      -- the checked-width rule at every path component.
      let keyCore? : Option CoreExpr :=
        -- An explicit narrow conversion is TRUNCATING, not a checked implicit
        -- conversion.  Lower its operand at the operand's own width first (so
        -- checked arithmetic inside still panics), then apply the explicit cast
        -- before the mapping key is hashed.
        match (match key with
          | Expr.call (Expr.typeName castTy) [Arg.positional inner] => do
              let (isSigned, bits) ← Ty.narrowIntCastTarget? castTy
              let innerTy ← Expr.abiTyWithEnv? env inner
              let innerCore ←
                match Expr.toCoreAsWithEnv? storageNames env innerTy inner with
                | some core => some core
                | none => Expr.toCore? storageNames inner
              if isSigned then
                some (SolidCore.Solidity.Source.Expr.intCast bits innerCore)
              else
                some (SolidCore.Solidity.Source.Expr.uintCast bits innerCore)
          | _ => none) with
        | some c => some c
        | none =>
        match (do
            let keyTy ← Expr.abiTyWithEnv? env key
            let _ ← Ty.narrowIntCastTarget? keyTy
            Expr.toCoreAsWithEnv? storageNames env keyTy key) with
          | some c => some c
          | none => Expr.toCore? storageNames key
      (do
        let keyCore ← keyCore?
        match base with
        | Expr.ident name =>
            match stateNameRuntimeKey? name storageNames with
            | some skey =>
                -- R3 (#192): env-aware write index key — materialize a
                -- bare-storage `string`/`bytes`/array key (value-use boundary),
                -- so `m[stateStr] = v` hits the contents-derived slot. Narrow
                -- checked keys and scalars are unaffected (materialize is a
                -- no-op for any non-`Expr.storage` core).
                some (SolidCore.Solidity.Source.LValue.storageIndex skey
                  keyCore)
            | none => do
                let baseCore ←
                  Expr.toCoreLValue? storageNames (Expr.ident name)
                some (SolidCore.Solidity.Source.LValue.index baseCore keyCore)
        | _ => do
            let baseCore ← Expr.toCoreLValueWithEnv? storageNames env base
            some (SolidCore.Solidity.Source.LValue.index baseCore keyCore))
  | other => Expr.toCoreLValue? storageNames other

/-- Use the env-aware lvalue path only when some part of the target needs
    source-type cleanup.  This keeps ordinary lvalues on the established
    lowering while making every specialized assignment arm honor narrow
    checked arithmetic in nested index keys. -/
def Expr.toCoreLValueWithEnvCleanup? (storageNames : List Name) (env : TypeEnv)
    (expr : Expr) : Option CoreLValue :=
  if Expr.abiArgNeedsEnvCleanup? expr then
    Expr.toCoreLValueWithEnv? storageNames env expr
  else
    Expr.toCoreLValue? storageNames expr

/-- A compound shift assignment whose count needs operand-width cleanup.
    Shift counts keep their own Solidity type, so `x <<= a + b` with `uint8`
    operands must evaluate `a + b` at `uint8` and Panic 0x11 on overflow before
    modifying `x`. The generic compound-assignment lowerer uses env-less
    `toCore?` for the RHS and therefore loses that check. -/
def Expr.toCoreAssignOpShiftRhsAware? (storageNames : List Name)
    (env : TypeEnv) : Expr -> Option CoreExpr
  | Expr.assign lhs op rhs => do
      let coreOp ←
        match op with
        | AssignOp.shlAssign =>
            some SolidCore.Solidity.Source.BinaryOp.shl
        | AssignOp.shrAssign =>
            some SolidCore.Solidity.Source.BinaryOp.shr
        | AssignOp.sarAssign =>
            some SolidCore.Solidity.Source.BinaryOp.sar
        | _ => none
      if !Expr.abiArgNeedsEnvCleanup? rhs then none else do
        let lhsCore ←
          match lhs with
          | Expr.index _ key =>
              if Expr.abiArgNeedsEnvCleanup? key then
                Expr.toCoreLValueWithEnv? storageNames env lhs
              else
                Expr.toCoreLValue? storageNames lhs
          | _ => Expr.toCoreLValue? storageNames lhs
        let rhsTy ← Expr.abiTyWithEnv? env rhs
        let rhsCore ← Expr.toCoreAsWithEnv? storageNames env rhsTy rhs
        let lhsTy ← Expr.abiTyWithEnv? env lhs
        let cleanup ← Ty.toCoreValueCleanup? lhsTy
        some
          (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
            lhsCore.toExpr coreOp rhsCore cleanup)
  | _ => none

def assignmentCoreWithEnv? (storageNames : List Name)
    (env : TypeEnv) (lhs rhs : Expr) : Option CoreStmt := do
  let lhsCore ← Expr.toCoreLValueWithEnv? storageNames env lhs
  let targetTy ← Expr.abiTyWithEnv? env lhs
  let rhsCore ← Expr.structCtorTupleCoreAsWithEnv? storageNames env targetTy rhs
  some
    (SolidCore.Solidity.Source.Stmt.assign lhsCore rhsCore)

/-- FB1 (tuple-RHS target typing) — shared component lowering. Given each
    component's declared target type (`tys`; `none` = anonymous binding / hole
    LHS / non-`bytesN`) and the RHS tuple `items`, lower every component: one
    whose target is `bytesN size` AND whose expression is a width-EXPANDING bit
    op (`Expr.isFixedBytesBitOpShape`, i.e. `<<` / `~`) is routed through
    `Expr.toCoreFixedBytesBitOp?` (the SAME per-op `cleanup_t_bytesN` mask the
    single-assign path emits via `assignmentCoreWithEnv?`); every other component
    keeps its exact env-LESS `Expr.toCore?` core (byte-identical). Returns the
    lowered component list paired with a flag that is `true` iff at least one
    mask was inserted, so the caller only reroutes tuples that actually need the
    cleanup and leaves every other tuple's prior lowering untouched. A bare
    string/hex literal assigned to a `bytesN` component also needs the declared
    component type: env-less literal lowering produces dynamic bytes and later
    assignment panics, whereas a single declaration already target-types it.
    Route that literal through the same target-aware lowering and mark the tuple
    changed. `none` on a hole RHS component or an arity mismatch. -/
def TupleItems.toCoreRhsBitAwareExprs? (storageNames : List Name) (env : TypeEnv) :
    List (Option Ty) -> List TupleItem -> Option (List CoreExpr × Bool)
  | [], [] => some ([], false)
  | ty? :: tyRest, TupleItem.value rhsExpr :: itemRest => do
      let (restCore, restMasked) ←
        TupleItems.toCoreRhsBitAwareExprs? storageNames env tyRest itemRest
      -- A tuple component is still a value-use boundary. In particular,
      -- `(uint8 value,) = (a + b, 0)` must evaluate `a + b` at its inferred
      -- narrow source width before assigning the component. The ordinary
      -- tuple path lowers every item env-less and loses that Panic 0x11.
      match (do
          let ty ← ty?
          if Expr.abiArgNeedsEnvCleanup? rhsExpr then
            Expr.toCoreAsWithEnv? storageNames env ty rhsExpr
          else none) with
      | some envAware => some (envAware :: restCore, true)
      | none =>
      match (do
          let ty ← ty?
          let _ ← Ty.fixedBytesSize? ty
          match rhsExpr with
          | Expr.literal (Literal.string _)
          | Expr.literal (Literal.hexString _) =>
              Expr.toCoreAsWithEnv? storageNames env ty rhsExpr
          | _ => none) with
      | some targetTyped => some (targetTyped :: restCore, true)
      | none =>
      match (do
          let ty ← ty?
          let size ← Ty.fixedBytesSize? ty
          if Expr.isFixedBytesBitOpShape rhsExpr then
            Expr.toCoreFixedBytesBitOp? storageNames env size rhsExpr
          else none) with
      | some masked => some (masked :: restCore, true)
      | none => do
          let core ← Expr.toCore? storageNames rhsExpr
          some (core :: restCore, restMasked)
  | _, _ => none

/-- FB1 (tuple-RHS lane cleanup), ASSIGNMENT form `(x, y, …) = (r0, r1, …)`.
    The plain env-LESS tuple-assign lowering (`tupleAssignmentCore?` via
    `Expr.toCore?`) has no per-component target type, so a `bytesN` `<<` / `~`
    RHS component kept its shifted-out / high bits (wrong value). Take each
    component's target type from the LHS component (`Expr.abiTyWithEnv?`; a hole
    LHS has no target) and re-lower through
    `TupleItems.toCoreRhsBitAwareExprs?`. Only fires when a mask was actually
    inserted (`masked`) and the LHS is flat; otherwise the caller keeps the
    unchanged path. -/
def tupleAssignBitAwareCore? (storageNames : List Name) (env : TypeEnv)
    (lhsItems rhsItems : List TupleItem) : Option CoreStmt := do
  if TupleItems.hasNestedTuple lhsItems then none
  else do
    let tys := lhsItems.map (fun item =>
      match item with
      | TupleItem.value e => Expr.abiTyWithEnv? env e
      | TupleItem.hole => none)
    let (coreExprs, masked) ←
      TupleItems.toCoreRhsBitAwareExprs? storageNames env tys rhsItems
    if masked then do
      let targets ← TupleItems.toCoreLValueTargets? storageNames lhsItems
      some
        (SolidCore.Solidity.Source.Stmt.assignTuple targets
          (SolidCore.Solidity.Source.Expr.tuple coreExprs))
    else none

/-- FB1 (tuple-RHS lane cleanup), DECLARATION form `(T0 a, …) = (r0, …)`. Same
    fix as `tupleAssignBitAwareCore?`, but the per-component target type is the
    declared binding type and the pieces mirror the literal-tuple decl lowering
    (`tupleVarDeclCorePieces?`): the fresh-local decls followed by a single
    `assignTuple`, differing only in the masked component cores. -/
def tupleVarDeclBitAwarePieces? (storageNames : List Name) (env : TypeEnv)
    (bindings : List VarBinding) (items : List TupleItem) :
    Option (List CoreStmt) := do
  if bindings.length == items.length then do
    let (coreExprs, masked) ←
      TupleItems.toCoreRhsBitAwareExprs? storageNames env
        (bindings.map (fun b => b.ty)) items
    if masked then do
      let coreDecls ← VarBindings.toCoreTupleDecls? bindings
      let targets ← VarBindings.toCoreTupleTargets? bindings
      some
        (coreDecls ++
          [ SolidCore.Solidity.Source.Stmt.assignTuple targets
              (SolidCore.Solidity.Source.Expr.tuple coreExprs) ])
    else none
  else none

def varDeclCoreWithEnv? (storageNames : List Name)
    (env : TypeEnv) (binding : VarBinding) (expr : Expr) :
    Option CoreStmt := do
  match binding.name, binding.ty, binding.location with
  | some _, some _, some DataLocation.storage =>
      Stmt.toCore? storageNames (Stmt.varDecl [binding] (some expr))
  | some name, some ty, _ => do
      let coreTy ← Ty.toCore? ty
      let initCore ← Expr.structCtorTupleCoreAsWithEnv? storageNames env ty expr
      if binding.location == some DataLocation.memory then
        some
          (SolidCore.Solidity.Source.Stmt.memoryVarDecl
            coreTy name (some initCore))
      else
        some
          (SolidCore.Solidity.Source.Stmt.varDecl
            coreTy name (some initCore))
  | _, _, _ => none
termination_by (2, 0, 0, 0)

/-- TUP-IDX: hoist internal-function calls out of the INDEX operand of a
    tuple-assignment LHS component. For each component `base[iname(iargs)]`
    (an internal call in the array-index / mapping-key position), bind the
    call result into a per-component temp and build the tuple lvalue target
    from that temp read, mirroring the MI1 single-assign path
    (`Expr.assign (Expr.index base (call)) …`). Non-call-index components (a
    plain lvalue, or an index whose operand is a param/storage-read/constant)
    keep the ordinary pure `Expr.toCoreLValue?` path unchanged — no behaviour
    change. Returns the prefix statements (the per-component index-call temp
    binders, concatenated LEFT-to-right) and the resulting target list; the
    caller sequences these AFTER the RHS temps so solc's order (RHS
    left-to-right, THEN LHS index expressions left-to-right) is preserved. -/
def FunctionDecl.tupleLhsIndexCallHoistTargets?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) :
    Nat -> List TupleItem ->
      Option (List CoreStmt × List (Option CoreLValue))
  | _, [] => some ([], [])
  | idx, TupleItem.hole :: rest => do
      let (restPre, restTargets) ←
        FunctionDecl.tupleLhsIndexCallHoistTargets?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions (idx + 1) rest
      some (restPre, none :: restTargets)
  | idx,
      TupleItem.value
        (Expr.index base (Expr.call (Expr.ident iname) iargs)) :: rest => do
      let tmp := "_sol_lhs_index_call_" ++ toString idx
      let idxTy ←
        Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env
          (Expr.call (Expr.ident iname) iargs)
      let idxCoreTy ← Ty.toCore? idxTy
      let baseLV ← Expr.toCoreLValueWithEnvCleanup? storageNames env base
      let buildLV := fun index =>
        SolidCore.Solidity.Source.LValue.index baseLV index
      let hoisted ←
        FunctionDecl.internalSingleReturnCallCore?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions iname iargs
          (fun idxCore =>
            SolidCore.Solidity.Source.Stmt.assign
              (SolidCore.Solidity.Source.LValue.var tmp) idxCore)
      let (restPre, restTargets) ←
        FunctionDecl.tupleLhsIndexCallHoistTargets?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions (idx + 1) rest
      some
        ( [ SolidCore.Solidity.Source.Stmt.varDecl idxCoreTy tmp none
          , hoisted ] ++ restPre
        , some (buildLV (SolidCore.Solidity.Source.Expr.var tmp))
            :: restTargets )
  | idx, TupleItem.value expr :: rest => do
      let target ←
        if Expr.abiArgNeedsEnvCleanup? expr then
          Expr.toCoreLValueWithEnv? storageNames env expr
        else
          Expr.toCoreLValue? storageNames expr
      let (restPre, restTargets) ←
        FunctionDecl.tupleLhsIndexCallHoistTargets?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions (idx + 1) rest
      some (restPre, some target :: restTargets)
termination_by _ items => (3, internalFuel, sizeOf items, 8)

/-- Lower tuple-assignment targets that include the storage reference returned
    by a zero-argument push on a direct state array.  The returned prefix grows
    those arrays, left-to-right, and each corresponding target names the newly
    appended element.  We deliberately keep this helper to direct arrays: for
    `matrix[i()].push()` the path expression must be captured once and reused,
    while spelling it in both a push statement and a later lvalue would evaluate
    `i()` twice.  Those effectful nested paths therefore remain rejected until
    they have a dedicated captured-path core operation. -/
def TupleItems.toCoreLValueTargetsWithDirectPush?
    (storageNames : List Name) :
    List TupleItem ->
      Option (List CoreStmt × List (Option CoreLValue) × Bool)
  | [] => some ([], [], false)
  | TupleItem.hole :: rest => do
      let (restPre, restTargets, restHasPush) ←
        TupleItems.toCoreLValueTargetsWithDirectPush? storageNames rest
      some (restPre, none :: restTargets, restHasPush)
  | TupleItem.value
      (Expr.call (Expr.member target "push") []) :: rest => do
      let (name, indexes) ← Expr.storagePathCore? storageNames target
      match indexes with
      | [] => do
          let pushStmt ← storageArrayPushPathCore? storageNames target none
          let lastIndex := storageLastPushedIndexExpr name []
          let (restPre, restTargets, _) ←
            TupleItems.toCoreLValueTargetsWithDirectPush? storageNames rest
          some
            ( pushStmt :: restPre
            , some (SolidCore.Solidity.Source.LValue.storageIndex name lastIndex)
                :: restTargets
            , true )
      | _ => none
  | TupleItem.value expr :: rest => do
      let target ← Expr.toCoreLValue? storageNames expr
      let (restPre, restTargets, restHasPush) ←
        TupleItems.toCoreLValueTargetsWithDirectPush? storageNames rest
      some (restPre, some target :: restTargets, restHasPush)
termination_by items => (sizeOf items, 1)

/-- Recover the destination type of each flat tuple-assignment component.  A
    push-return target has the element type of its dynamic array; a hole uses
    the corresponding RHS component's type because it still must be evaluated.
    These types drive the RHS temporaries used by the push-target lowering, so
    implicit narrow conversions happen before any LHS push side effect. -/
def FunctionDecl.tupleAssignTargetTysWithDirectPush?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv) :
    List TupleItem -> List TupleItem -> Option (List Ty)
  | [], [] => some []
  | TupleItem.hole :: lhsRest, TupleItem.value rhs :: rhsRest => do
      let ty ←
        Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env rhs
      let rest ←
        FunctionDecl.tupleAssignTargetTysWithDirectPush?
          functions freeFunctions env lhsRest rhsRest
      some (ty :: rest)
  | TupleItem.value
      (Expr.call (Expr.member target "push") []) :: lhsRest,
      TupleItem.value _ :: rhsRest => do
      let targetTy ← Expr.abiTyWithEnv? env target
      let elemTy ←
        match targetTy with
        | Ty.array elemTy none => some elemTy
        | _ => none
      let rest ←
        FunctionDecl.tupleAssignTargetTysWithDirectPush?
          functions freeFunctions env lhsRest rhsRest
      some (elemTy :: rest)
  | TupleItem.value lhs :: lhsRest, TupleItem.value _ :: rhsRest => do
      let ty ← Expr.abiTyWithEnv? env lhs
      let rest ←
        FunctionDecl.tupleAssignTargetTysWithDirectPush?
          functions freeFunctions env lhsRest rhsRest
      some (ty :: rest)
  | _, _ => none
termination_by lhs _ => (sizeOf lhs, 1)

/-- A compound assignment through `array.push()` evaluates its RHS first, then
    grows the array, reads the new zero element, applies the operation, and
    writes it back.  solc's IR makes this ordering observable for an RHS that
    mutates or reads the same array.  Snapshot the converted RHS in a scoped
    temp before emitting the push; the usual cleanup node then provides the
    element-width overflow/truncation semantics.  As above, only direct state
    arrays are accepted so no path expression is duplicated. -/
def Expr.storageArrayDirectPushAssignOpCoreWithEnv?
    (storageNames : List Name) (env : TypeEnv) : Expr -> Option CoreStmt
  | Expr.assign
      (Expr.call (Expr.member target "push") []) op rhs => do
      let (name, indexes) ← Expr.storagePathCore? storageNames target
      match indexes with
      | [] => do
          let targetTy ← Expr.abiTyWithEnv? env target
          let elemTy ←
            match targetTy with
            | Ty.array elemTy none => some elemTy
            | _ => none
          let elemCoreTy ← Ty.toCore? elemTy
          let coreOp ← AssignOp.toCoreBinary? op
          let rhsCore ←
            match Expr.toCoreAsWithEnv? storageNames env elemTy rhs with
            | some core => some core
            | none => Expr.toCore? storageNames rhs
          let cleanup ← Ty.toCoreValueCleanup? elemTy
          let rhsTmp : Name := "_sol_push_assign_rhs"
          let pushStmt ← storageArrayPushPathCore? storageNames target none
          let lastIndex := storageLastPushedIndexExpr name []
          let lhs :=
            SolidCore.Solidity.Source.LValue.storageIndex name lastIndex
          some
            (SolidCore.Solidity.Source.Stmt.block
              [ CoreTy.tempDeclStmt elemCoreTy rhsTmp (some rhsCore)
              , pushStmt
              , SolidCore.Solidity.Source.Stmt.exprStmt
                  (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
                    lhs.toExpr coreOp
                    (SolidCore.Solidity.Source.Expr.var rhsTmp) cleanup) ])
      | _ => none
  | _ => none

/-- Environment-aware form of assignment through a subfield/index of the
    reference returned by `array.push()`.  The destination type is recovered by
    walking the array element type down the trailing index path, so the RHS is
    checked at that exact width before the push mutates storage. -/
def Expr.storageArrayPushIndexedAssignCoreWithEnv?
    (storageNames : List Name) (env : TypeEnv)
    (lhs rhs : Expr) : Option CoreStmt := do
  let (target, trailing) ← Expr.stripPushIndexPath? lhs
  match trailing with
  | [] => none
  | _ =>
      let (name, indexes) ← Expr.storagePathCore? storageNames target
      match indexes with
      | [] => do
          let targetTy ← Expr.abiTyWithEnv? env target
          let elemTy ←
            match targetTy with
            | Ty.array elemTy none => some elemTy
            | _ => none
          let valueTy ← Ty.peelIndexSpineTy? elemTy trailing
          let rhsCore ← Expr.toCoreAsWithEnv? storageNames env valueTy rhs
          let trailingCore ←
            mapOption
              (Expr.abiArgCoreWithEnvCleanup? storageNames env) trailing
          let lastIndex := storageLastPushedIndexExpr name []
          let baseLv :=
            SolidCore.Solidity.Source.LValue.storageIndex name lastIndex
          let lv :=
            trailingCore.foldl
              (fun acc idx => SolidCore.Solidity.Source.LValue.index acc idx)
              baseLv
          some
            (SolidCore.Solidity.Source.Stmt.block
              [ SolidCore.Solidity.Source.Stmt.storageArrayPush name none
              , SolidCore.Solidity.Source.Stmt.assign lv rhsCore ])
      | _ => none

def FunctionDecl.tupleItemsUseCoreWithInternalCalls?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (fallbackPrefix : String) :
    Nat -> List Ty -> List TupleItem -> (List CoreExpr -> CoreStmt) ->
      Option CoreStmt
  | _, [], [], useItems => some (useItems [])
  | index, targetTy :: targetTys, TupleItem.value expr :: rest, useItems => do
      let tmp := internalCallArgTempName fallbackPrefix index
      let tmpTy ← Ty.toCore? targetTy
      let assignCore ←
        match Expr.toCoreAsWithEnv? storageNames env targetTy expr with
        | some coreExpr =>
            some
              (SolidCore.Solidity.Source.Stmt.assign
                (SolidCore.Solidity.Source.LValue.var tmp)
                coreExpr)
        | none =>
            FunctionDecl.internalExprSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions expr
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var tmp)
                  (Ty.implicitCleanupCore targetTy resultExpr))
      let restCore ←
        FunctionDecl.tupleItemsUseCoreWithInternalCalls?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions fallbackPrefix
          (index + 1) targetTys rest
          (fun coreExprs =>
            useItems
              (SolidCore.Solidity.Source.Expr.var tmp :: coreExprs))
      some
        (SolidCore.Solidity.Source.Stmt.block
          [ SolidCore.Solidity.Source.Stmt.varDecl tmpTy tmp none
          , assignCore
          , restCore ])
  | _, _, _, _ => none
termination_by _ _ items _ =>
  (3, internalFuel, sizeOf (Expr.tuple items), 10)

/-- R1 (residue-cleanup): hoist internal calls out of ONE component of a
    nested-tuple-assignment RHS, returning (prefix statements, the temp-read
    expression that replaces the component). Every leaf component is evaluated,
    left-to-right, into its own uniquely named temp (`tag` encodes the tree
    path so names never collide), preserving solc's temps-then-stores order; a
    direct MULTI-return internal call in a nested-target position is captured
    into per-return outer temps and replaced by an `Expr.tuple` of their reads
    (`((a, b), c) = (foo(), bar())` with `foo` returning a 2-tuple); a
    parenthesized sub-tuple `((foo(), bar()), baz())` recurses. -/
def FunctionDecl.nestedTupleRhsHoistItem?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (tag : String) : TupleItem -> Option (List CoreStmt × CoreExpr)
  | TupleItem.hole => none
  | TupleItem.value (Expr.tuple subItems) => do
      let (pre, exprs) ←
        FunctionDecl.nestedTupleRhsHoistList?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions tag 0 subItems
      some (pre, SolidCore.Solidity.Source.Expr.tuple exprs)
  | TupleItem.value expr =>
      let multiReturn? : Option (List CoreStmt × CoreExpr) :=
        match expr with
        | Expr.call (Expr.ident name) callArgs =>
            match FunctionDecl.internalCalleeReturnTys?
                functions freeFunctions env name callArgs with
            | some (t0 :: t1 :: ts) => do
                let retTys := t0 :: t1 :: ts
                let (returnBindings, returnStorageRefs, prefixCore, bodyCore) ←
                  FunctionDecl.internalCallParts?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions name callArgs
                if returnStorageRefs.any id then none else some ()
                let returnNames :=
                  returnBindings.map SolidCore.Solidity.Source.BindingDecl.name
                if returnNames.length == retTys.length then some () else none
                let outerNames :=
                  (List.range retTys.length).map
                    (fun j => tag ++ "_r" ++ toString j)
                let outerDecls ←
                  mapOption
                    (fun (p : Ty × Name) => do
                      let cty ← Ty.toCore? p.fst
                      some
                        (SolidCore.Solidity.Source.Stmt.varDecl cty p.snd none))
                    (retTys.zip outerNames)
                let copies :=
                  (outerNames.zip returnNames).map
                    (fun p =>
                      SolidCore.Solidity.Source.Stmt.assign
                        (SolidCore.Solidity.Source.LValue.var p.fst)
                        (SolidCore.Solidity.Source.Expr.var p.snd))
                let inner :=
                  SolidCore.Solidity.Source.Stmt.block
                    (prefixCore ++
                      [SolidCore.Solidity.Source.Stmt.captureReturn
                        returnNames bodyCore] ++ copies)
                some
                  ( outerDecls ++ [inner]
                  , SolidCore.Solidity.Source.Expr.tuple
                      (outerNames.map SolidCore.Solidity.Source.Expr.var) )
            | _ => none
        | _ => none
      match multiReturn? with
      | some result => some result
      | none => do
          let ty ←
            Expr.abiTyWithInternalFunctionsEnv? functions freeFunctions env expr
          let cty ← Ty.toCore? ty
          let assignStmt ←
            match Expr.toCoreAsWithEnv? storageNames env ty expr with
            | some coreExpr =>
                some
                  (SolidCore.Solidity.Source.Stmt.assign
                    (SolidCore.Solidity.Source.LValue.var tag) coreExpr)
            | none =>
                FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions expr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var tag)
                      (Ty.implicitCleanupCore ty resultExpr))
          some
            ( [ SolidCore.Solidity.Source.Stmt.varDecl cty tag none, assignStmt ]
            , SolidCore.Solidity.Source.Expr.var tag )
termination_by item => (3, internalFuel, sizeOf item, 18)

/-- List form of `nestedTupleRhsHoistItem?`: hoist a whole RHS component list,
    left-to-right, concatenating the prefixes and collecting one replacement
    expression per component. -/
def FunctionDecl.nestedTupleRhsHoistList?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (tag : String) : Nat -> List TupleItem -> Option (List CoreStmt × List CoreExpr)
  | _, [] => some ([], [])
  | idx, item :: rest => do
      let (headPre, headExpr) ←
        FunctionDecl.nestedTupleRhsHoistItem?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions (tag ++ "_" ++ toString idx) item
      let (restPre, restExprs) ←
        FunctionDecl.nestedTupleRhsHoistList?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          modifiers functions freeFunctions tag (idx + 1) rest
      some (headPre ++ restPre, headExpr :: restExprs)
termination_by _ items => (3, internalFuel, sizeOf items, 16)

def FunctionDecl.tupleReturnValuesCoreWithInternalCalls?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (items : List TupleItem) : Option CoreStmt :=
  match returnTys with
  | [Ty.tuple tupleTys] =>
      FunctionDecl.tupleItemsUseCoreWithInternalCalls?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions "_sol_return_tuple_item"
        0 tupleTys items
        (fun coreExprs =>
          SolidCore.Solidity.Source.Stmt.returnValues
            [SolidCore.Solidity.Source.Expr.tuple coreExprs])
  | [Ty.struct _ tupleTys] =>
      FunctionDecl.tupleItemsUseCoreWithInternalCalls?
        internalFuel storageRefEnv env externalCallKindEnv storageNames
        modifiers functions freeFunctions "_sol_return_struct_item"
        0 tupleTys items
        (fun coreExprs =>
          SolidCore.Solidity.Source.Stmt.returnValues
            [SolidCore.Solidity.Source.Expr.tuple coreExprs])
  | _ :: _ :: _ =>
      match TupleItems.toCoreExprsAsWithEnv? storageNames env returnTys items with
      | some coreExprs =>
          some (SolidCore.Solidity.Source.Stmt.returnValues coreExprs)
      | none =>
          FunctionDecl.tupleItemsUseCoreWithInternalCalls?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions "_sol_return_item"
            0 returnTys items
            (fun coreExprs =>
              SolidCore.Solidity.Source.Stmt.returnValues coreExprs)
  | _ => none
termination_by (3, internalFuel, sizeOf (Expr.tuple items) + 1, 10)

def returnValuesCoreWithReturnTys? (storageNames : List Name)
    (env : TypeEnv) (returnTys : List Ty) (expr : Expr) : Option CoreStmt :=
  match returnTys, expr with
  | [returnTy], _ => do
      match Expr.toCoreAsWithEnv? storageNames env returnTy expr with
      | some coreExpr =>
          some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
      | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
  | _ :: _ :: _, Expr.tuple items => do
      let coreExprs ←
        TupleItems.toCoreExprsAsWithEnv? storageNames env returnTys items
      some (SolidCore.Solidity.Source.Stmt.returnValues coreExprs)
  | _, _ => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
termination_by (2, 0, 0, 0)

def Expr.isLowLevelCallExpr : Expr -> Bool
  | Expr.call (Expr.member _ "call") [Arg.positional _] => true
  | Expr.callWithOptions (Expr.member _ "call") _ [Arg.positional _] => true
  | Expr.call (Expr.member _ "staticcall") [Arg.positional _] => true
  | Expr.callWithOptions (Expr.member _ "staticcall") _ [Arg.positional _] =>
      true
  | Expr.call (Expr.member _ "delegatecall") [Arg.positional _] => true
  | Expr.callWithOptions (Expr.member _ "delegatecall") _ [Arg.positional _] =>
      true
  | _ => false

def Expr.lowLevelCallCoreWithEnvCleanup? (storageNames : List Name)
    (env : TypeEnv) : Expr -> Option CoreExpr
  | Expr.call (Expr.member target "call") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call targetCore payloadCore
          (SolidCore.Solidity.Source.Expr.word 0) none false)
  | Expr.call (Expr.member target "staticcall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall targetCore payloadCore
          (SolidCore.Solidity.Source.Expr.word 0) none false)
  | Expr.call (Expr.member target "delegatecall") [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall targetCore payloadCore
          (SolidCore.Solidity.Source.Expr.word 0) none false)
  | Expr.callWithOptions (Expr.member target "call") options
      [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelCallValueGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.call targetCore payloadCore
          valueCore gasCore? gasFirst)
  | Expr.callWithOptions (Expr.member target "staticcall") options
      [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelDelegateGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.staticcall targetCore payloadCore
          valueCore gasCore? gasFirst)
  | Expr.callWithOptions (Expr.member target "delegatecall") options
      [Arg.positional payload] => do
      let targetCore ← Expr.toCore? storageNames target
      let payloadCore ← Expr.abiArgCoreWithEnvCleanup? storageNames env payload
      let (valueCore, gasCore?, gasFirst) ←
        CallOptions.lowLevelDelegateGasCore? storageNames options
      some
        (SolidCore.Solidity.Source.Expr.lowLevelCall
          SolidCore.Solidity.Source.LowLevelCallKind.delegatecall targetCore payloadCore
          valueCore gasCore? gasFirst)
  | _ => none

def Expr.lowLevelTupleReturnCore? (storageNames : List Name) (env : TypeEnv)
    (returnTys : List Ty) (expr : Expr) : Option CoreStmt := do
  if returnTys == [Ty.bool, Ty.bytes] && Expr.isLowLevelCallExpr expr then
    let returnTy ← Ty.toCore? lowLevelCallReturnTy
    let coreExpr ← Expr.lowLevelCallCoreWithEnvCleanup? storageNames env expr
    let resultName := "__solidcore_low_level_return"
    some
      (SolidCore.Solidity.Source.Stmt.block
        [ SolidCore.Solidity.Source.Stmt.varDecl
            returnTy resultName (some coreExpr)
        , SolidCore.Solidity.Source.Stmt.returnValues
            [ SolidCore.Solidity.Source.Expr.index
                (SolidCore.Solidity.Source.Expr.var resultName)
                (SolidCore.Solidity.Source.Expr.word 0)
            , SolidCore.Solidity.Source.Expr.index
                (SolidCore.Solidity.Source.Expr.var resultName)
                (SolidCore.Solidity.Source.Expr.word 1) ] ])
  else
    none

def VarBindings.lowLevelTupleReturnCompatible :
    List VarBinding -> Bool
  | [ { ty := some Ty.bool, .. }, { ty := some Ty.bytes, .. } ] => true
  | [ { ty := some Ty.bool, .. }, { name := none, ty := none, .. } ] => true
  | _ => false

def Expr.lowLevelTupleVarDeclCorePieces? (storageNames : List Name) (env : TypeEnv)
    (bindings : List VarBinding) (expr : Expr) :
    Option (List CoreStmt) := do
  if VarBindings.lowLevelTupleReturnCompatible bindings &&
      Expr.isLowLevelCallExpr expr then
    some ()
  else
    none
  let decls ← VarBindings.toCoreTupleDecls? bindings
  let targets ← VarBindings.toCoreTupleTargets? bindings
  let returnTy ← Ty.toCore? lowLevelCallReturnTy
  let coreExpr ← Expr.lowLevelCallCoreWithEnvCleanup? storageNames env expr
  let resultName := "__solidcore_low_level_return"
  some
    (decls ++
      [ SolidCore.Solidity.Source.Stmt.varDecl
          returnTy resultName (some coreExpr)
      , SolidCore.Solidity.Source.Stmt.assignTuple
          targets (SolidCore.Solidity.Source.Expr.var resultName) ])

/-- Existing-variable sibling of `lowLevelTupleVarDeclCorePieces?`.  A
    low-level call always returns `(bool, bytes)`; bind that pair once, with its
    payload lowered env-aware, then destructure it into the tuple lvalues. -/
def Expr.lowLevelTupleAssignCore? (storageNames : List Name) (env : TypeEnv)
    (lhsItems : List TupleItem) (expr : Expr) : Option CoreStmt := do
  if Expr.isLowLevelCallExpr expr then some () else none
  let targets ← TupleItems.toCoreLValueTargets? storageNames lhsItems
  if targets.length == 2 then some () else none
  let returnTy ← Ty.toCore? lowLevelCallReturnTy
  let coreExpr ← Expr.lowLevelCallCoreWithEnvCleanup? storageNames env expr
  let resultName := "__solidcore_low_level_assign"
  some
    (SolidCore.Solidity.Source.Stmt.block
      [ SolidCore.Solidity.Source.Stmt.varDecl
          returnTy resultName (some coreExpr)
      , SolidCore.Solidity.Source.Stmt.assignTuple
          targets (SolidCore.Solidity.Source.Expr.var resultName) ])

/-- CALL-POSITION CONSOLIDATED (#147-#151) generic fallback: hoist the leftmost
    STRICT-inner internal single-return call in `payload` into a prefix temp,
    then re-lower `rebuild replacedExpr` (the statement rebuilt with that call
    replaced by the temp reference) via `Stmt.toCoreWithInternalCalls?` at one
    less fuel. Each invocation peels ONE nested call, so a payload with several
    nested calls is drained by the fuel-decreasing re-entry (the residual
    statement is what the ordinary call-position arms lower once its
    argument-like positions are call-free). Returns `none` when `payload` has no
    strictly-nested internal call the walker reaches, or when the hoisted call /
    residual statement fails to lower, preserving the prior over-reject rather
    than emitting unsound code. solc evaluates these argument-like positions
    left-to-right and before the consuming construct; the walker peels in that
    order and the prefix runs before the residual, matching solc. -/
def Stmt.argPositionHoist? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (payload : Expr) (rebuild : Expr -> Stmt) : Option CoreStmt :=
  match internalFuel with
  | 0 => none
  | fuel + 1 =>
    let tmp := "_sol_argpos_" ++ toString fuel
    -- Walk budget: a plain (computable) node bound comfortably exceeding any
    -- realistic argument-position expression depth (`sizeOf` is intentionally
    -- avoided here — it has no executable code, which would infect the whole
    -- lowering with `noncomputable`).
    match
        Expr.findArgPosInnerCall?
          (functions ++ freeFunctions) env tmp true 100000 payload with
    | some (callExpr, retTy, replacedExpr) => do
        let retCoreTy ← Ty.toCore? retTy
        let callCore ←
          FunctionDecl.internalExprSingleReturnUseCore?
            fuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions callExpr
            (fun c =>
              SolidCore.Solidity.Source.Stmt.assign
                (SolidCore.Solidity.Source.LValue.var tmp) c)
        let restCore ←
          Stmt.toCoreWithInternalCalls?
            fuel storageRefEnv ((tmp, retTy) :: env) externalCallKindEnv
            storageNames modifiers functions freeFunctions returnTys
            (rebuild replacedExpr)
        some
          (SolidCore.Solidity.Source.Stmt.block
            [ SolidCore.Solidity.Source.Stmt.varDecl retCoreTy tmp none
            , callCore
            , restCore ])
    | none => none
termination_by (3, internalFuel, sizeOf payload, 0)

/- CALL-POSITION CONSOLIDATED (#148-#150) list-level peel: hoist EVERY
   strictly-nested internal single-return call inside `payload` into FLAT,
   ordered prefix statements (`retTy _tmp; _tmp = call`) and return them together
   with the fully argument-position-call-free residual expression. Unlike the
   block-wrapping `Stmt.argPositionHoist?`, this returns the temps as a flat list
   so a variable-declaration statement can be re-lowered with its local spliced
   as a SIBLING (a block would scope the local out before later statements). The
   peel is left-to-right / innermost-first, matching solc's argument evaluation
   order. `none` only if a hoisted call fails to lower. -/
def Expr.argPositionHoistPrefix? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (payload : Expr) :
    Option (List CoreStmt × Expr) :=
  match internalFuel with
  | 0 => some ([], payload)
  | fuel + 1 =>
    let tmp := "_sol_argpos_" ++ toString fuel
    match
        Expr.findArgPosInnerCall?
          (functions ++ freeFunctions) env tmp true 100000 payload with
    | some (callExpr, retTy, replacedExpr) =>
        (do
          let retCoreTy ← Ty.toCore? retTy
          let callCore ←
            FunctionDecl.internalExprSingleReturnUseCore?
              fuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions callExpr
              (fun c =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var tmp) c)
          let (restPieces, finalExpr) ←
            Expr.argPositionHoistPrefix? fuel storageRefEnv
              ((tmp, retTy) :: env) externalCallKindEnv storageNames modifiers
              functions freeFunctions replacedExpr
          some
            (SolidCore.Solidity.Source.Stmt.varDecl retCoreTy tmp none
                :: callCore :: restPieces
            , finalExpr))
    | none => some ([], payload)
termination_by (3, internalFuel, sizeOf payload, 2)

def storageVarDeclCoreWithEnv? (storageNames : List Name) (env : TypeEnv)
    (binding : VarBinding) (source : Expr) : Option CoreStmt := do
  if binding.location != some DataLocation.storage then none else some ()
  let name ← binding.name
  let _ ← binding.ty
  match source with
  | Expr.call (Expr.member target "push") [] =>
      storageArrayPushReturnAliasBlockCore? storageNames binding target
  | _ => do
      storageReferenceBindingSupported? binding
      let (target, indexes) ←
        Expr.storagePathCoreWithEnv? storageNames env source
      match indexes with
      | [] =>
          some (SolidCore.Solidity.Source.Stmt.storageAlias name target)
      | _ =>
          some
            (SolidCore.Solidity.Source.Stmt.storageAliasPath
              name target indexes)

/-- Hoist calls nested in a storage-reference declaration's path without
    converting the residual path to a value. The returned statements are flat
    siblings so the declared storage pointer survives in the enclosing scope. -/
def storageVarDeclArgPositionHoistPieces? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (binding : VarBinding) (source : Expr) : Option (List CoreStmt) :=
  match internalFuel with
  | 0 => none
  | fuel + 1 => do
      let (prefixStmts, residual) ←
        Expr.argPositionHoistPrefix? fuel storageRefEnv env
          externalCallKindEnv storageNames modifiers functions freeFunctions source
      match prefixStmts with
      | [] => none
      | _ :: _ => do
          let aliasStmt ←
            storageVarDeclCoreWithEnv? storageNames env binding residual
          some (prefixStmts ++ [aliasStmt])

/-- Lower one component of an all-storage-pointer tuple declaration as flat
    statements. Existing storage locals remain aliases, and a push-return
    component emits its push and alias as siblings rather than a nested block. -/
def storageTupleDeclItemPiecesWithEnv? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name)
    (binding : VarBinding) (item : Expr) : Option (List CoreStmt) :=
  match item with
  | Expr.call (Expr.member target "push") [] => do
      let (pushStmt, aliasStmt) ←
        storageArrayPushReturnAliasCore? storageNames binding target
      some [pushStmt, aliasStmt]
  | Expr.ident source =>
      match storageAliasDeclFromRefCore? storageRefEnv binding source with
      | some stmt => some [stmt]
      | none => (storageVarDeclCoreWithEnv? storageNames env binding item).map
          (fun stmt => [stmt])
  | Expr.member _ _
  | Expr.index _ _ =>
      match storageAliasDeclFromRefPathCore?
          storageRefEnv env storageNames binding item with
      | some stmt => some [stmt]
      | none => (storageVarDeclCoreWithEnv? storageNames env binding item).map
          (fun stmt => [stmt])
  | _ => (storageVarDeclCoreWithEnv? storageNames env binding item).map
      (fun stmt => [stmt])

def storageTupleDeclItemsPiecesWithEnv? (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (storageNames : List Name) :
    List VarBinding -> List TupleItem -> Option (List CoreStmt)
  | [], [] => some []
  | binding :: bindings, TupleItem.value item :: items => do
      let head ←
        storageTupleDeclItemPiecesWithEnv?
          storageRefEnv env storageNames binding item
      let tail ←
        storageTupleDeclItemsPiecesWithEnv?
          storageRefEnv env storageNames bindings items
      some (head ++ tail)
  | _, _ => none
termination_by bindings _ => sizeOf bindings

/-- Environment-aware, call-hoisting all-storage tuple binder. Calls in RHS
    paths are evaluated into flat prefix temps before any aliases are created. -/
def storageTupleDeclAllPiecesWithEnv? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (bindings : List VarBinding) (items : List TupleItem) :
    Option (List CoreStmt) := do
  if bindings.length == items.length then some () else none
  if VarBindings.allStoragePointers bindings then some () else none
  match
      storageTupleDeclItemsPiecesWithEnv?
        storageRefEnv env storageNames bindings items with
  | some pieces => some pieces
  | none =>
      match internalFuel with
      | 0 => none
      | fuel + 1 => do
          let (prefixStmts, residual) ←
            Expr.argPositionHoistPrefix? fuel storageRefEnv env
              externalCallKindEnv storageNames modifiers functions freeFunctions
              (Expr.tuple items)
          match prefixStmts, residual with
          | _ :: _, Expr.tuple residualItems => do
              let aliases ←
                storageTupleDeclItemsPiecesWithEnv?
                  storageRefEnv env storageNames bindings residualItems
              some (prefixStmts ++ aliases)
          | _, _ => none

/-- Hoist calls from the condition of a ternary storage-reference declaration
    while leaving branch selection lazy and the resulting alias in outer scope. -/
def storageTernaryConditionAliasPieces? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (binding : VarBinding)
    (cond thenExpr elseExpr : Expr) : Option (List CoreStmt) :=
  match cond with
  | Expr.call (Expr.ident name) args => do
      let (returnBindings, _, prefixCore, bodyCore) ←
        FunctionDecl.internalCallParts? internalFuel storageRefEnv env
          externalCallKindEnv storageNames modifiers functions freeFunctions
          name args
      match returnBindings with
      | [ret] => do
          let aliasStmt ←
            storageAliasDeclFromTernaryCore? storageRefEnv env storageNames binding
              (Expr.ident ret.name) thenExpr elseExpr
          some
            (prefixCore ++
              [ SolidCore.Solidity.Source.Stmt.captureReturn
                  [ret.name] bodyCore
              , aliasStmt ])
      | _ => none
  | _ =>
      match internalFuel with
      | 0 => none
      | fuel + 1 => do
          let (prefixStmts, residualCond) ←
            Expr.argPositionHoistPrefix? fuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions cond
          match prefixStmts with
          | [] => none
          | _ :: _ => do
              let aliasStmt ←
                storageAliasDeclFromTernaryCore? storageRefEnv env storageNames binding
                  residualCond thenExpr elseExpr
              some (prefixStmts ++ [aliasStmt])

def retargetInternalCallCore? (target : Name) : CoreStmt -> Option CoreStmt
  | SolidCore.Solidity.Source.Stmt.internalCall _ callee args =>
      some (SolidCore.Solidity.Source.Stmt.internalCall [target] callee args)
  | SolidCore.Solidity.Source.Stmt.internalCallPtr _ callee args =>
      some (SolidCore.Solidity.Source.Stmt.internalCallPtr [target] callee args)
  | _ => none

/-- Bind a storage pointer from a ternary whose selected branch may call a
    function returning a storage reference. Declare the destination once, then
    have each selected branch re-point that existing binding. -/
def storageTernaryBranchAliasPieces? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (binding : VarBinding)
    (cond thenExpr elseExpr : Expr) : Option (List CoreStmt) := do
  let localName ← binding.name
  if binding.location == some DataLocation.storage then some () else none
  let condCore ← Expr.toCoreAsWithEnv? storageNames env Ty.bool cond
  let branchCore := fun branch =>
    match branch with
    | Expr.call (Expr.ident name) args => do
        let (_, returnStorageRefs, prefixCore, bodyCore) ←
          FunctionDecl.internalCallParts? internalFuel storageRefEnv env
            externalCallKindEnv storageNames modifiers functions freeFunctions
            name args
        if returnStorageRefs == [true] then some () else none
        let callCore ← retargetInternalCallCore? localName bodyCore
        match prefixCore with
        | [] => some callCore
        | _ => some (SolidCore.Solidity.Source.Stmt.block
            (prefixCore ++ [callCore]))
    | _ =>
        storageAliasAssignmentExprCore?
          storageRefEnv env storageNames localName branch
  let thenCore ← branchCore thenExpr
  let elseCore ← branchCore elseExpr
  some
    [ SolidCore.Solidity.Source.Stmt.storageAlias localName ""
    , SolidCore.Solidity.Source.Stmt.ifElse condCore thenCore elseCore ]

def Stmt.lowerCore? (internalFuel : Nat) (ctx? : Option StmtLoweringCtx)
    (storageNames : List Name) (stmt : Stmt) : Option CoreStmt :=
  -- ITEM-2 (§3c collapse, phase 1): statements whose lowering is IDENTICAL
  -- with and without a ctx are dispatched ONCE, before the ctx? split — the
  -- arm pairs the env-aware/env-less halves used to duplicate
  -- (block/unchecked: the env-aware half re-spelled the ctx?-some recursion
  -- with ten named arguments) or reach only through the env-less default
  -- (empty/inline-assembly/break/continue). Byte-identity: `block` merges
  -- `listToCoreWithInternalCallsWithRefs?` (definitionally
  -- `listLowerCore? (some ctx)`) with `listLowerCore? none`; `unchecked`
  -- merges `toCoreWithInternalCalls?` (definitionally
  -- `lowerCore? (some ctx)`) with `lowerCore? none`; the four constants were
  -- reached identically through the env-less fallback when a ctx was
  -- present.
  match stmt with
  | Stmt.empty => some SolidCore.Solidity.Source.Stmt.skip
  | Stmt.inlineAssembly "" => some SolidCore.Solidity.Source.Stmt.skip
  -- Solidity accepts the special base-dispatch namespace as a bare
  -- expression statement (`super;`). Merely evaluating that namespace has
  -- no runtime effect; only a member call such as `super.f()` dispatches.
  | Stmt.expr (Expr.ident "super") =>
      some SolidCore.Solidity.Source.Stmt.skip
  | Stmt.break => some SolidCore.Solidity.Source.Stmt.break
  | Stmt.continue => some SolidCore.Solidity.Source.Stmt.continue
  | Stmt.block body => do
      let coreBody ← Stmt.listLowerCore? internalFuel ctx? storageNames body
      some (SolidCore.Solidity.Source.Stmt.block coreBody)
  | Stmt.unchecked body => do
      let coreBody ← Stmt.lowerCore? internalFuel ctx? storageNames body
      some (SolidCore.Solidity.Source.Stmt.unchecked coreBody)
  | stmt =>
  match ctx? with
  | some ctx =>
      let storageRefEnv := ctx.storageRefEnv
      let env := ctx.env
      let externalCallKindEnv := ctx.externalCallKindEnv
      let modifiers := ctx.modifiers
      let functions := ctx.functions
      let freeFunctions := ctx.freeFunctions
      let returnTys := ctx.returnTys
      -- SHADOW-LOCAL (soundness): drop names a nearer local shadows so a bare
      -- shadowed identifier lowers as that local, not the same-name state variable
      -- (see `TypeEnv.shadowedStateNames`). Params/named returns are excluded
      -- upstream (`bodyStorageNames`); this covers body-level (incl. nested-block)
      -- locals, re-derived from the current `env` so it respects C99 scoping.
      let storageNames :=
        stateNamesExcludingBound (TypeEnv.shadowedStateNames env) storageNames
      (match stmt with
      | Stmt.expr
          (Expr.assign lhs@(Expr.index
            (Expr.call (Expr.member _ "push") []) _) AssignOp.assign rhs) =>
          match Expr.storageArrayPushIndexedAssignCoreWithEnv?
              storageNames env lhs rhs with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr (Expr.assign lhs AssignOp.assign rhs))
      | Stmt.expr
          (Expr.assign lhs@(Expr.call (Expr.member target "push") [])
            AssignOp.assign rhs) =>
          match storageArrayPushPathCoreWithEnv? env storageNames target rhs with
          | some coreStmt => some coreStmt
          | none =>
              match Expr.storageRefArrayPushAssignStmtCore?
                  storageRefEnv env storageNames target rhs with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr (Expr.assign lhs AssignOp.assign rhs))
      | Stmt.expr expr@(Expr.unary UnaryOp.preIncrement _)
      | Stmt.expr expr@(Expr.unary UnaryOp.preDecrement _)
      | Stmt.expr expr@(Expr.unary UnaryOp.postIncrement _)
      | Stmt.expr expr@(Expr.unary UnaryOp.postDecrement _) =>
          match Expr.toCoreIncDecWithEnv? env
              (Expr.toCoreLValueWithEnvCleanup? storageNames env) expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none => Stmt.toCore? storageNames (Stmt.expr expr)
      -- Compound assignment (`+= -= *= /= %= &= |= ^= <<= >>= >>>=`) to a narrow
      -- (`< 256`-bit) int/uint LValue must apply the LValue-type-width cleanup that
      -- solc emits for the read-modify-write result — a checked cleanup (Panic
      -- 0x11 on overflow) for the arithmetic ops, and a *truncating* cast for
      -- `<<=` (which never overflow-checks, even in a checked block). Route these
      -- through the env-aware `Expr.toCoreAssignOpWithEnv?` (which emits
      -- `assignOpCleanupExpr` carrying the width cleanup) exactly as inc/dec above
      -- routes through `Expr.toCoreIncDecWithEnv?`. The plain-`assign` op is *not*
      -- matched here (only the compound ops), so the later tuple/call assign arms
      -- and the raw-`assignOp` default are untouched; when the RHS is a call the
      -- env-less lowering returns `none` and we fall back exactly as before.
      | Stmt.expr expr@(Expr.assign _ AssignOp.addAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.subAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.mulAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.divAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.modAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.bitAndAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.bitOrAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.bitXorAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.shlAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.shrAssign _)
      | Stmt.expr expr@(Expr.assign _ AssignOp.sarAssign _) =>
          -- A zero-argument storage-array push is itself an lvalue: the newly
          -- appended element.  It cannot pass through ordinary lvalue lowering
          -- because the call is also an effect.  Snapshot the RHS, then push,
          -- then use the standard compound-cleanup expression on that element.
          match
              Expr.storageArrayDirectPushAssignOpCoreWithEnv?
                storageNames env expr with
          | some coreStmt => some coreStmt
          | none =>
          -- Shift counts retain their own type. Evaluate a flagged RHS through
          -- the env-aware lowerer before the read-modify-write so narrow checked
          -- arithmetic Panics at its operand width.
          match Expr.toCoreAssignOpShiftRhsAware? storageNames env expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none =>
          -- #201 (G): a compound-assign whose LVALUE index KEY carries narrow
          -- checked arithmetic (`arr[a + b] += 1`, `uint8 a,b`) must lower the key
          -- env-aware (`Expr.toCoreLValueWithEnv?`, exactly as plain `=` does via
          -- `assignmentCoreWithEnv?`) so the operand-width Panic 0x11 fires BEFORE
          -- the slot is computed; `Expr.toCoreAssignOpWithEnv?` below lowers the
          -- lvalue env-LESS (key bare at 256 bits → read-modify-wrote arr[300]).
          -- Same `assignOpCleanupExpr` shape; only flagged index keys reroute.
          match (match expr with
            | Expr.assign lhs@(Expr.index _ key) op rhs =>
                if Expr.abiArgNeedsEnvCleanup? key then do
                  let coreOp ← AssignOp.toCoreBinary? op
                  let lhsCore ← Expr.toCoreLValueWithEnv? storageNames env lhs
                  let rhsCore ← Expr.toCore? storageNames rhs
                  let lhsTy ← Expr.abiTyWithEnv? env lhs
                  let cleanup ← Ty.toCoreValueCleanup? lhsTy
                  some
                    (SolidCore.Solidity.Source.Stmt.exprStmt
                      (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
                        lhsCore.toExpr coreOp rhsCore cleanup))
                else none
            | _ => none) with
          | some coreStmt => some coreStmt
          | none =>
          -- FB-COMPOUND: `bytesN |= / &= / ^=` bare-literal RHS must be lowered at
          -- the LValue's bytesN type (else a bare hex/string literal stays a
          -- byte-string value and the bitwise op Panics 0). Returns `none` for
          -- every non-bytesN LValue / non-bitwise op, preserving the paths below.
          match Expr.toCoreAssignOpBytesNBitwiseRhsAware? storageNames env expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none =>
          match Expr.toCoreAssignOpWithEnv? storageNames env expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none =>
              -- CALLPOS-REMAINDER Bug 1: the compound-assign RHS contains a user
              -- call (`total += fee()`, `m[k] += f()`, `x += t.g()`), which the
              -- env-aware pure lowering above cannot handle (`Expr.toCore? rhs` →
              -- `none` for any call), so it over-rejected. solc evaluates the RHS
              -- FIRST (verified via `--ir`: for `x += f()` and `m[k] += f()` the
              -- call `expr := f()` is emitted BEFORE the LValue `read`/index), so
              -- hoisting the call into a prefix statement and then lowering the
              -- read-modify-write through the SAME `assignOpCleanupExpr` path
              -- reproduces solc's order exactly AND preserves the LValue-width
              -- COMPOUND-CLEANUP (Panic 0x11 on narrow `+=`, truncating `<<=`),
              -- since the hoisted call result is fed as the (pure temp-read) RHS of
              -- the very same cleanup node. Only a single-user-call RHS the hoister
              -- can lower is accepted (internal via `internalExprSingleReturnUseCore?`,
              -- external/member via `externalCallSingleReturnCoreWithKindEnv?`); any
              -- shape either can't lower (multiple calls, deeper nesting, or a
              -- non-narrowable LValue) returns `none` and preserves the prior
              -- over-reject rather than emitting unsound code.
              match expr with
              | Expr.assign lhs op rhs =>
                  match
                    (do
                      let coreOp ← AssignOp.toCoreBinary? op
                      let lhsCore ←
                        Expr.toCoreLValueWithEnvCleanup? storageNames env lhs
                      let lhsTy ← Expr.abiTyWithEnv? env lhs
                      let cleanup ← Ty.toCoreValueCleanup? lhsTy
                      let useResult : CoreExpr -> CoreStmt := fun retExpr =>
                        SolidCore.Solidity.Source.Stmt.exprStmt
                          (SolidCore.Solidity.Source.Expr.assignOpCleanupExpr
                            lhsCore.toExpr coreOp retExpr cleanup)
                      match
                          FunctionDecl.internalExprSingleReturnUseCore?
                            internalFuel storageRefEnv env externalCallKindEnv
                            storageNames modifiers functions freeFunctions rhs
                            useResult with
                      | some coreStmt => some coreStmt
                      | none =>
                          match
                              Expr.externalMemberSingleReturnCallTy?
                                storageNames env externalCallKindEnv rhs with
                          | some rhsTy =>
                              Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                                storageNames env externalCallKindEnv rhsTy rhs
                                useResult
                          | none => none) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames (Stmt.expr expr)
              | _ => Stmt.toCore? storageNames (Stmt.expr expr)
      | Stmt.expr expr@(Expr.unary UnaryOp.delete target) =>
          -- #201 (G): `delete arr[a + b]` (`uint8 a,b`) — the env-less delete
          -- lowering ran the index key bare at 256 bits (zeroed arr[300], no
          -- Panic). Route a flagged narrow-arithmetic key through the env-aware
          -- lvalue lowering (`Expr.toCoreLValueWithEnv?`, the same helper plain
          -- assignment uses) so the operand-width Panic 0x11 fires before any
          -- write; every other delete keeps the env-less `Stmt.toCore?` path
          -- byte-identically.
          match (match target with
            | Expr.index _ key =>
                if Expr.abiArgNeedsEnvCleanup? key then
                  (Expr.toCoreLValueWithEnv? storageNames env target).map
                    SolidCore.Solidity.Source.Stmt.deleteValue
                else none
            | _ => none) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames (Stmt.expr expr)
      | Stmt.expr
          (Expr.assign (Expr.tuple lhsItems) AssignOp.assign
            (Expr.call (Expr.ident name) args)) =>
          let fallback :=
            Stmt.expr
              (Expr.assign (Expr.tuple lhsItems) AssignOp.assign
                (Expr.call (Expr.ident name) args))
          match TupleItems.toCoreLValueTargets? storageNames lhsItems with
          | some targets =>
              -- Pure LHS (no call-valued index): unchanged path.
              match FunctionDecl.internalTupleAssignReturnCallCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args targets with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames fallback
          | none =>
              -- TUP-IDX (direct-call RHS): an LHS component is indexed by an
              -- internal call — `(m[k()], arr[j()]) = two()`. The pure lvalue
              -- lowering above rejects the call index, so without this it fell
              -- through to the general ANF hoister, which evaluated the LHS index
              -- calls BEFORE the RHS call (wrong order). Hoist each LHS index call
              -- into a temp and thread it as `lhsPrefix` — spliced AFTER the RHS
              -- call is evaluated and captured — so solc's RHS-then-LHS-index order
              -- is reproduced (mirrors the tuple-LITERAL RHS arm below).
              match FunctionDecl.tupleLhsIndexCallHoistTargets?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions 0 lhsItems with
              | some (lhsPrefix, targets) =>
                  match FunctionDecl.internalTupleAssignReturnCallCore?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions name args targets
                      lhsPrefix with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
              | none => Stmt.toCore? storageNames fallback
      | Stmt.expr
          (Expr.assign (Expr.tuple lhsItems) AssignOp.assign
            (Expr.tuple rhsItems)) =>
          -- `array.push()` may be a tuple-assignment target.  Snapshot every RHS
          -- component first, then perform all push effects left-to-right, then
          -- assign from the temp reads.  This is solc's observable ordering and
          -- also ensures implicit destination-width conversion precedes pushes.
          match
              TupleItems.toCoreLValueTargetsWithDirectPush?
                storageNames lhsItems with
          | some (lhsPrefix, targets, true) => do
              let targetTys ←
                FunctionDecl.tupleAssignTargetTysWithDirectPush?
                  functions freeFunctions env lhsItems rhsItems
              FunctionDecl.tupleItemsUseCoreWithInternalCalls?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions "_sol_tuple_push_rhs"
                0 targetTys rhsItems
                (fun coreExprs =>
                  SolidCore.Solidity.Source.Stmt.block
                    (lhsPrefix ++
                      [ SolidCore.Solidity.Source.Stmt.assignTuple targets
                          (SolidCore.Solidity.Source.Expr.tuple coreExprs) ]))
          | _ =>
          -- Stage B (boundary-completion arc): tuple-literal RHS whose components
          -- contain internal calls — `(a, b) = (f(), g())`, `(, b) = (f(), g())`.
          -- solc evaluates the components LEFT-to-right, each into its own temp,
          -- ALL before any assignment, and a hole's component still evaluates
          -- (`docs/refs-completion-solc-research.md` §4). The no-call form keeps
          -- today's `Stmt.toCore?` path (tried first: behaviour-preserving); only
          -- shapes that path rejects (call components) reach the hoisting, which
          -- reuses `tupleItemsUseCoreWithInternalCalls?` — the same left-to-right
          -- temp sequencing already pinned for `return (f(), g())` — and assigns
          -- the temps via the ordinary `assignTuple` (pure temp reads, so store
          -- order is unobservable, matching solc's temps-then-stores shape).
          -- FB1: a `bytesN` width-EXPANDING op (`b << k` / `~b`) as a tuple RHS
          -- component must carry the same per-op `cleanup_t_bytesN` mask solc
          -- emits (and that the single-assign path emits via
          -- `assignmentCoreWithEnv?`). The env-LESS `Stmt.toCore?` path below has
          -- no per-component target type and drops the mask (wrong value, no
          -- revert). Reroute env-aware only when a mask is actually inserted;
          -- every other tuple assignment keeps the byte-identical path below.
          match (if TupleItems.anyAbiArgNeedsEnvCleanup rhsItems then do
              let targetTys ←
                FunctionDecl.tupleAssignTargetTysWithDirectPush?
                  functions freeFunctions env lhsItems rhsItems
              let targets ←
                TupleItems.toCoreLValueTargets? storageNames lhsItems
              FunctionDecl.tupleItemsUseCoreWithInternalCalls?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions "_sol_tuple_cleanup_rhs"
                0 targetTys rhsItems
                (fun coreExprs =>
                  SolidCore.Solidity.Source.Stmt.assignTuple
                    targets
                    (SolidCore.Solidity.Source.Expr.tuple coreExprs))
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match tupleAssignBitAwareCore? storageNames env lhsItems rhsItems with
          | some coreStmt => some coreStmt
          | none =>
          match
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.assign (Expr.tuple lhsItems) AssignOp.assign
                    (Expr.tuple rhsItems))) with
          | some coreStmt => some coreStmt
          | none =>
              if TupleItems.hasNestedTuple lhsItems then do
                -- R1 (residue-cleanup): NESTED LHS with an internal-call RHS —
                -- `((a, b), c) = (foo(), bar())` (`foo` returns a 2-tuple) or
                -- `((a, b), c) = ((foo(), bar()), baz())`. The flat `Stmt.toCore?`
                -- nested path (`tupleAssignmentCore?`) cannot hoist internal calls
                -- out of the RHS, so it over-rejected. Hoist every RHS leaf into a
                -- path-unique temp left-to-right (a multi-return call captured into
                -- per-return temps → a nested `Expr.tuple` value), preserving
                -- solc's temps-then-stores order, then destructure the temp-read
                -- tuple against the nested target tree with `assignTupleNested`.
                let targets ←
                  TupleItems.toCoreTupleTargets? storageNames lhsItems
                let (prefixStmts, replExprs) ←
                  FunctionDecl.nestedTupleRhsHoistList?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions "_sol_nested_tuple_item"
                    0 rhsItems
                some
                  (SolidCore.Solidity.Source.Stmt.block
                    (prefixStmts ++
                      [ SolidCore.Solidity.Source.Stmt.assignTupleNested targets
                          (SolidCore.Solidity.Source.Expr.tuple replExprs) ]))
              else do
                -- TUP-IDX: hoist internal calls out of any LHS-component INDEX
                -- (`(xs[f()], z) = …`, `(m[k()], z) = …`) into per-component temps;
                -- non-call-index components keep the pure `toCoreLValueTargets?`
                -- path unchanged. `lhsPrefix` binds the index-call temps and must
                -- run AFTER the RHS is evaluated (solc: RHS left-to-right, THEN LHS
                -- index expressions left-to-right).
                let (lhsPrefix, targets) ←
                  FunctionDecl.tupleLhsIndexCallHoistTargets?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions 0 lhsItems
                match Expr.toCore? storageNames (Expr.tuple rhsItems) with
                | some rhsCore =>
                    -- RHS is call-free (e.g. `(3, 4)`): it is pure, so evaluating
                    -- it inside `assignTuple` after the LHS index temps is order-
                    -- unobservable. Reached here only because an LHS index call made
                    -- the plain `Stmt.toCore?` fail.
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        (lhsPrefix ++
                          [ SolidCore.Solidity.Source.Stmt.assignTuple
                              targets rhsCore ]))
                | none => do
                    -- RHS itself contains internal calls (e.g. `(rhs(3), rhs(4))`,
                    -- possibly alongside call-valued LHS indices). Bind the RHS
                    -- components into temps LEFT-to-right first, THEN the LHS index
                    -- temps, THEN assign (temp reads only) — matching solc's order.
                    let componentTys ←
                      mapOption
                        (fun item =>
                          match item with
                          | TupleItem.value expr =>
                              Expr.abiTyWithInternalFunctionsEnv?
                                functions freeFunctions env expr
                          | TupleItem.hole => none)
                        rhsItems
                    FunctionDecl.tupleItemsUseCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions "_sol_tuple_assign_item"
                      0 componentTys rhsItems
                      (fun coreExprs =>
                        SolidCore.Solidity.Source.Stmt.block
                          (lhsPrefix ++
                            [ SolidCore.Solidity.Source.Stmt.assignTuple targets
                                (SolidCore.Solidity.Source.Expr.tuple coreExprs) ]))
      | Stmt.expr
          (Expr.assign (Expr.tuple lhsItems) AssignOp.assign expr) =>
          match Expr.lowLevelTupleAssignCore? storageNames env lhsItems expr with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.assign (Expr.tuple lhsItems) AssignOp.assign expr))
      | Stmt.expr
          (Expr.call
            (Expr.member (Expr.call (Expr.ident name) args) "push")
            memberArgs) =>
          match memberArgs with
          | [] =>
              match FunctionDecl.internalSingleStorageReturnRefCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args
                  (fun retName =>
                    SolidCore.Solidity.Source.Stmt.storageArrayPushRef
                      retName none) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.call (Expr.ident name) args) "push")
                        []))
          | [Arg.positional value] => do
              let retTys ←
                FunctionDecl.internalCalleeReturnTys?
                  functions freeFunctions env name args
              let elemTy ←
                match retTys with
                | [Ty.array elemTy _] => some elemTy
                | _ => none
              let valueCore ←
                Expr.toCoreAsWithEnv? storageNames env elemTy value
              match FunctionDecl.internalSingleStorageReturnRefCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args
                  (fun retName =>
                    SolidCore.Solidity.Source.Stmt.storageArrayPushRef
                      retName (some valueCore)) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call
                        (Expr.member (Expr.call (Expr.ident name) args) "push")
                        [Arg.positional value]))
          | _ =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.call (Expr.ident name) args) "push")
                    memberArgs))
      | Stmt.expr
          (Expr.call
            (Expr.member (Expr.call (Expr.ident name) args) "pop") []) =>
          match FunctionDecl.internalSingleStorageReturnRefCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retName =>
                SolidCore.Solidity.Source.Stmt.storageArrayPopRef retName) with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.call
                    (Expr.member (Expr.call (Expr.ident name) args) "pop") []))
      | Stmt.expr
          (Expr.assign
            (Expr.index (Expr.call (Expr.ident name) args) index)
            AssignOp.assign rhs) => do
          let retTys ←
            FunctionDecl.internalCalleeReturnTys?
              functions freeFunctions env name args
          let elemTy ←
            match retTys with
            | [Ty.array elemTy _] => some elemTy
            | _ => none
          let indexCore ←
            if Expr.abiArgNeedsEnvCleanup? index then do
              let indexTy ← Expr.abiTyWithEnv? env index
              Expr.toCoreAsWithEnv? storageNames env indexTy index
            else
              Expr.toCore? storageNames index
          let rhsCore ←
            Expr.toCoreAsWithEnv? storageNames env elemTy rhs
          match FunctionDecl.internalSingleStorageReturnRefCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retName =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.index
                    (SolidCore.Solidity.Source.LValue.var retName)
                    indexCore)
                  rhsCore) with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.assign
                    (Expr.index (Expr.call (Expr.ident name) args) index)
                    AssignOp.assign rhs))
      -- LIB-STORAGE-RETURN-USE (#156), READ side: `return L.ref(s).x` — after the
      -- struct-member→index rewrite (in `expandUsing`) this is
      -- `return <call>[index]` where the call value-returns a `storage` reference.
      -- Capture the returned pointer into the storage-ref temp (the SAME machinery
      -- the index-ASSIGN arm above uses) and read the indexed sub-path off it as the
      -- return value. `internalSingleStorageReturnRefCore?` declines any callee whose
      -- single return is not a storage ref, so non-storage-return calls fall through
      -- to the ordinary return lowering unchanged.
      | Stmt.returnValues
          (some (Expr.index (Expr.call (Expr.ident name) args) index)) =>
          match
            (do
              if FunctionDecl.callSiteReturnsSingleStorageRef?
                  functions freeFunctions env name args then
                some ()
              else
                none
              let indexCore ←
                Expr.abiArgCoreWithEnvCleanup? storageNames env index
              FunctionDecl.internalSingleStorageReturnRefCore?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions name args
                (fun retName =>
                  SolidCore.Solidity.Source.Stmt.returnValues
                    [SolidCore.Solidity.Source.Expr.index
                      (SolidCore.Solidity.Source.Expr.var retName) indexCore])) with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.returnValues
                  (some (Expr.index (Expr.call (Expr.ident name) args) index)))
      | Stmt.expr expr@(Expr.call (Expr.member _ _) _) =>
          -- LIB-STORAGE-RETURN-USE, ARRAY-FIELD push/pop: `L.ref(s).a.push(v)` /
          -- `.push()` / `.pop()` — after the struct-member→index rewrite the
          -- receiver is an index spine rooted at a call value-returning a
          -- `storage` reference (`<call>[fieldIndex]…`). Capture the returned
          -- pointer into the storage-ref temp (the SAME machinery the
          -- direct-call push/pop and index-ASSIGN arms above use) and push/pop
          -- through the indexed sub-path off it
          -- (`storageArrayPushRefPath`/`storageArrayPopRefPath` — the runtime
          -- shape already pinned for storage-ref LOCALS: `S storage p;
          -- p.a.push(v)`). `internalSingleStorageReturnRefCore?` declines any
          -- callee whose single return is not a storage ref (e.g. a MEMORY
          -- struct return, whose array field solc also rejects push/pop on),
          -- and a non-call-rooted receiver yields no spine — both fall through
          -- to the pre-existing chain below unchanged.
          match (match expr with
                 | Expr.call (Expr.member receiver "push") [] => do
                     let (name, args, indexes) ←
                       Expr.callRootedIndexSpine? receiver
                     let indexCores ←
                       mapOption
                         (Expr.abiArgCoreWithEnvCleanup? storageNames env) indexes
                     FunctionDecl.internalSingleStorageReturnRefCore?
                       internalFuel storageRefEnv env externalCallKindEnv
                       storageNames modifiers functions freeFunctions name args
                       (fun retName =>
                         SolidCore.Solidity.Source.Stmt.storageArrayPushRefPath
                           retName indexCores none)
                 | Expr.call (Expr.member receiver "push")
                     [Arg.positional value] => do
                     let (name, args, indexes) ←
                       Expr.callRootedIndexSpine? receiver
                     let indexCores ←
                       mapOption
                         (Expr.abiArgCoreWithEnvCleanup? storageNames env) indexes
                     -- NARROW-PUSH (#183) through the returned ref: lower the
                     -- pushed value against the array ELEMENT type recovered
                     -- from the callee's return type down the index spine, so
                     -- a narrow checked-arithmetic argument keeps its
                     -- operand-width cleanup (Panic 0x11 on overflow). If the
                     -- element type cannot be recovered, decline — keeping the
                     -- prior over-reject rather than silently wrapping.
                     let retTys ←
                       FunctionDecl.internalCalleeReturnTys?
                         functions freeFunctions env name args
                     let retTy ←
                       match retTys with
                       | [ty] => some ty
                       | _ => none
                     let elemTy ←
                       match Ty.peelIndexSpineTy? retTy indexes with
                       | some (Ty.array elemTy _) => some elemTy
                       | _ => none
                     let valueCore ←
                       match
                           Expr.toCoreAsWithEnv? storageNames env elemTy
                             value with
                       | some c => some c
                       | none => Expr.toCore? storageNames value
                     FunctionDecl.internalSingleStorageReturnRefCore?
                       internalFuel storageRefEnv env externalCallKindEnv
                       storageNames modifiers functions freeFunctions name args
                       (fun retName =>
                         SolidCore.Solidity.Source.Stmt.storageArrayPushRefPath
                           retName indexCores (some valueCore))
                 | Expr.call (Expr.member receiver "pop") [] => do
                     let (name, args, indexes) ←
                       Expr.callRootedIndexSpine? receiver
                     let indexCores ←
                       mapOption (Expr.toCore? storageNames) indexes
                     FunctionDecl.internalSingleStorageReturnRefCore?
                       internalFuel storageRefEnv env externalCallKindEnv
                       storageNames modifiers functions freeFunctions name args
                       (fun retName =>
                         SolidCore.Solidity.Source.Stmt.storageArrayPopRefPath
                           retName indexCores)
                 | _ => none) with
          | some coreStmt => some coreStmt
          | none =>
          -- NARROW-PUSH (#183): a state-variable array push with a value argument
          -- must lower that value against the array ELEMENT type (env-aware, so
          -- narrow checked arithmetic Panics 0x11 on overflow). The env-less
          -- `Stmt.toCore?` below would succeed FIRST via `storageArrayPushPathCore?`
          -- and silently drop the operand-width cleanup, so intercept it here.
          match (match expr with
                 | Expr.call (Expr.member target "push") [] =>
                     storageArrayEmptyPushPathCoreWithEnv?
                       env storageNames target
                 | Expr.call (Expr.member target "push") [Arg.positional value] =>
                     storageArrayPushPathCoreWithEnv? env storageNames target value
                 | Expr.call (Expr.member target "pop") [] => do
                     let (name, indexes) ←
                       Expr.storagePathCoreWithEnv? storageNames env target
                     match indexes with
                     | [] =>
                         some
                           (SolidCore.Solidity.Source.Stmt.storageArrayPop name)
                     | _ =>
                         some
                           (SolidCore.Solidity.Source.Stmt.storageArrayPopPath
                             name indexes)
                 | _ => none) with
          | some coreStmt => some coreStmt
          | none =>
          match (if Expr.abiArgNeedsEnvCleanup? expr then do
              let ty ← Expr.abiTyWithEnv? env expr
              let coreExpr ← Expr.toCoreAsWithEnv? storageNames env ty expr
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match Stmt.toCore? storageNames (Stmt.expr expr) with
          | some coreStmt => some coreStmt
          | none =>
              match Expr.localStorageArrayMemberStmtCore?
                  storageRefEnv env storageNames expr with
              | some coreStmt => some coreStmt
              | none =>
                  match
                      Expr.externalCallDiscardCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                        storageNames env externalCallKindEnv expr with
                  | some coreStmt => some coreStmt
                  | none =>
                      -- CALLPOS-REMAINDER Bug 2: storage-array `.push(<call>)` whose
                      -- ARGUMENT is a user call (`xs.push(f())`, `xs.push(t.g())`).
                      -- The pure push path (`localStorageArrayMemberStmtCore?`)
                      -- cannot lower a call argument, so it over-rejected. solc
                      -- evaluates the push argument, then pushes; hoist the call
                      -- into a prefix statement and push the (pure temp-read)
                      -- result through the SAME `storageArrayPushRef` path. Scope:
                      -- only a DIRECT storage array (`indexes = []`, i.e. the
                      -- receiver path reads no dynamic index) — for a receiver whose
                      -- path itself has dynamic indexes (`nested[k].push(f())`) solc
                      -- computes the receiver slot BEFORE evaluating the argument
                      -- (verified via `--ir`: `xs.push`'s self-slot is emitted
                      -- before `f()`), which a call-first hoist would reorder, so
                      -- those return `none` and keep the prior over-reject.
                      match expr with
                      | Expr.call (Expr.member target "push")
                          [Arg.positional value] =>
                          let directStatePush? := do
                            let (name, indexes) ←
                              Expr.storagePathCoreWithEnv? storageNames env target
                            let elemTy ←
                              match Expr.abiTyWithEnv? env target with
                              | some (Ty.array elemTy _) => some elemTy
                              | _ => none
                            match indexes with
                            | [] =>
                                let mkPush : CoreExpr -> CoreStmt := fun valueCore =>
                                  SolidCore.Solidity.Source.Stmt.storageArrayPush name
                                    (some (Ty.implicitCleanupCore elemTy valueCore))
                                FunctionDecl.internalExprSingleReturnUseCore?
                                  internalFuel storageRefEnv env
                                  externalCallKindEnv storageNames modifiers
                                  functions freeFunctions value mkPush
                            | _ => none
                          match directStatePush? with
                          | some coreStmt => some coreStmt
                          | none =>
                            (do
                              let (source, indexes) ←
                                Expr.storageRefPathCore? storageRefEnv storageNames
                                  target
                              match target with
                              | Expr.ident name => do
                                  let ty ← TypeEnv.lookup? env name
                                  if Ty.hasStorageArrayMembers ty then some ()
                                  else none
                              | _ => some ()
                              match indexes with
                              | [] =>
                                  let mkPush : CoreExpr -> CoreStmt := fun valueCore =>
                                    SolidCore.Solidity.Source.Stmt.storageArrayPushRef
                                      source (some valueCore)
                                  match
                                      FunctionDecl.internalExprSingleReturnUseCore?
                                        internalFuel storageRefEnv env
                                        externalCallKindEnv storageNames modifiers
                                        functions freeFunctions value mkPush with
                                  | some coreStmt => some coreStmt
                                  | none =>
                                      match
                                          Expr.externalMemberSingleReturnCallTy?
                                            storageNames env externalCallKindEnv
                                            value with
                                      | some vTy =>
                                          Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                                            storageNames env externalCallKindEnv vTy
                                            value mkPush
                                      | none => none
                              | _ => none)
                      -- ABI-ENCODE-INTERNAL-CALL-ARG (#174), discard position:
                      -- `abi.encode(g());` as a bare expression statement. The
                      -- env-less `Stmt.toCore?` above cannot lower the nested
                      -- internal call; peel it into a prefix temp via the generic
                      -- argument-position hoister and re-lower the residual
                      -- `abi.encode((retTy)(_tmp))` (which then hits the env-less
                      -- lowering cleanly). Only fires when a nested call is found.
                      | Expr.call (Expr.member (Expr.ident "abi") _) _ =>
                          Stmt.argPositionHoist? internalFuel storageRefEnv env
                            externalCallKindEnv storageNames modifiers functions
                            freeFunctions returnTys expr (fun e => Stmt.expr e)
                      | _ => none
      | Stmt.expr expr@(Expr.callWithOptions (Expr.member _ _) _ _) =>
          match Stmt.toCore? storageNames (Stmt.expr expr) with
          | some coreStmt => some coreStmt
          | none =>
              Expr.externalCallDiscardCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                storageNames env externalCallKindEnv expr
      | Stmt.expr
          (Expr.call (Expr.ident "assert")
            [Arg.positional (Expr.call (Expr.ident name) args)]) =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assertStmt retExpr) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr
                (Expr.call (Expr.ident "assert")
                  [Arg.positional (Expr.call (Expr.ident name) args)]))
      | Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional cond]) =>
          -- R2 (Stage C): a NON-call assert condition routes through the same
          -- env-aware condition lowering as `require` (operand-width cleanup, so
          -- `assert((a + b) < n)` with `uint8 a,b` Panics 0x11 on the overflow
          -- BEFORE the assert check — previously this fell to the generic
          -- ident-call statement arm and the env-less `Stmt.toCore?`, dropping
          -- the cleanup). Call conditions matched the arm above; on `none` the
          -- prior generic fallbacks are preserved verbatim.
          (match FunctionDecl.conditionUseCoreWithInternalCalls?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions cond
              (fun condCore =>
                SolidCore.Solidity.Source.Stmt.assertStmt condCore) with
          | some coreStmt => some coreStmt
          | none =>
              match
                  Stmt.argPositionHoist? internalFuel storageRefEnv env
                    externalCallKindEnv storageNames modifiers functions
                    freeFunctions returnTys
                    (Expr.call (Expr.ident "assert") [Arg.positional cond])
                    (fun e => Stmt.expr e) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call (Expr.ident "assert") [Arg.positional cond])))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional (Expr.call (Expr.ident name) args)]) =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.requireStmt retExpr none) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr
                (Expr.call (Expr.ident "require")
                  [Arg.positional (Expr.call (Expr.ident name) args)]))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional (Expr.call (Expr.ident name) args)
            , Arg.positional (Expr.literal (Literal.string reason)) ]) =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.requireStmt
                  retExpr (some reason)) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames
              (Stmt.expr
                (Expr.call (Expr.ident "require")
                  [ Arg.positional (Expr.call (Expr.ident name) args)
                  , Arg.positional (Expr.literal (Literal.string reason)) ]))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond]) =>
          FunctionDecl.conditionUseCoreWithInternalCalls?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions cond
            (fun condCore =>
              SolidCore.Solidity.Source.Stmt.requireStmt condCore none)
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional cond
            , Arg.positional (Expr.literal (Literal.string reason)) ]) =>
          FunctionDecl.conditionUseCoreWithInternalCalls?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions cond
            (fun condCore =>
              SolidCore.Solidity.Source.Stmt.requireStmt
                condCore (some reason))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional (Expr.call (Expr.ident name) args)
            , Arg.positional
                (Expr.call (Expr.ident errorName)
                  [Arg.positional (Expr.call (Expr.ident valueName) valueArgs)]) ]) =>
          match FunctionDecl.internalTwoSingleReturnCallsCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args valueName valueArgs
              "_sol_require_cond"
              (fun condExpr valueExpr =>
                SolidCore.Solidity.Source.Stmt.requireCustom
                  condExpr errorName [valueExpr]) with
          | some coreStmt => some coreStmt
          | none => do
              let valueCore ←
                Expr.toCore? storageNames
                  (Expr.call (Expr.ident valueName) valueArgs)
              match FunctionDecl.internalSingleReturnCallCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.requireCustom
                      retExpr errorName [valueCore]) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call (Expr.ident "require")
                        [ Arg.positional (Expr.call (Expr.ident name) args)
                        , Arg.positional
                            (Expr.call (Expr.ident errorName)
                              [Arg.positional
                                (Expr.call (Expr.ident valueName) valueArgs)]) ]))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional (Expr.call (Expr.ident name) args)
            , Arg.positional (Expr.call (Expr.ident errorName) errorArgs) ]) => do
          match FunctionDecl.internalTwoSingleReturnCallsCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args errorName errorArgs
              "_sol_require_cond"
              (fun condExpr reasonExpr =>
                SolidCore.Solidity.Source.Stmt.requireErrorExpr
                  condExpr reasonExpr) with
          | some coreStmt => some coreStmt
          | none => do
              let coreArgs ← Args.toCoreExprs? storageNames errorArgs
              match FunctionDecl.internalSingleReturnCallCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.requireCustom
                      retExpr errorName coreArgs) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call (Expr.ident "require")
                        [ Arg.positional (Expr.call (Expr.ident name) args)
                        , Arg.positional
                            (Expr.call (Expr.ident errorName) errorArgs) ]))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional (Expr.call (Expr.ident name) args)
            , Arg.positional reason ]) => do
          let reasonCore ← Expr.toCore? storageNames reason
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.requireErrorExpr
                  retExpr reasonCore) with
          | some coreStmt => some coreStmt
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.call (Expr.ident "require")
                    [ Arg.positional (Expr.call (Expr.ident name) args)
                    , Arg.positional reason ]))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [ Arg.positional cond
            , Arg.positional
                (Expr.call (Expr.ident errorName)
                  [Arg.positional (Expr.call (Expr.ident name) args)]) ]) => do
          let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
          let condTmp := "_sol_require_cond"
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.requireCustom
                  (SolidCore.Solidity.Source.Expr.var condTmp)
                  errorName [retExpr]) with
          | some coreStmt =>
              some
                (SolidCore.Solidity.Source.Stmt.block
                  [ SolidCore.Solidity.Source.Stmt.varDecl
                      SolidCore.Solidity.Source.Ty.bool condTmp
                      (some condCore)
                  , coreStmt ])
          | none =>
              Stmt.toCore? storageNames
                (Stmt.expr
                  (Expr.call (Expr.ident "require")
                    [ Arg.positional cond
                    , Arg.positional
                        (Expr.call (Expr.ident errorName)
                          [Arg.positional
                            (Expr.call (Expr.ident name) args)]) ]))
      | Stmt.expr expr@(
          Expr.call (Expr.ident "require")
            [ Arg.positional cond
            , Arg.positional (Expr.call (Expr.ident name) args) ]) =>
          match Expr.requireCustomWithEnvCleanup? storageNames env expr with
          | some coreStmt => some coreStmt
          | none =>
              do
                let condCore ← Expr.conditionCoreWithEnv? storageNames env cond
                let condTmp := "_sol_require_cond"
                match FunctionDecl.internalSingleReturnCallCore?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions name args
                    (fun retExpr =>
                      SolidCore.Solidity.Source.Stmt.requireErrorExpr
                        (SolidCore.Solidity.Source.Expr.var condTmp) retExpr) with
                | some coreStmt =>
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        [ SolidCore.Solidity.Source.Stmt.varDecl
                            SolidCore.Solidity.Source.Ty.bool condTmp
                            (some condCore)
                        , coreStmt ])
                | none =>
                    Stmt.toCore? storageNames
                      (Stmt.expr
                        (Expr.call (Expr.ident "require")
                          [ Arg.positional cond
                          , Arg.positional (Expr.call (Expr.ident name) args) ]))
      -- NOTE: the earlier specialized `f(first, g())` call-statement arm (which
      -- hoisted ONLY the second argument and failed when `first` was itself a call,
      -- e.g. `f(g(), h());`) was removed — the general `Expr.call (Expr.ident name)
      -- args` arm below now hoists EVERY direct-call argument via
      -- `hoistDirectInternalCallArgs?`, subsuming it.
      | Stmt.expr expr@(Expr.call (Expr.ident name) args) =>
          let argHoist? : Option CoreStmt :=
            Stmt.argPositionHoist? internalFuel storageRefEnv env
              externalCallKindEnv storageNames modifiers functions
              freeFunctions returnTys (Expr.call (Expr.ident name) args)
              (fun e => Stmt.expr e)
          let builtinEnvAware? : Option CoreStmt :=
            match name, args with
            | "require",
                [ Arg.positional cond
                , Arg.positional
                    (Expr.call
                      (Expr.member (Expr.typeName (Ty.user _)) errorName)
                      errorArgs) ] => do
                -- A qualified custom error still uses the unqualified error
                -- name in its selector.  Keep this shape ahead of the generic
                -- env-aware `require(cond, reason)` lowering, which otherwise
                -- preserves the source qualifier in `requireErrorExpr` and
                -- changes the observable error name.
                let condCore ←
                  Expr.conditionCoreWithEnv? storageNames env cond
                let coreArgs ←
                  if Args.anyAbiArgNeedsEnvCleanup errorArgs then
                    Args.toCoreExprsWithEnvCleanup?
                      storageNames env errorArgs
                  else
                    Args.toCoreExprs? storageNames errorArgs
                some
                  (SolidCore.Solidity.Source.Stmt.requireCustom
                    condCore errorName coreArgs)
            | "require", [Arg.positional cond, Arg.positional reason] =>
                if Expr.abiArgNeedsEnvCleanup? cond ||
                    Expr.abiArgNeedsEnvCleanup? reason then do
                  -- Both arguments are evaluated eagerly, left-to-right. Keep
                  -- narrow arithmetic under a dynamic reason expression (for
                  -- example `string(abi.encode(a + b))`) at its source width
                  -- before `require` consumes it.
                  let condCore ←
                    Expr.toCoreAsWithEnv?
                      storageNames env Ty.bool cond
                  let reasonTy ← Expr.abiTyWithEnv? env reason
                  let reasonCore ←
                    Expr.toCoreAsWithEnv?
                      storageNames env reasonTy reason
                  some
                    (SolidCore.Solidity.Source.Stmt.requireErrorExpr
                      condCore reasonCore)
                else none
            | "selfdestruct", [Arg.positional recipient] =>
                if Expr.abiArgNeedsEnvCleanup? recipient then do
                  let recipientTy ← Expr.abiTyWithEnv? env recipient
                  let recipientCore ←
                    Expr.toCoreAsWithEnv?
                      storageNames env recipientTy recipient
                  some
                    (SolidCore.Solidity.Source.Stmt.selfdestruct recipientCore)
                else none
            | "revert", [Arg.positional reason] =>
                if Expr.abiArgNeedsEnvCleanup? reason then do
                  let reasonTy ← Expr.abiTyWithEnv? env reason
                  let reasonCore ←
                    Expr.toCoreAsWithEnv?
                      storageNames env reasonTy reason
                  some
                    (SolidCore.Solidity.Source.Stmt.revertErrorExpr reasonCore)
                else none
            | _, _ => none
          let fallback? :=
            match builtinEnvAware? with
            | some coreStmt => some coreStmt
            | none =>
            match (if Expr.abiArgNeedsEnvCleanup? expr then do
                let ty ← Expr.abiTyWithEnv? env expr
                let coreExpr ← Expr.toCoreAsWithEnv? storageNames env ty expr
                some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
              else none) with
            | some coreStmt => some coreStmt
            | none =>
            match Expr.externalFunctionValueCallDiscardCore? storageNames env expr with
            | some coreStmt => some coreStmt
            | none =>
                match FunctionDecl.internalStatementCallCore?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions name args with
                | some coreStmt => some coreStmt
                | none =>
                    match argHoist? with
                    | some coreStmt => some coreStmt
                    | none => Stmt.toCore? storageNames
                        (Stmt.expr (Expr.call (Expr.ident name) args))
          match FunctionDecl.hoistDirectInternalCallArgsForCallee?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions "_sol_call_arg" name args with
          | some (prefixPieces, tempEnv, replacedArgs) =>
              (match FunctionDecl.internalStatementCallCore?
                  internalFuel storageRefEnv (tempEnv ++ env) externalCallKindEnv
                  storageNames modifiers functions freeFunctions
                  name replacedArgs with
              | some callCore =>
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      (prefixPieces ++ [callCore]))
              | none => fallback?)
          | none => fallback?
      | Stmt.expr
          (Expr.call (Expr.typeName targetTy) [Arg.positional inner]) =>
          match FunctionDecl.internalTypeConversionSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions targetTy inner
              (fun _ => SolidCore.Solidity.Source.Stmt.skip) with
          | some coreStmt => some coreStmt
          | none =>
              match (if Expr.abiArgNeedsEnvCleanup? inner then do
                  let coreExpr ←
                    Expr.toCoreAsWithEnv? storageNames env targetTy
                      (Expr.call (Expr.typeName targetTy)
                        [Arg.positional inner])
                  some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
                else none) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.expr
                      (Expr.call (Expr.typeName targetTy)
                        [Arg.positional inner]))
      | Stmt.expr expr@(Expr.callWithOptions (Expr.ident _) _ _) =>
          match Expr.externalFunctionValueCallDiscardCore? storageNames env expr with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames (Stmt.expr expr)
      | Stmt.expr expr@(Expr.newExpr _ _) =>
          match
            Expr.toContractCreationCoreWithKindEnv?
              storageNames externalCallKindEnv expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none =>
              match
                  Stmt.argPositionHoist? internalFuel storageRefEnv env
                    externalCallKindEnv storageNames modifiers functions
                    freeFunctions returnTys expr (fun e => Stmt.expr e) with
              | some coreStmt => some coreStmt
              | none =>
                  match (if Expr.abiArgNeedsEnvCleanup? expr then do
                      let ty ← Expr.abiTyWithEnv? env expr
                      let coreExpr ←
                        Expr.toCoreAsWithEnv? storageNames env ty expr
                      some
                        (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
                    else none) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames (Stmt.expr expr)
      | Stmt.expr expr@(Expr.callWithOptions (Expr.newExpr _ []) _ _) =>
          match
            Expr.toContractCreationCoreWithKindEnv?
              storageNames externalCallKindEnv expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none => Stmt.toCore? storageNames (Stmt.expr expr)
      | Stmt.expr
          (Expr.assign
            (Expr.index base (Expr.call (Expr.ident iname) iargs))
            AssignOp.assign rhs) =>
          -- MI1: an INTERNAL function-call result used as a mapping/array INDEX in
          -- the assignment target `base[idu8(k)] = rhs`. The plain LValue lowering
          -- (`Expr.toCoreLValue?`) has no internal-call fallback for the index
          -- operand, so this used to over-reject at Executable lowering. Hoist the
          -- index call into a temp and thread the temp through the LValue. solc
          -- evaluates the RHS before the LHS index (verified: `m[idx()] = val()`
          -- runs val() first), so the RHS is bound to a temp *before* the hoisted
          -- index call. When the index is not an internal call this pattern still
          -- matches but the hoist returns `none`, so we fall back to the ordinary
          -- lowering — no behaviour change for non-internal-call indices.
          let original :=
            Stmt.expr
              (Expr.assign
                (Expr.index base (Expr.call (Expr.ident iname) iargs))
                AssignOp.assign rhs)
          match
              (do
                let targetTy ←
                  Expr.abiTyWithEnv? env
                    (Expr.index base (Expr.call (Expr.ident iname) iargs))
                let targetCoreTy ← Ty.toCore? targetTy
                let rhsCore ← Expr.toCoreAsWithEnv? storageNames env targetTy rhs
                let baseLV ← Expr.toCoreLValueWithEnvCleanup? storageNames env base
                let buildLV := fun idx =>
                  SolidCore.Solidity.Source.LValue.index baseLV idx
                let hoisted ←
                  FunctionDecl.internalSingleReturnCallCore?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions iname iargs
                    (fun idxCore =>
                      SolidCore.Solidity.Source.Stmt.assign (buildLV idxCore)
                        (SolidCore.Solidity.Source.Expr.var indexAssignRhsTempName))
                some
                  (SolidCore.Solidity.Source.Stmt.block
                    [ SolidCore.Solidity.Source.Stmt.varDecl
                        targetCoreTy indexAssignRhsTempName (some rhsCore)
                    , hoisted ])) with
          | some coreStmt => some coreStmt
          | none =>
              -- OVERREJECT-CALLPOS-BATCH (E): `m[f()] = g()` — the RHS is ITSELF a
              -- call-position shape, so the pure RHS lowering (`toCoreAsWithEnv?`)
              -- above fails. solc evaluates the RHS FIRST, then the index (verified
              -- via `--ir`: `m[f()] = g()` runs g() before f()). Declare the RHS
              -- temp uninitialised, hoist the RHS call into it, THEN hoist the index
              -- call — preserving RHS-before-index order. Any RHS the hoister cannot
              -- lower leaves this `none`, preserving the prior over-reject.
              match
                  (do
                    let targetTy ←
                      Expr.abiTyWithEnv? env
                        (Expr.index base (Expr.call (Expr.ident iname) iargs))
                    let targetCoreTy ← Ty.toCore? targetTy
                    let baseLV ←
                      Expr.toCoreLValueWithEnvCleanup? storageNames env base
                    let buildLV := fun idx =>
                      SolidCore.Solidity.Source.LValue.index baseLV idx
                    let indexHoist ←
                      FunctionDecl.internalSingleReturnCallCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions iname iargs
                        (fun idxCore =>
                          SolidCore.Solidity.Source.Stmt.assign (buildLV idxCore)
                            (SolidCore.Solidity.Source.Expr.var
                              indexAssignRhsTempName))
                    let rhsHoist ←
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions rhs
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var
                              indexAssignRhsTempName)
                            (Ty.implicitCleanupCore targetTy resultExpr))
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        [ SolidCore.Solidity.Source.Stmt.varDecl
                            targetCoreTy indexAssignRhsTempName none
                        , rhsHoist
                        , indexHoist ])) with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames original
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.call (Expr.member _ _) _)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs,
              Expr.abiTyWithEnv? env lhs with
          | some lhsCore, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign lhsCore retExpr) with
              | some coreStmt => some coreStmt
              | none =>
                  -- #201 (A): a MEMBER-call RHS that is an abi/concat builtin with
                  -- a flagged argument (`z = abi.encode(a + b)`,
                  -- `z = bytes.concat(bytes1(a + b))`, `s = abi.encodePacked(a+b)`)
                  -- is not an external call, so the chain above declines; route it
                  -- through `assignmentCoreWithEnv?` exactly as the IDENT-call
                  -- assignment arm below already does, so the env-aware `abi.*`/
                  -- concat arms fire the operand-width Panic 0x11. Unflagged
                  -- member-call assigns keep the env-less fallback byte-identically.
                  match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
                      assignmentCoreWithEnv? storageNames env lhs expr
                    else none) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames
                      (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs,
              Expr.abiTyWithEnv? env lhs with
          | some lhsCore, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign lhsCore retExpr) with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames
                  (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.call (Expr.ident name) args)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs with
          | some lhsCore =>
              let lhsTy? := Expr.abiTyWithEnv? env lhs
              match Expr.externalFunctionValueCallSingleReturnCore?
                  storageNames env expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign lhsCore
                      (match lhsTy? with
                      | some lhsTy => Ty.implicitCleanupCore lhsTy retExpr
                      | none => retExpr)) with
              | some coreStmt => some coreStmt
              | none =>
                  -- Use the expression-aware call lowerer here: an assignment
                  -- RHS such as `fold(result, keccak256(11))` may contain a
                  -- nested user-defined call (even one whose name collides
                  -- with a builtin). The direct helper leaves that argument
                  -- to the env-less builtin path; the expression helper
                  -- hoists and resolves it against the actual declarations.
                  match FunctionDecl.internalSingleReturnCallExprCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions expr
                      (fun retExpr =>
                        SolidCore.Solidity.Source.Stmt.assign lhsCore
                          (match lhsTy? with
                          | some lhsTy => Ty.implicitCleanupCore lhsTy retExpr
                          | none => retExpr)) with
                  | some coreStmt => some coreStmt
                  | none =>
                      match assignmentCoreWithEnv? storageNames env lhs
                          (Expr.call (Expr.ident name) args) with
                      | some coreStmt => some coreStmt
                      | none => Stmt.toCore? storageNames
                          (Stmt.expr
                            (Expr.assign lhs AssignOp.assign
                              (Expr.call (Expr.ident name) args)))
          | none => Stmt.toCore? storageNames
              (Stmt.expr
                (Expr.assign lhs AssignOp.assign
                  (Expr.call (Expr.ident name) args)))
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.callWithOptions (Expr.ident _) _ _)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs with
          | some lhsCore =>
              let lhsTy? := Expr.abiTyWithEnv? env lhs
              match Expr.externalFunctionValueCallSingleReturnCore?
                  storageNames env expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign lhsCore
                      (match lhsTy? with
                      | some lhsTy => Ty.implicitCleanupCore lhsTy retExpr
                      | none => retExpr)) with
              | some coreStmt => some coreStmt
              | none =>
                  match assignmentCoreWithEnv? storageNames env lhs expr with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames
                      (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
          | none => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.newExpr _ _)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs with
          | some lhsCore =>
              match
                Expr.toContractCreationCoreWithKindEnv?
                  storageNames externalCallKindEnv expr with
              | some coreExpr =>
                  some (SolidCore.Solidity.Source.Stmt.assign lhsCore coreExpr)
              | none => Stmt.toCore? storageNames
                  (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
          | none => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | Stmt.expr (Expr.assign lhs AssignOp.assign
          expr@(Expr.callWithOptions (Expr.newExpr _ []) _ _)) =>
          match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs with
          | some lhsCore =>
              match
                Expr.toContractCreationCoreWithKindEnv?
                  storageNames externalCallKindEnv expr with
              | some coreExpr =>
                  some (SolidCore.Solidity.Source.Stmt.assign lhsCore coreExpr)
              | none => Stmt.toCore? storageNames
                  (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
          | none => Stmt.toCore? storageNames
              (Stmt.expr (Expr.assign lhs AssignOp.assign expr))
      | Stmt.expr
          (Expr.assign target AssignOp.assign
            (Expr.ternary cond thenExpr elseExpr)) =>
          let fallback :=
            Stmt.expr
              (Expr.assign target AssignOp.assign
                (Expr.ternary cond thenExpr elseExpr))
          match Expr.toCoreLValueWithEnvCleanup? storageNames env target with
          | some targetCore =>
              let targetTy? := Expr.abiTyWithEnv? env target
              let conditionBranchAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          targetCore branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions thenExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            targetCore
                            (Ty.implicitCleanupCore targetTy resultExpr))
                let elseCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          targetCore branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions elseExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            targetCore
                            (Ty.implicitCleanupCore targetTy resultExpr))
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      condCore thenCore elseCore)
              let conditionAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr
                let elseCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.assign
                      targetCore
                      (SolidCore.Solidity.Source.Expr.ternary
                        condCore thenCore elseCore))
              match conditionBranchAssign? with
              | some coreStmt => some coreStmt
              | none =>
                match conditionAssign? with
                | some coreStmt => some coreStmt
                | none =>
                  match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond thenExpr elseExpr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      targetCore
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
                  | some coreStmt => some coreStmt
                  | none =>
                      match FunctionDecl.internalTernaryBranchSingleReturnUseCore?
                          internalFuel storageRefEnv env externalCallKindEnv storageNames
                          modifiers functions freeFunctions cond thenExpr elseExpr
                          (fun resultExpr =>
                            SolidCore.Solidity.Source.Stmt.assign
                              targetCore
                              (match targetTy? with
                              | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                              | none => resultExpr)) with
                      | some coreStmt => some coreStmt
                      | none =>
                          match assignmentCoreWithEnv? storageNames env target
                              (Expr.ternary cond thenExpr elseExpr) with
                          | some coreStmt => some coreStmt
                          | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.expr
          (Expr.assign target AssignOp.assign
            (Expr.unary op expr)) =>
          let fallback :=
            Stmt.expr
              (Expr.assign target AssignOp.assign
                (Expr.unary op expr))
          match Expr.toCoreLValueWithEnvCleanup? storageNames env target with
          | some targetCore =>
              let targetTy? := Expr.abiTyWithEnv? env target
              match FunctionDecl.internalUnarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op expr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      targetCore
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some coreStmt => some coreStmt
              | none =>
                  match assignmentCoreWithEnv? storageNames env target
                      (Expr.unary op expr) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.expr
          (Expr.assign target AssignOp.assign
            (Expr.call (Expr.typeName targetTy)
              [Arg.positional inner])) =>
          let fallback :=
            Stmt.expr
              (Expr.assign target AssignOp.assign
                (Expr.call (Expr.typeName targetTy)
                  [Arg.positional inner]))
          match Expr.toCoreLValueWithEnvCleanup? storageNames env target with
          | some targetCore =>
              let targetTy? := Expr.abiTyWithEnv? env target
              match FunctionDecl.internalTypeConversionSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions targetTy inner
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      targetCore
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some coreStmt => some coreStmt
              | none =>
                  match assignmentCoreWithEnv? storageNames env target
                      (Expr.call (Expr.typeName targetTy) [Arg.positional inner]) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.expr
          (Expr.assign target AssignOp.assign
            (Expr.binary op lhs rhs)) =>
          let fallback :=
            Stmt.expr
              (Expr.assign target AssignOp.assign
                (Expr.binary op lhs rhs))
          match Expr.toCoreLValueWithEnvCleanup? storageNames env target with
          | some targetCore =>
              let targetTy? := Expr.abiTyWithEnv? env target
              match FunctionDecl.internalBinarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op lhs rhs
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      targetCore
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some coreStmt => some coreStmt
              | none =>
                  match assignmentCoreWithEnv? storageNames env target
                      (Expr.binary op lhs rhs) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.expr (Expr.assign lhs AssignOp.assign rhs) =>
          match assignmentCoreWithEnv? storageNames env lhs rhs with
          | some coreStmt => some coreStmt
          | none =>
              -- OVERREJECT-CALLPOS-BATCH (B): plain `lhs = rhs` where the pure
              -- assignment lowering fails and `rhs` is a call-position shape the
              -- single-return hoister recognises (e.g. `y = arr[f()]`). The target
              -- LValue is lowered purely (`toCoreLValue?`); a target whose own index
              -- contains a call fails there and preserves the prior over-reject.
              -- solc evaluates the RHS then the (pure-index) LHS reference, which
              -- the prefix-then-assign shape reproduces.
              match Expr.toCoreLValueWithEnvCleanup? storageNames env lhs with
              | some targetCore =>
                  let targetTy? := Expr.abiTyWithEnv? env lhs
                  match FunctionDecl.internalExprSingleReturnUseCore?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions rhs
                      (fun resultExpr =>
                        SolidCore.Solidity.Source.Stmt.assign targetCore
                          (match targetTy? with
                          | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                          | none => resultExpr)) with
                  | some coreStmt => some coreStmt
                  | none =>
                      match
                          Stmt.argPositionHoist? internalFuel storageRefEnv env
                            externalCallKindEnv storageNames modifiers functions
                            freeFunctions returnTys rhs
                            (fun e => Stmt.expr (Expr.assign lhs AssignOp.assign e)) with
                      | some coreStmt => some coreStmt
                      | none => Stmt.toCore? storageNames
                          (Stmt.expr (Expr.assign lhs AssignOp.assign rhs))
              | none =>
                  match
                      Stmt.argPositionHoist? internalFuel storageRefEnv env
                        externalCallKindEnv storageNames modifiers functions
                        freeFunctions returnTys rhs
                        (fun e => Stmt.expr (Expr.assign lhs AssignOp.assign e)) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames
                      (Stmt.expr (Expr.assign lhs AssignOp.assign rhs))
      | Stmt.varDecl [binding]
          (some (Expr.binary op lhs rhs)) =>
          let fallback :=
            Stmt.varDecl [binding]
              (some (Expr.binary op lhs rhs))
          match binding.name with
          | some localName =>
              let targetTy? := binding.ty
              match FunctionDecl.internalBinarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op lhs rhs
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                  match varDeclCoreWithEnv? storageNames env binding
                      (Expr.binary op lhs rhs) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.varDecl [binding]
          (some (Expr.call (Expr.typeName targetTy)
            [Arg.positional inner])) =>
          let fallback :=
            Stmt.varDecl [binding]
              (some
                (Expr.call (Expr.typeName targetTy)
                  [Arg.positional inner]))
          match binding.name with
          | some localName =>
              let targetTy? := binding.ty
              match FunctionDecl.internalTypeConversionSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions targetTy inner
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                  match varDeclCoreWithEnv? storageNames env binding
                      (Expr.call (Expr.typeName targetTy) [Arg.positional inner]) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.varDecl [binding]
          (some (Expr.ternary cond thenExpr elseExpr)) =>
          let fallback :=
            Stmt.varDecl [binding]
              (some (Expr.ternary cond thenExpr elseExpr))
          match binding.name with
          | some localName =>
              let targetTy? := binding.ty
              let conditionBranchAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions thenExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (Ty.implicitCleanupCore targetTy resultExpr))
                let elseCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions elseExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (Ty.implicitCleanupCore targetTy resultExpr))
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      condCore thenCore elseCore)
              let conditionAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr
                let elseCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (SolidCore.Solidity.Source.Expr.ternary
                        condCore thenCore elseCore))
              match conditionBranchAssign? with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                match conditionAssign? with
                | some assignBlock => do
                    let declCore ←
                      Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        [declCore, assignBlock])
                | none =>
                  match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond thenExpr elseExpr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      some
                        (SolidCore.Solidity.Source.Stmt.block
                          [declCore, assignBlock])
                  | none =>
                      match FunctionDecl.internalTernaryBranchSingleReturnUseCore?
                          internalFuel storageRefEnv env externalCallKindEnv storageNames
                          modifiers functions freeFunctions cond thenExpr elseExpr
                          (fun resultExpr =>
                            SolidCore.Solidity.Source.Stmt.assign
                              (SolidCore.Solidity.Source.LValue.var localName)
                              (match targetTy? with
                              | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                              | none => resultExpr)) with
                      | some assignBlock => do
                          let declCore ←
                            Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                          some
                            (SolidCore.Solidity.Source.Stmt.block
                              [declCore, assignBlock])
                      | none =>
                          match varDeclCoreWithEnv? storageNames env binding
                              (Expr.ternary cond thenExpr elseExpr) with
                          | some coreStmt => some coreStmt
                          | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.varDecl [binding]
          (some (Expr.unary op expr)) =>
          let fallback :=
            Stmt.varDecl [binding]
              (some (Expr.unary op expr))
          match binding.name with
          | some localName =>
              let targetTy? := binding.ty
              match FunctionDecl.internalUnarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op expr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (match targetTy? with
                      | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                  match varDeclCoreWithEnv? storageNames env binding
                      (Expr.unary op expr) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames fallback
          | none => Stmt.toCore? storageNames fallback
      | Stmt.varDecl [binding] (some expr@(Expr.call (Expr.member _ _) _)) =>
          match binding.name, binding.ty with
          | some localName, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                  -- #201 (B): a MEMBER-call initializer that is an abi/concat
                  -- builtin with a flagged argument
                  -- (`bytes memory z = abi.encode(a + b)`,
                  -- `bytes memory z = abi.encode(abi.encodePacked(a + b))`,
                  -- `uint8 a,b`) is not an external call, so the chain above
                  -- declines and the statement fell env-less (silently encoding
                  -- 300). Route it through `varDeclCoreWithEnv?` so the env-aware
                  -- `abi.*`/concat arms fire the operand-width Panic 0x11;
                  -- unflagged member-call vardecls keep the env-less fallback
                  -- byte-identically.
                  match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
                      varDeclCoreWithEnv? storageNames env binding expr
                    else none) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames
                      (Stmt.varDecl [binding] (some expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl [binding]
          (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
          match binding.name, binding.ty with
          | some localName, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none => Stmt.toCore? storageNames
                  (Stmt.varDecl [binding] (some expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl [binding] (some expr@(Expr.call (Expr.ident name) args)) =>
          -- #201 (B): a HASH-builtin initializer with a flagged argument
          -- (`bytes32 h = keccak256(abi.encodePacked(a + b))`, `uint8 a,b`) is
          -- never a user function, so every chain below declines and the
          -- statement fell env-less (hashing 300). Gated on the builtin flag, so
          -- every user-function vardecl keeps the existing chain byte-identically.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
              varDeclCoreWithEnv? storageNames env binding expr
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match binding.name with
          | some localName =>
              match binding.location with
              | some DataLocation.storage =>
                  match FunctionDecl.internalSingleStorageReturnRefCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions name args
                      (fun retName =>
                        SolidCore.Solidity.Source.Stmt.storageAliasFrom
                          localName retName) with
                  | some assignBlock => some assignBlock
                  | none => Stmt.toCore? storageNames
                      (Stmt.varDecl [binding]
                        (some (Expr.call (Expr.ident name) args)))
              | _ =>
                  match Expr.externalFunctionValueCallSingleReturnCore?
                      storageNames env expr
                      (fun retExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          retExpr) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      some
                        (SolidCore.Solidity.Source.Stmt.block
                          [declCore, assignBlock])
                  | none =>
                      match FunctionDecl.internalSingleReturnCallCore?
                          internalFuel storageRefEnv env externalCallKindEnv
                          storageNames modifiers functions freeFunctions name args
                          (fun retExpr =>
                            SolidCore.Solidity.Source.Stmt.assign
                              (SolidCore.Solidity.Source.LValue.var localName)
                              retExpr) with
                      | some assignBlock => do
                          let declCore ←
                            Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                          some
                            (SolidCore.Solidity.Source.Stmt.block
                              [declCore, assignBlock])
                      | none =>
                          match FunctionDecl.abiInternalSingleReturnUseCore?
                              internalFuel storageRefEnv env externalCallKindEnv
                              storageNames modifiers functions freeFunctions
                              "_sol_vardecl_abi_arg" expr
                              (fun replacedExpr =>
                                varDeclCoreWithEnv? storageNames env binding
                                  replacedExpr) with
                          | some coreStmt => some coreStmt
                          | none => Stmt.toCore? storageNames
                              (Stmt.varDecl [binding]
                                (some (Expr.call (Expr.ident name) args)))
          | none => Stmt.toCore? storageNames
              (Stmt.varDecl [binding]
                (some (Expr.call (Expr.ident name) args)))
      -- A call through a function pointer stored in an aggregate has an
      -- arbitrary expression as its callee (`stored[k](x)`).  The direct-call
      -- initializer arms above only cover identifier/member callees, leaving
      -- this shape on the pure expression path where the storage word was
      -- mistaken for a dispatch value.  Reuse the general internal-expression
      -- call hoister, which already resolves and invokes aggregate-loaded
      -- internal function pointers for assignment/return positions.
      | Stmt.varDecl [binding] (some expr@(Expr.call _ _)) =>
          match binding.name, binding.ty with
          | some localName, some expectedTy =>
              match FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv
                  storageNames modifiers functions freeFunctions expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (Ty.implicitCleanupCore expectedTy retExpr)) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.varDecl [binding] (some expr))
          | _, _ =>
              Stmt.toCore? storageNames
                (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl [binding]
          (some expr@(Expr.callWithOptions (Expr.ident _) _ _)) =>
          match binding.name with
          | some localName =>
              match Expr.externalFunctionValueCallSingleReturnCore?
                  storageNames env expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [declCore, assignBlock])
              | none => Stmt.toCore? storageNames
                  (Stmt.varDecl [binding] (some expr))
          | none => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl [binding] (some expr@(Expr.newExpr _ _)) =>
          -- WS1 (H): `uint256[] memory t = new uint256[](a + b)` (`uint8 a,b`) —
          -- the allocation-size arithmetic Panics 0x11 at the operand width; the
          -- non-creation fallback below lowered the whole vardecl env-less. Only
          -- flagged sizes reroute (through `varDeclCoreWithEnv?`, reaching the
          -- env-aware `newExpr` arm); contract creations and unflagged news keep
          -- the existing lowering byte-identically.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
              varDeclCoreWithEnv? storageNames env binding expr
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match binding.name, binding.ty with
          | some localName, some _ =>
              match
                Expr.toContractCreationCoreWithKindEnv?
                  storageNames externalCallKindEnv expr with
              | some coreExpr => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [ declCore
                      , SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          coreExpr ])
              | none => Stmt.toCore? storageNames
                  (Stmt.varDecl [binding] (some expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl [binding]
          (some expr@(Expr.callWithOptions (Expr.newExpr _ []) _ _)) =>
          match binding.name, binding.ty with
          | some localName, some _ =>
              match
                Expr.toContractCreationCoreWithKindEnv?
                  storageNames externalCallKindEnv expr with
              | some coreExpr => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      [ declCore
                      , SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          coreExpr ])
              | none => Stmt.toCore? storageNames
                  (Stmt.varDecl [binding] (some expr))
          | _, _ => Stmt.toCore? storageNames
              (Stmt.varDecl [binding] (some expr))
      | Stmt.varDecl bindings (some expr@(Expr.call (Expr.member _ _) _)) =>
          -- #201 (B): a MEMBER-call initializer that is an abi/concat builtin with
          -- a flagged argument (`bytes memory z = abi.encode(a + b)`, `uint8 a,b`)
          -- is not an external call, so the external-call pieces below decline and
          -- the statement fell to the env-less lowering (silently encoding 300).
          -- Route it through `varDeclCoreWithEnv?` (the generic vardecl arm's
          -- helper) so the env-aware `abi.*`/concat arms fire the operand-width
          -- Panic 0x11. Unflagged member-call vardecls are untouched.
          match (match bindings with
            | [binding] =>
                if Expr.abiBuiltinArgsNeedEnvCleanup expr then
                  varDeclCoreWithEnv? storageNames env binding expr
                else none
            | _ => none) with
          | some coreStmt => some coreStmt
          | none => do
              let pieces ←
                Expr.externalCallAssignBindingsCorePiecesWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv bindings expr
              some (SolidCore.Solidity.Source.Stmt.block pieces)
      | Stmt.varDecl bindings
          (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) => do
          let pieces ←
            Expr.externalCallAssignBindingsCorePiecesWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv bindings expr
          some (SolidCore.Solidity.Source.Stmt.block pieces)
      | Stmt.varDecl bindings
          (some expr@(Expr.call (Expr.ident name) args)) => do
          -- #201 (B): a HASH-builtin initializer with a flagged argument
          -- (`bytes32 h = keccak256(abi.encodePacked(a + b))`, `uint8 a,b`) is
          -- never an internal function, so the `_sol_vardecl_arg` hoist / internal
          -- chains below decline and the statement fell env-less. Route it through
          -- `varDeclCoreWithEnv?` first (gated on the builtin flag, so every
          -- user-function vardecl keeps the existing chain byte-identically).
          match (match bindings with
            | [binding] =>
                if Expr.abiBuiltinArgsNeedEnvCleanup expr then
                  varDeclCoreWithEnv? storageNames env binding expr
                else none
            | _ => none) with
          | some coreStmt => some coreStmt
          | none =>
          -- Named-argument order (R1): reorder NAMED arguments into the callee's
          -- parameter-declaration order (as positional) BEFORE the direct-arg
          -- hoister (`hoistDirectInternalCallArgs?`) lifts their nested calls
          -- into `_sol_vardecl_arg_eval*` temps, so `g({b: t(1), a: t(2)})`
          -- evaluates the `a` expression `t(2)` first (solc reorders named args
          -- to parameter order, then evaluates L2R). Binding was already correct
          -- via `orderedArgs?`; positional calls are unchanged.
          let args := Expr.reorderNamedInternalCallArgs functions freeFunctions
            env (Expr.ident name) args
          let fallback? := do
            match FunctionDecl.internalVarDeclAssignReturnCallCorePieces?
                internalFuel storageRefEnv env externalCallKindEnv storageNames
                modifiers functions freeFunctions name args bindings with
            | some pieces =>
                some (SolidCore.Solidity.Source.Stmt.block pieces)
            | none => do
                match FunctionDecl.internalTupleVarDeclAssignReturnCallCorePieces?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions name args bindings with
                | some pieces =>
                    some (SolidCore.Solidity.Source.Stmt.block pieces)
                | none => do
                    match Expr.externalFunctionValueCallAssignBindingsCorePieces?
                        storageNames env bindings expr with
                    | some pieces =>
                        some (SolidCore.Solidity.Source.Stmt.block pieces)
                    | none => do
                        let names ← VarBindings.names? bindings
                        let decls ← VarBindings.toCoreDecls? bindings
                        let callCore ←
                          FunctionDecl.internalAssignReturnCallCore?
                            internalFuel storageRefEnv env externalCallKindEnv
                            storageNames modifiers functions freeFunctions name args
                            names
                        some
                          (SolidCore.Solidity.Source.Stmt.block
                            (decls ++ [callCore]))
          match FunctionDecl.hoistDirectInternalCallArgsForCallee?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions "_sol_vardecl_arg" name args with
          | some (prefixPieces, tempEnv, replacedArgs) =>
              (match FunctionDecl.internalVarDeclAssignReturnCallCorePieces?
                  internalFuel storageRefEnv (tempEnv ++ env) externalCallKindEnv
                  storageNames modifiers functions freeFunctions
                  name replacedArgs bindings with
              | some pieces =>
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      (prefixPieces ++
                        [SolidCore.Solidity.Source.Stmt.block pieces]))
              | none => fallback?)
          | none => fallback?
      | Stmt.varDecl bindings
          (some expr@(Expr.callWithOptions (Expr.ident _) _ _)) => do
          let pieces ←
            Expr.externalFunctionValueCallAssignBindingsCorePieces?
              storageNames env bindings expr
          some (SolidCore.Solidity.Source.Stmt.block pieces)
      | Stmt.varDecl [binding] (some expr) =>
          match storageVarDeclCoreWithEnv? storageNames env binding expr with
          | some coreStmt => some coreStmt
          | none =>
              match binding.name with
              | some localName =>
                  match FunctionDecl.internalExprSingleReturnUseCore?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions expr
                      (fun resultExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          (match binding.ty with
                          | some targetTy =>
                              Ty.implicitCleanupCore targetTy resultExpr
                          | none => resultExpr)) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      some
                        (SolidCore.Solidity.Source.Stmt.block
                          [declCore, assignBlock])
                  | none =>
                      match varDeclCoreWithEnv? storageNames env binding expr with
                      | some coreStmt => some coreStmt
                      | none =>
                          Stmt.toCore? storageNames
                            (Stmt.varDecl [binding] (some expr))
              | none =>
                  match varDeclCoreWithEnv? storageNames env binding expr with
                  | some coreStmt => some coreStmt
                  | none =>
                      Stmt.toCore? storageNames
                        (Stmt.varDecl [binding] (some expr))
      | Stmt.emitEvent (Expr.call (Expr.ident eventName) args) =>
          -- §3c COLLAPSE: every call-bearing emit shape routes through the
          -- SHARED emit/revert arg lowering
          -- (`FunctionDecl.eventErrorCallArgsCore?`); the call-free
          -- remainder keeps the #201 (D) env-cleanup gate byte-identically
          -- (flagged narrow checked arithmetic / abi-hash-concat builtins
          -- lower env-aware, unflagged shapes keep `Stmt.toCore?`).
          match FunctionDecl.eventErrorCallArgsCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions "_sol_event" true
              (fun coreArgs =>
                SolidCore.Solidity.Source.Stmt.emitEvent eventName coreArgs)
              (Stmt.emitEvent (Expr.call (Expr.ident eventName) args))
              args with
          | some result => result
          | none =>
              match (if Args.anyAbiArgNeedsEnvCleanup args then
                  (Args.toCoreExprsWithEnvCleanup? storageNames env args).map
                    (fun coreArgs =>
                      SolidCore.Solidity.Source.Stmt.emitEvent
                        eventName coreArgs)
                else none) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.emitEvent (Expr.call (Expr.ident eventName) args))
      | Stmt.revertCall (Expr.call (Expr.ident errorName) args) =>
          -- §3c COLLAPSE + #201 (E): every call-bearing custom-error revert
          -- routes through the SAME shared lowering as emit, so the pure
          -- companion arguments are env-aware (`revert Err(a + b, bump())`
          -- with `uint8 a,b` Panics 0x11 as solc+EVM do — the copy-pasted
          -- revert arms had drifted env-less). The builtin `revert(...)`
          -- statement (errorName "revert") keeps the historical env-less
          -- single-call hoist (no flagged-single-call env fallback) and its
          -- dedicated `Stmt.toCore?` arms. The call-free remainder keeps
          -- the #201 (E) env-cleanup gate byte-identically.
          match (if errorName == "revert" then
              match args with
              | [Arg.positional reason] =>
                  if Expr.abiArgNeedsEnvCleanup? reason then do
                    let reasonTy ← Expr.abiTyWithEnv? env reason
                    let reasonCore ←
                      Expr.toCoreAsWithEnv?
                        storageNames env reasonTy reason
                    some
                      (SolidCore.Solidity.Source.Stmt.revertErrorExpr
                        reasonCore)
                  else none
              | _ => none
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match FunctionDecl.eventErrorCallArgsCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions "_sol_error"
              (errorName != "revert")
              (fun coreArgs =>
                SolidCore.Solidity.Source.Stmt.revert errorName coreArgs)
              (Stmt.revertCall (Expr.call (Expr.ident errorName) args))
              args with
          | some result => result
          | none =>
              match (if errorName != "revert" &&
                    Args.anyAbiArgNeedsEnvCleanup args then
                  (Args.toCoreExprsWithEnvCleanup? storageNames env args).map
                    (fun coreArgs =>
                      SolidCore.Solidity.Source.Stmt.revert
                        errorName coreArgs)
                else none) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.revertCall (Expr.call (Expr.ident errorName) args))
      | Stmt.returnValues
          (some (Expr.ternary cond thenExpr elseExpr)) =>
          let fallback :=
            Stmt.returnValues (some (Expr.ternary cond thenExpr elseExpr))
          match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions cond thenExpr elseExpr
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
          | some coreStmt => some coreStmt
          | none =>
              match FunctionDecl.internalTernaryBranchSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond thenExpr elseExpr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
              | some coreStmt => some coreStmt
              | none =>
                  match returnTys with
                  | [] => Stmt.toCore? storageNames fallback
                  | _ :: _ =>
                      match
                          returnValuesCoreWithReturnTys? storageNames env
                            returnTys thenExpr,
                          returnValuesCoreWithReturnTys? storageNames env
                            returnTys elseExpr with
                      | some thenCore, some elseCore =>
                          FunctionDecl.conditionUseCoreWithInternalCalls?
                            internalFuel storageRefEnv env externalCallKindEnv
                            storageNames modifiers functions freeFunctions cond
                            (fun condCore =>
                              SolidCore.Solidity.Source.Stmt.ifElse
                                condCore thenCore elseCore)
                      | _, _ => Stmt.toCore? storageNames fallback
      | Stmt.returnValues
          (some (Expr.unary op expr)) =>
          match FunctionDecl.internalUnarySingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions op expr
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
          | some coreStmt => some coreStmt
          | none =>
              returnValuesCoreWithReturnTys? storageNames env returnTys
                (Expr.unary op expr)
      | Stmt.returnValues (some (Expr.tuple items)) =>
          match FunctionDecl.tupleReturnValuesCoreWithInternalCalls?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys items with
          | some coreStmt => some coreStmt
          | none =>
              match
                  Stmt.argPositionHoist? internalFuel storageRefEnv env
                    externalCallKindEnv storageNames modifiers functions
                    freeFunctions returnTys (Expr.tuple items)
                    (fun e => Stmt.returnValues (some e)) with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames
                    (Stmt.returnValues (some (Expr.tuple items)))
      | Stmt.returnValues (some (Expr.binary op lhs rhs)) =>
          match FunctionDecl.internalBinarySingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions op lhs rhs
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
          | some coreStmt => some coreStmt
          | none =>
              returnValuesCoreWithReturnTys? storageNames env returnTys
                (Expr.binary op lhs rhs)
      | Stmt.returnValues
          (some (Expr.call (Expr.typeName targetTy)
            [Arg.positional inner])) =>
          let fallback :=
            Stmt.returnValues
              (some
                (Expr.call (Expr.typeName targetTy)
                  [Arg.positional inner]))
          match FunctionDecl.internalTypeConversionSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions targetTy inner
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
          | some coreStmt => some coreStmt
          | none =>
              -- H2: route a conversion-typed return through the type-directed
              -- elaboration (which keeps a narrow `uintN`/`intN` cast of a checked
              -- arithmetic argument at its operand width, so the overflow Panic
              -- 0x11 survives). `returnValuesCoreWithReturnTys?` itself falls back
              -- to the env-less `Stmt.toCore?` shape when the type-directed path
              -- does not apply, so no previously-accepted return regresses.
              match returnValuesCoreWithReturnTys? storageNames env returnTys
                  (Expr.call (Expr.typeName targetTy) [Arg.positional inner]) with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames fallback
      | Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "decode")
              [Arg.positional data, Arg.positional typesExpr])) => do
          let (tys, cleanups, directDataCore) ←
            Expr.toAbiDecode? storageNames data typesExpr
          let dataCore ←
            if Expr.abiArgNeedsEnvCleanup? data then do
              let dataTy ← Expr.abiTyWithEnv? env data
              Expr.toCoreAsWithEnv? storageNames env dataTy data
            else
              some directDataCore
          some
            (SolidCore.Solidity.Source.Stmt.returnValues
              (abiDecodeReturnExprs tys cleanups dataCore))
      | Stmt.returnValues
          (some expr@(Expr.call (Expr.member (Expr.ident "abi") member) args)) =>
          -- TC1: `return abi.encode(c ? x : y)` / `abi.encodePacked(...)` with a
          -- `bytesN`-common-type conditional argument must widen each branch to the
          -- common type (left-aligned). The generic member-call return path below
          -- lowers `abi.*` through the env-less `Stmt.toCore?`, which has no branch
          -- types, so the narrow branch keeps the wrong alignment. Route these
          -- through the typed env path (`Expr.toCoreAsWithEnv?`), which inserts the
          -- per-branch `fixedBytesCast`. Only the `bytesN`-conditional shape is
          -- rerouted; every other `abi.*` return keeps the env-less lowering, byte
          -- for byte.
          -- STAGE-D #193: additionally reroute when any argument carries narrow
          -- checked arithmetic (`abi.encode(a + b)`, `uint8` — must Panic 0x11 at
          -- the operand width); the env-aware `abi.*` arms handle both shapes.
          if ((member == "encode" || member == "encodePacked") &&
                Args.anyAbiEncodeFixedBytesTernary? storageNames env args) ||
              Expr.abiBuiltinArgsNeedEnvCleanup expr then
            match returnTys with
            | [returnTy] =>
                match Expr.toCoreAsWithEnv? storageNames env returnTy expr with
                | some coreExpr =>
                    some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
                | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
            | _ => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
          else
            -- ABI-ENCODE-INTERNAL-CALL-ARG (#174): a direct internal call nested in
            -- an `abi.encode`/`abi.encodePacked`/… argument (`abi.encode(g())`,
            -- `abi.encode(uint256(9), g())`, `abi.encode(uint256(g()) + 1)`) cannot
            -- be lowered by the env-less `Stmt.toCore?` (which routes each abi arg
            -- through `exprToCore?`, and that has no way to lower an internal call).
            -- Route through the generic argument-position call hoister FIRST — it
            -- peels the strictly-nested internal call into a prefix temp and re-lowers
            -- `abi.encode((retTy)(_tmp))`, which lowers cleanly (the pure-local abi
            -- arg case). Only falls back to the env-less shape when nothing was
            -- hoisted, so every previously-accepted `abi.*` return is byte-identical.
            match Stmt.argPositionHoist? internalFuel storageRefEnv env
                externalCallKindEnv storageNames modifiers functions freeFunctions
                returnTys expr (fun e => Stmt.returnValues (some e)) with
            | some coreStmt => some coreStmt
            | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues (some expr@(Expr.call (Expr.member _ _) _)) =>
          -- STAGE-D #193: `return bytes.concat(bytes1(a + b))` (and any concat with
          -- a narrow-checked-arithmetic argument) must go through the env-aware
          -- lowering so the operand-width Panic 0x11 fires; the env-less paths
          -- below run the arithmetic at 256 bits. Only the flagged shapes are
          -- rerouted; on `none` the original chain runs unchanged.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
              match returnTys with
              | [returnTy] =>
                  (Expr.toCoreAsWithEnv? storageNames env returnTy expr).map
                    (fun coreExpr =>
                      SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
              | _ => none
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match Expr.lowLevelTupleReturnCore? storageNames env returnTys expr with
          | some coreStmt => some coreStmt
          | none =>
            if returnTys.isEmpty then
              match Expr.noReturnEffectStmtCoreWithStorageRefs?
                  storageRefEnv env storageNames expr with
              | some coreStmt => some (CoreStmt.thenReturnEmpty coreStmt)
              | none =>
                  match Expr.externalCallReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                      storageNames env externalCallKindEnv returnTys expr with
                  | some coreStmt => some coreStmt
                  | none =>
                      Stmt.toCore? storageNames (Stmt.returnValues (some expr))
            else
              match Expr.externalCallReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv returnTys expr with
              | some coreStmt => some coreStmt
              | none =>
                  Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues
          (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) =>
          match Expr.lowLevelTupleReturnCore? storageNames env returnTys expr with
          | some coreStmt => some coreStmt
          | none =>
              match Expr.externalCallReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv returnTys expr with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues (some expr@(Expr.call (Expr.ident name) args)) =>
          -- STAGE-D #193: `return keccak256(abi.encodePacked(a + b))` (hash builtin
          -- over an abi/concat call with a narrow-checked-arithmetic argument) must
          -- go through the env-aware lowering so the operand-width Panic 0x11
          -- fires. Only the flagged hash/abi shapes reroute (`name` is a builtin,
          -- never a user function there); everything else keeps the chain below.
          -- `ripemd160` is `bytesN 20`: when the return type is a WIDER `bytesN`
          -- (`return ripemd160(x)` from `returns (bytes32)`) the implicit
          -- `bytes20 -> bytes32` widening must move the digest into the HIGH bytes
          -- (left-aligned). The env-less `Stmt.toCore?` below is target-blind and
          -- lowers the hash at its natural width, leaving the digest right-aligned
          -- (wrong value), so route it through the return-type-aware env path — an
          -- identity for a `bytes20` target, the `fixedBytesCast` widening otherwise.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr || name == "ripemd160" then
              match returnTys with
              | [returnTy] =>
                  (Expr.toCoreAsWithEnv? storageNames env returnTy expr).map
                    (fun coreExpr =>
                      SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
              | _ => none
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          let fallback? :=
            match Expr.externalFunctionValueCallReturnCore?
                storageNames env returnTys expr with
            | some coreStmt => some coreStmt
            | none =>
                if returnTys.isEmpty then
                  match FunctionDecl.internalStatementCallCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions name args with
                  | some coreStmt => some (CoreStmt.thenReturnEmpty coreStmt)
                  | none =>
                      match
                          Stmt.argPositionHoist? internalFuel storageRefEnv env
                            externalCallKindEnv storageNames modifiers functions
                            freeFunctions returnTys (Expr.call (Expr.ident name) args)
                            (fun e => Stmt.returnValues (some e)) with
                      | some coreStmt => some coreStmt
                      | none => Stmt.toCore? storageNames
                          (Stmt.returnValues
                            (some (Expr.call (Expr.ident name) args)))
                else
                  match FunctionDecl.internalReturnCallCore?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions name args
                      returnTys with
                  | some coreStmt => some coreStmt
                  | none =>
                      match FunctionDecl.internalSingleReturnCallCore?
                          internalFuel storageRefEnv env externalCallKindEnv
                          storageNames modifiers functions freeFunctions name args
                          (fun retExpr =>
                            SolidCore.Solidity.Source.Stmt.returnValues [retExpr]) with
                      | some coreStmt => some coreStmt
                      | none =>
                          match
                              Stmt.argPositionHoist? internalFuel storageRefEnv env
                                externalCallKindEnv storageNames modifiers functions
                                freeFunctions returnTys
                                (Expr.call (Expr.ident name) args)
                                (fun e => Stmt.returnValues (some e)) with
                          | some coreStmt => some coreStmt
                          | none => Stmt.toCore? storageNames
                              (Stmt.returnValues
                                (some (Expr.call (Expr.ident name) args)))
          match FunctionDecl.hoistDirectInternalCallArgsForCallee?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions "_sol_return_arg" name args with
          | some (prefixPieces, tempEnv, replacedArgs) =>
              let envWith := tempEnv ++ env
              (match
                  (if returnTys.isEmpty then
                    match FunctionDecl.internalStatementCallCore?
                        internalFuel storageRefEnv envWith externalCallKindEnv
                        storageNames modifiers functions freeFunctions
                        name replacedArgs with
                    | some coreStmt =>
                        some (CoreStmt.thenReturnEmpty coreStmt)
                    | none => none
                  else
                    match FunctionDecl.internalReturnCallCore?
                        internalFuel storageRefEnv envWith externalCallKindEnv
                        storageNames modifiers functions freeFunctions
                        name replacedArgs returnTys with
                    | some coreStmt => some coreStmt
                    | none =>
                        FunctionDecl.internalSingleReturnCallCore?
                          internalFuel storageRefEnv envWith externalCallKindEnv
                          storageNames modifiers functions freeFunctions
                          name replacedArgs
                          (fun retExpr =>
                            SolidCore.Solidity.Source.Stmt.returnValues
                              [retExpr])) with
              | some callCore =>
                  some
                    (SolidCore.Solidity.Source.Stmt.block
                      (prefixPieces ++ [callCore]))
              | none => fallback?)
          | none => fallback?
      | Stmt.returnValues
          (some expr@(Expr.callWithOptions (Expr.ident _) _ _)) =>
          match Expr.externalFunctionValueCallReturnCore?
              storageNames env returnTys expr with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues (some expr@(Expr.newExpr _ _)) =>
          -- WS1 (H): `return new uint256[](a + b)` (`uint8 a,b`) — flagged
          -- allocation sizes reroute through the env-aware `newExpr` arm (Panic
          -- 0x11 at the operand width); contract creations and unflagged news
          -- keep the existing chain byte-identically.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
              match returnTys with
              | [returnTy] =>
                  (Expr.toCoreAsWithEnv? storageNames env returnTy expr).map
                    (fun coreExpr =>
                      SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
              | _ => none
            else none) with
          | some coreStmt => some coreStmt
          | none =>
          match
            Expr.toContractCreationCoreWithKindEnv?
              storageNames externalCallKindEnv expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
          | none =>
              match
                  Stmt.argPositionHoist? internalFuel storageRefEnv env
                    externalCallKindEnv storageNames modifiers functions
                    freeFunctions returnTys expr
                    (fun e => Stmt.returnValues (some e)) with
              | some coreStmt => some coreStmt
              | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues
          (some expr@(Expr.callWithOptions (Expr.newExpr _ []) _ _)) =>
          match
            Expr.toContractCreationCoreWithKindEnv?
              storageNames externalCallKindEnv expr with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
          | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues
          (some (Expr.index base (Expr.call (Expr.ident iname) iargs))) =>
          -- MI1 (rvalue): `return base[idu8(k)]` — an internal-call result used as a
          -- mapping/array INDEX in a read position. The plain index-read lowering
          -- (`Expr.toCore?`) has no internal-call fallback for the index operand, so
          -- this used to over-reject. Hoist the index call into a temp and build the
          -- index read with the temp (the base is a pure storage/local reference, so
          -- base-before-index order is preserved). Non-internal-call indices still
          -- match this pattern but the hoist returns `none`, so we fall back to the
          -- ordinary return lowering — no behaviour change.
          let original :=
            Stmt.returnValues
              (some (Expr.index base (Expr.call (Expr.ident iname) iargs)))
          match
              (do
                let buildRead ←
                  Expr.indexReadCoreBuilderWithEnvCleanup? storageNames env base
                FunctionDecl.internalSingleReturnCallCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions iname iargs
                  (fun idxCore =>
                    SolidCore.Solidity.Source.Stmt.returnValues
                      [buildRead idxCore])) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames original
      | Stmt.returnValues (some expr@(Expr.call (Expr.index _ _) _)) =>
          -- `return arr[i](x)` — a call through an internal function POINTER read
          -- from an array element. The plain return lowerings have no fallback for
          -- a non-identifier callee; hoist it via `internalExprSingleReturnUseCore?`
          -- (declines to `none` for non-pointer callees, preserving over-reject).
          match FunctionDecl.internalExprSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions expr
              (fun resultExpr =>
                SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
          | some coreStmt => some coreStmt
          | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.returnValues (some expr) =>
          match returnValuesCoreWithReturnTys? storageNames env returnTys expr with
          | some coreStmt => some coreStmt
          | none =>
              -- A bare returned expression can itself require the internal-call
              -- hoister. In particular, `return g()(7)` first calls `g` to obtain
              -- an internal function pointer, then immediately dispatches through
              -- it. Binary/conditional contexts already reached this helper, but
              -- the generic return fallback skipped it and failed closed.
              match FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions expr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]) with
              | some coreStmt => some coreStmt
              | none =>
                  match
                      Stmt.argPositionHoist? internalFuel storageRefEnv env
                        externalCallKindEnv storageNames modifiers functions
                        freeFunctions returnTys expr
                        (fun e => Stmt.returnValues (some e)) with
                  | some coreStmt => some coreStmt
                  | none => Stmt.toCore? storageNames (Stmt.returnValues (some expr))
      | Stmt.ifElse (Expr.call (Expr.ident name) args)
          thenBranch elseBranch => do
          let thenCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := thenBranch)
          let elseCore ←
            match elseBranch with
            | some stmt =>
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := stmt)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  retExpr thenCore elseCore) with
          | some coreStmt => some coreStmt
          | none => do
              let condCore ←
                Expr.toCore? storageNames (Expr.call (Expr.ident name) args)
              some (SolidCore.Solidity.Source.Stmt.ifElse
                condCore thenCore elseCore)
      | Stmt.ifElse cond thenBranch elseBranch => do
          let thenCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := thenBranch)
          let elseCore ←
            match elseBranch with
            | some stmt =>
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := stmt)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          FunctionDecl.conditionUseCoreWithInternalCalls?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions cond
            (fun condCore =>
              SolidCore.Solidity.Source.Stmt.ifElse
                condCore thenCore elseCore)
      | Stmt.whileLoop (Expr.call (Expr.ident name) args) body => do
          let bodyCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := body)
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.ifElse
                  retExpr bodyCore SolidCore.Solidity.Source.Stmt.break) with
          | some stepCore =>
              some
                (SolidCore.Solidity.Source.Stmt.whileLoop
                  (SolidCore.Solidity.Source.Expr.word 1)
                  stepCore)
          | none => do
              let condCore ←
                Expr.toCore? storageNames (Expr.call (Expr.ident name) args)
              some (SolidCore.Solidity.Source.Stmt.whileLoop
                condCore bodyCore)
      | Stmt.whileLoop cond body => do
          let bodyCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := body)
          match Expr.conditionCoreWithEnv? storageNames env cond with
          | some condCore =>
              -- call-free condition: `whileLoop` node with the env-aware (R2,
              -- operand-width-cleaned) condition lowering.
              some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
          | none =>
              -- CALL-POSITION (#3): the condition contains a call the pure lowering
              -- can't hoist. Desugar `while (cond) body` into the same `while(1) {
              -- if(cond') body else break }` shape already used for bare
              -- `while(f())`, evaluating the hoisted call statements at the top of
              -- every iteration (re-evaluation matches solc). `continue` in `body`
              -- jumps to the `while(1)` top and re-checks the condition — exactly
              -- `while` semantics — so no `continue` guard is needed here.
              match
                  FunctionDecl.conditionUseCoreWithInternalCalls?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions cond
                    (fun condCore =>
                      SolidCore.Solidity.Source.Stmt.ifElse
                        condCore bodyCore SolidCore.Solidity.Source.Stmt.break) with
              | some stepCore =>
                  some
                    (SolidCore.Solidity.Source.Stmt.whileLoop
                      (SolidCore.Solidity.Source.Expr.word 1) stepCore)
              | none => none
      | Stmt.doWhile body cond => do
          let bodyCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := body)
          match Expr.conditionCoreWithEnv? storageNames env cond with
          | some condCore =>
              -- call-free condition: `doWhile` node with the env-aware (R2)
              -- condition lowering.
              some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
          | none =>
              -- CALL-POSITION (#2): the post-body condition contains a call. Desugar
              -- `do body while(cond)` into `while(1) { body; <hoist>; if(cond') {}
              -- else break }`, evaluating the hoisted condition-call at the bottom
              -- of every iteration (re-evaluation matches solc).
              match
                  FunctionDecl.conditionUseCoreWithInternalCalls?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions cond
                    (fun condCore =>
                      SolidCore.Solidity.Source.Stmt.ifElse
                        condCore SolidCore.Solidity.Source.Stmt.skip
                        SolidCore.Solidity.Source.Stmt.break) with
              | some checkCore =>
                  if Stmt.mentionsBareContinue body then
                    -- LOOP-COND-CALL-CONTINUE (#133): a bare `continue` in a
                    -- do-while must jump to the (hoisted) condition re-check, but
                    -- the naive `while(1) { body; check }` desugar would send it to
                    -- the `while(1)` top (re-running `body`, skipping `check`).
                    -- Relocate `check` to the TOP of the loop, guarded by a fresh
                    -- flag so it is skipped on the first iteration — then `continue`
                    -- and normal fall-through both re-check `cond` before the next
                    -- `body`, exactly matching do-while semantics. The whole loop is
                    -- wrapped in a `block` (its own scope), so the flag never
                    -- collides with a nested call-condition loop's flag.
                    let flagName := "__solidcore_loop_first"
                    some
                      (SolidCore.Solidity.Source.Stmt.block
                        [ SolidCore.Solidity.Source.Stmt.varDecl
                            SolidCore.Solidity.Source.Ty.bool flagName
                            (some (SolidCore.Solidity.Source.Expr.word 1))
                        , SolidCore.Solidity.Source.Stmt.whileLoop
                            (SolidCore.Solidity.Source.Expr.word 1)
                            (SolidCore.Solidity.Source.Stmt.block
                              [ SolidCore.Solidity.Source.Stmt.ifElse
                                  (SolidCore.Solidity.Source.Expr.var flagName)
                                  (SolidCore.Solidity.Source.Stmt.assign
                                    (SolidCore.Solidity.Source.LValue.var flagName)
                                    (SolidCore.Solidity.Source.Expr.word 0))
                                  checkCore
                              , bodyCore ]) ])
                  else
                    some
                      (SolidCore.Solidity.Source.Stmt.whileLoop
                        (SolidCore.Solidity.Source.Expr.word 1)
                        (SolidCore.Solidity.Source.Stmt.block [bodyCore, checkCore]))
              | none => none
      | Stmt.forLoop init cond post body => do
          -- NARROW-FORINIT (#182): the for-init `varDecl` bindings are in scope for
          -- `cond`, `post`, and `body`. Extend the type env with them before lowering
          -- those, so a narrow (`uintN`/`intN`) for-init counter's `i++`/`i +=`
          -- reaches the env-aware `toCoreIncDecWithEnv?`/`toCoreAssignOpWithEnv?`
          -- (emitting the operand-width `uintCleanup`/`intCleanup` → Panic 0x11 on
          -- overflow). Without this, the env-less fallback dropped the cleanup and
          -- silently widened the counter to 256 bits. A block-declared counter
          -- already worked because the block lowerer extends env per varDecl.
          let loopEnv :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                VarBindings.extendTypeEnv env bindings
            | _ => env
          -- A call-valued loop declaration must keep the declared variable in
          -- the scope shared by the condition, post expression, and body.
          -- The ordinary single-statement varDecl lowerer returns
          -- `block [decl, call]`; using that block as the `forLoop` initializer
          -- pops the declaration before the first condition check. Split only
          -- this direct internal-call shape into an outer prefix and use a
          -- no-op loop initializer.
          let (initCore, initPrefix) ←
            match init with
            | some (Stmt.varDecl [binding]
                (some (Expr.call (Expr.ident name) args))) =>
                match binding.name with
                | some localName =>
                    match FunctionDecl.internalSingleReturnCallCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions name args
                        (fun retExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (match binding.ty with
                            | some targetTy =>
                                Ty.implicitCleanupCore targetTy retExpr
                            | none => retExpr)) with
                    | some callCore => do
                        let declCore ←
                          Stmt.toCore? storageNames
                            (Stmt.varDecl [binding] none)
                        some
                          ( SolidCore.Solidity.Source.Stmt.skip
                          , [declCore, callCore] )
                    | none => do
                        let core ←
                          Stmt.toCoreWithInternalCalls?
                            (internalFuel := internalFuel)
                            (storageRefEnv := storageRefEnv)
                            (env := env)
                            (externalCallKindEnv := externalCallKindEnv)
                            (storageNames := storageNames)
                            (modifiers := modifiers)
                            (functions := functions)
                            (freeFunctions := freeFunctions)
                            (returnTys := returnTys)
                            (stmt := Stmt.varDecl [binding]
                              (some (Expr.call (Expr.ident name) args)))
                        some (core, [])
                | none => do
                    let core ←
                      Stmt.toCoreWithInternalCalls?
                        (internalFuel := internalFuel)
                        (storageRefEnv := storageRefEnv)
                        (env := env)
                        (externalCallKindEnv := externalCallKindEnv)
                        (storageNames := storageNames)
                        (modifiers := modifiers)
                        (functions := functions)
                        (freeFunctions := freeFunctions)
                        (returnTys := returnTys)
                        (stmt := Stmt.varDecl [binding]
                          (some (Expr.call (Expr.ident name) args)))
                    some (core, [])
            | some stmt =>
                (Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := stmt)).map (fun core => (core, []))
            | none =>
                some (SolidCore.Solidity.Source.Stmt.skip, [])
          let postCore ←
            match post with
            | some expr =>
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := loopEnv)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.expr expr)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let bodyCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := loopEnv)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := body)
          -- Try the pure lowering of the condition first: a call-free (or `none`)
          -- condition keeps today's `forLoop` node, with the env-aware (R2)
          -- condition lowering under `loopEnv` (the for-init bindings are in
          -- scope for the condition).
          let purecond? : Option CoreExpr :=
            match cond with
            | some expr => Expr.conditionCoreWithEnv? storageNames loopEnv expr
            | none => some (SolidCore.Solidity.Source.Expr.word 1)
          match purecond? with
          | some condCore =>
              let loopCore :=
                SolidCore.Solidity.Source.Stmt.forLoop
                  initCore condCore postCore bodyCore
              if initPrefix.isEmpty then
                some loopCore
              else
                some
                  (SolidCore.Solidity.Source.Stmt.block
                    (initPrefix ++ [loopCore]))
          | none =>
              -- CALL-POSITION (#1): the condition contains a call. Desugar
              -- `for (init; cond; post) body` into
              -- `{ init; while(1) { <hoist>; if(cond') {} else break; body; post } }`.
              match cond with
              | none => none  -- unreachable: `none` cond succeeds above
              | some condExpr =>
                    -- The condition is in the scope of the for-init declaration, so
                    -- extend the type env with any init bindings before hoisting the
                    -- call (the hoister needs the type of a non-call operand like the
                    -- loop counter `i` in `i < f()`).
                    let condEnv :=
                      match init with
                      | some (Stmt.varDecl bindings _) =>
                          VarBindings.extendTypeEnv env bindings
                      | _ => env
                    match
                        FunctionDecl.conditionUseCoreWithInternalCalls?
                          internalFuel storageRefEnv condEnv externalCallKindEnv
                          storageNames modifiers functions freeFunctions condExpr
                          (fun condCore =>
                            SolidCore.Solidity.Source.Stmt.ifElse
                              condCore SolidCore.Solidity.Source.Stmt.skip
                              SolidCore.Solidity.Source.Stmt.break) with
                    | some checkCore =>
                        if Stmt.mentionsBareContinue body then
                          -- LOOP-COND-CALL-CONTINUE (#133): a bare `continue` in a
                          -- `for` must run `post` and then re-check `cond`; the naive
                          -- `while(1) { check; body; post }` desugar would instead
                          -- send it to the `while(1)` top (re-running `check`,
                          -- skipping `post`). Relocate `post` to the TOP of the loop,
                          -- guarded by a fresh flag so it is skipped on the first
                          -- iteration — then `continue` and normal fall-through both
                          -- run `post` before the `check`, exactly matching `for`
                          -- semantics. The loop is wrapped in a `block` (its own
                          -- scope), so the flag never collides with a nested
                          -- call-condition loop's flag.
                          let flagName := "__solidcore_loop_first"
                          some
                            (SolidCore.Solidity.Source.Stmt.block
                              (initPrefix ++ [ initCore
                              , SolidCore.Solidity.Source.Stmt.varDecl
                                  SolidCore.Solidity.Source.Ty.bool flagName
                                  (some (SolidCore.Solidity.Source.Expr.word 1))
                              , SolidCore.Solidity.Source.Stmt.whileLoop
                                  (SolidCore.Solidity.Source.Expr.word 1)
                                  (SolidCore.Solidity.Source.Stmt.block
                                    [ SolidCore.Solidity.Source.Stmt.ifElse
                                        (SolidCore.Solidity.Source.Expr.var flagName)
                                        (SolidCore.Solidity.Source.Stmt.assign
                                          (SolidCore.Solidity.Source.LValue.var flagName)
                                          (SolidCore.Solidity.Source.Expr.word 0))
                                        postCore
                                    , checkCore
                                    , bodyCore ]) ]))
                        else
                          some
                            (SolidCore.Solidity.Source.Stmt.block
                              (initPrefix ++ [ initCore
                              , SolidCore.Solidity.Source.Stmt.whileLoop
                                  (SolidCore.Solidity.Source.Expr.word 1)
                                  (SolidCore.Solidity.Source.Stmt.block
                                    [checkCore, bodyCore, postCore]) ]))
                    | none => none
      | Stmt.tryCatch expr clauses => do
          match Expr.toExternalCallWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) => do
              let catchCore ←
                CatchClause.listToCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys clauses
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv env [] expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode [] []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
          | none => do
              match Expr.externalFunctionValueCallCore? storageNames env expr with
              | some (kind, _, targetCore, calldataCore, valueCore, gasCore?,
                  gasFirst) => do
                  let catchCore ←
                    CatchClause.listToCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions returnTys clauses
                  some
                    (SolidCore.Solidity.Source.Stmt.tryExternalCall
                      kind targetCore calldataCore valueCore gasCore? gasFirst
                      true [] []
                      SolidCore.Solidity.Source.Stmt.skip catchCore)
              | none => do
                  let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                    Expr.toContractCreationWithKindEnv?
                      storageNames externalCallKindEnv expr
                  let catchCore ←
                    CatchClause.listToCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions returnTys clauses
                  some
                    (SolidCore.Solidity.Source.Stmt.tryContractCreate
                      contractName argsCore valueCore saltCore? valueBeforeSalt []
                      SolidCore.Solidity.Source.Stmt.skip catchCore)
      | Stmt.tryCatchReturns expr returns success clauses => do
          let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
          let returnAbiCleanups ←
            Tys.toCoreAbiCleanups? (returns.map Parameter.ty)
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          match Expr.toExternalCallWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) => do
              let successCore ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := successEnv)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := success)
              let catchCore ←
                CatchClause.listToCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys clauses
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv env
                  (returns.map Parameter.ty) expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode returnBindings returnAbiCleanups
                  successCore catchCore)
          | none => do
              match Expr.externalFunctionValueCallCore? storageNames env expr with
              | some (kind, _, targetCore, calldataCore, valueCore, gasCore?,
                  gasFirst) => do
                  let successCore ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := successEnv)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := success)
                  let catchCore ←
                    CatchClause.listToCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions returnTys clauses
                  let checkTargetCode := returns.isEmpty
                  some
                    (SolidCore.Solidity.Source.Stmt.tryExternalCall
                      kind targetCore calldataCore valueCore gasCore? gasFirst
                      checkTargetCode returnBindings returnAbiCleanups
                      successCore catchCore)
              | none => do
                  let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                    Expr.toContractCreationWithKindEnv?
                      storageNames externalCallKindEnv expr
                  let successCore ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := successEnv)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := success)
                  let catchCore ←
                    CatchClause.listToCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions returnTys clauses
                  some
                    (SolidCore.Solidity.Source.Stmt.tryContractCreate
                      contractName argsCore valueCore saltCore? valueBeforeSalt returnBindings
                      successCore catchCore)
      | Stmt.expr expr@(Expr.binary _ _ _)
      | Stmt.expr expr@(Expr.unary UnaryOp.neg _)
      | Stmt.expr expr@(Expr.unary UnaryOp.bitNot _)
      | Stmt.expr expr@(Expr.unary UnaryOp.logicalNot _) =>
          -- R2 (Stage C): a DISCARD-expression statement (`a + b;`, `-x;`) is
          -- still evaluated by solc with full checked semantics — a narrow
          -- checked overflow Panics 0x11 even though the value is dropped. Lower
          -- the expression env-aware at its OWN type (operand-width cleanup);
          -- fall back to the prior env-less lowering on `none`. Inc/dec and
          -- `delete` unaries matched their dedicated arms earlier.
          (match (do
              let ty ← Expr.abiTyWithEnv? env expr
              Expr.toCoreAsWithEnv? storageNames env ty expr) with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none => Stmt.toCore? storageNames (Stmt.expr expr))
      | Stmt.expr (Expr.ident name) =>
          -- A bare reference to a builtin namespace/function is a no-op. Keep
          -- ordinary locals and user-declared functions on the normal value
          -- path so shadowing retains its usual meaning.
          if strayBuiltinIdentAllowed name &&
              (TypeEnv.lookup? env name).isNone &&
              !functions.any (fun fn => fn.name == some name) then
            some SolidCore.Solidity.Source.Stmt.skip
          else
            Stmt.toCore? storageNames (Stmt.expr (Expr.ident name))
      | Stmt.expr expr =>
          match (if Expr.abiArgNeedsEnvCleanup? expr then do
              let ty ←
                match expr with
                | Expr.tuple items => do
                    let tys ← mapOption
                      (fun item => match item with
                        | TupleItem.value e => Expr.abiTyWithEnv? env e
                        | TupleItem.hole => none) items
                    some (Ty.tuple tys)
                | _ => Expr.abiTyWithEnv? env expr
              Expr.toCoreAsWithEnv? storageNames env ty expr
            else none) with
          | some coreExpr =>
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
          | none => Stmt.toCore? storageNames (Stmt.expr expr)
      | other => Stmt.toCore? storageNames other
      )
  | none =>
      match stmt with
      | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) => do
          match tupleVarDeclAllStorageCore? storageNames bindings items with
          | some decls =>
              some (SolidCore.Solidity.Source.Stmt.block decls)
          | none => do
              let (coreDecls, assigns) ←
                tupleVarDeclCorePieces? storageNames bindings items
              some (SolidCore.Solidity.Source.Stmt.block (coreDecls ++ assigns))
      -- GENERAL TUPLE-VARDECL (#171 abi.decode RHS, #172 ternary RHS): a
      -- multi-binding tuple decl whose non-literal-tuple RHS is lowerable as one
      -- expression. `Stmt.listLowerCore? internalFuel none` flattens this so the locals stay in scope for
      -- following statements; this block form covers a standalone decl.
      | Stmt.varDecl bindings@(_ :: _ :: _) (some rhs) => do
          let (coreDecls, assigns) ←
            tupleVarDeclGeneralCorePieces? storageNames bindings rhs
          some (SolidCore.Solidity.Source.Stmt.block (coreDecls ++ assigns))
      | Stmt.varDecl bindings init =>
          match bindings with
          | [] => some SolidCore.Solidity.Source.Stmt.skip
          | [binding] =>
              match binding.name, binding.ty with
              | some name, some ty =>
                  match binding.location, init with
                  | some DataLocation.storage, some source => do
                      match source with
                      | Expr.call (Expr.member target "push") [] =>
                          storageArrayPushReturnAliasBlockCore?
                            storageNames binding target
                      | _ => do
                          storageReferenceBindingSupported? binding
                          let (target, indexes) ←
                            Expr.storagePathCore? storageNames source
                          match indexes with
                          | [] =>
                              some
                                (SolidCore.Solidity.Source.Stmt.storageAlias
                                  name target)
                          | _ =>
                              some
                                (SolidCore.Solidity.Source.Stmt.storageAliasPath
                                  name target indexes)
                  | some DataLocation.storage, none =>
                      some
                        (SolidCore.Solidity.Source.Stmt.storageAlias name "")
                  | _, _ => do
                      let coreTy ← Ty.toCore? ty
                      let initCore ←
                        match init with
                        | some expr => do
                            let coreExpr ← Expr.toCoreAs? storageNames ty expr
                            some (some coreExpr)
                        | none => some none
                      if binding.location == some DataLocation.memory then
                        some
                          (SolidCore.Solidity.Source.Stmt.memoryVarDecl
                            coreTy name initCore)
                      else
                        some
                          (SolidCore.Solidity.Source.Stmt.varDecl
                            coreTy name initCore)
              | _, _ => none
          | _ =>
              match init with
              | some _ => none
              | none => do
                  let coreDecls ←
                    mapOption
                      (fun binding =>
                        match binding.name, binding.ty with
                        | some name, some ty => do
                            let coreTy ← Ty.toCore? ty
                            if binding.location == some DataLocation.memory then
                              some
                                (SolidCore.Solidity.Source.Stmt.memoryVarDecl
                                  coreTy name none)
                            else
                              some
                                (SolidCore.Solidity.Source.Stmt.varDecl
                                  coreTy name none)
                        | _, _ => none)
                      bindings
                  some (SolidCore.Solidity.Source.Stmt.block coreDecls)
      | Stmt.expr
          (Expr.call
            (Expr.ident "__solidcore_internal_function_pointer_panic") []) =>
          some
            (SolidCore.Solidity.Source.Stmt.panic
              internalFunctionPointerPanicCode)
      | Stmt.expr (Expr.assign (Expr.tuple lhsItems) AssignOp.assign rhs) =>
          tupleAssignmentCore? storageNames lhsItems rhs
      | Stmt.expr
          (Expr.assign
            (Expr.call (Expr.member target "push") [])
            AssignOp.assign rhs) =>
          storageArrayPushPathAssignCore? storageNames target rhs
      | Stmt.expr (Expr.assign lhs AssignOp.assign rhs) =>
          -- PUSH-FIELD-LVALUE: first try lowering an assignment through a
          -- `.push()`-returned reference (`xs.push().a = 7`, `ys.push()[1] = 9`).
          -- Returns `none` for every ordinary LHS, so the plain lvalue path below is
          -- unchanged (the direct `xs.push() = v` arm above still wins for that shape).
          match storageArrayPushIndexedAssignCore? storageNames lhs rhs with
          | some stmt => some stmt
          | none => do
              let lhsCore ← Expr.toCoreLValue? storageNames lhs
              let rhsCore ← Expr.toCore? storageNames rhs
              some (SolidCore.Solidity.Source.Stmt.assign lhsCore rhsCore)
      | Stmt.expr (Expr.assign lhs op rhs) => do
          let lhsCore ← Expr.toCoreLValue? storageNames lhs
          let coreOp ← AssignOp.toCoreBinary? op
          let rhsCore ← Expr.toCore? storageNames rhs
          some (SolidCore.Solidity.Source.Stmt.assignOp lhsCore coreOp rhsCore)
      | Stmt.expr (Expr.unary UnaryOp.delete target) => do
          let targetCore ← Expr.toCoreLValue? storageNames target
          some (SolidCore.Solidity.Source.Stmt.deleteValue targetCore)
      | Stmt.expr
          (Expr.call (Expr.member target "push") []) =>
          storageArrayPushPathCore? storageNames target none
      | Stmt.expr
          (Expr.call (Expr.member target "push")
            [Arg.positional value]) =>
          storageArrayPushPathCore? storageNames target (some value)
      | Stmt.expr
          (Expr.call (Expr.member target "pop") []) =>
          storageArrayPopPathCore? storageNames target
      | Stmt.expr
          (Expr.call (Expr.member target "transfer") [Arg.positional value]) =>
          Expr.transferCore? storageNames target value
      | Stmt.expr
          (Expr.call (Expr.ident "selfdestruct") [Arg.positional recipient]) => do
          let recipientCore ← Expr.toCore? storageNames recipient
          some (SolidCore.Solidity.Source.Stmt.selfdestruct recipientCore)
      | Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional cond]) => do
          let condCore ← Expr.toCore? storageNames cond
          some (SolidCore.Solidity.Source.Stmt.assertStmt condCore)
      | Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional cond]) => do
          let condCore ← Expr.toCore? storageNames cond
          some (SolidCore.Solidity.Source.Stmt.requireStmt condCore none)
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond, Arg.positional (Expr.literal (Literal.string reason))]) => do
          let condCore ← Expr.toCore? storageNames cond
          some (SolidCore.Solidity.Source.Stmt.requireStmt condCore (some reason))
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond, Arg.positional (Expr.call (Expr.ident name) args)]) => do
          let condCore ← Expr.toCore? storageNames cond
          let coreArgs ← Args.toCoreExprs? storageNames args
          some (SolidCore.Solidity.Source.Stmt.requireCustom
            condCore name coreArgs)
      -- REVERT-QUAL (#77), require form: `require(a > 0, Base.Err(a))` with a
      -- base-/self-qualified member-access error callee. Mirrors the bare-ident
      -- `requireCustom` arm by the UNQUALIFIED `name` (the require-custom checker
      -- member arm resolves it the same way); must precede the generic
      -- `[cond, reason]` fallback below, which would otherwise degrade to
      -- `requireErrorExpr` whose member-call `toCore` returns `none` (over-reject).
      -- Also covers the LIBRARY-qualified error (`require(cond, L.Bad(a))`): the
      -- library qualifier is not part of the error selector, so resolving by the
      -- bare `name` soundly encodes `keccak256("Bad(...)")` — matching the checker
      -- (`REQUIRE-QUAL library case`) which accepts library errors here too.
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond,
             Arg.positional
               (Expr.call (Expr.member (Expr.typeName (Ty.user _)) name) args)]) => do
          let condCore ← Expr.toCore? storageNames cond
          let coreArgs ← Args.toCoreExprs? storageNames args
          some (SolidCore.Solidity.Source.Stmt.requireCustom
            condCore name coreArgs)
      | Stmt.expr
          (Expr.call (Expr.ident "require")
            [Arg.positional cond, Arg.positional reason]) => do
          let condCore ← Expr.toCore? storageNames cond
          let reasonCore ← Expr.toCore? storageNames reason
          some (SolidCore.Solidity.Source.Stmt.requireErrorExpr
            condCore reasonCore)
      | Stmt.expr expr => do
          match Expr.noReturnEffectStmtCore? storageNames expr with
          | some effect => some effect
          | none => do
              let coreExpr ← Expr.toCore? storageNames expr
              some (SolidCore.Solidity.Source.Stmt.exprStmt coreExpr)
      | Stmt.ifElse cond thenBranch elseBranch => do
          let condCore ← Expr.toCore? storageNames cond
          let thenCore ← Stmt.lowerCore? internalFuel none storageNames thenBranch
          let elseCore ←
            match elseBranch with
            | some stmt => Stmt.lowerCore? internalFuel none storageNames stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          some (SolidCore.Solidity.Source.Stmt.ifElse condCore thenCore elseCore)
      | Stmt.whileLoop cond body => do
          let condCore ← Expr.toCore? storageNames cond
          let bodyCore ← Stmt.lowerCore? internalFuel none storageNames body
          some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
      | Stmt.doWhile body cond => do
          let bodyCore ← Stmt.lowerCore? internalFuel none storageNames body
          let condCore ← Expr.toCore? storageNames cond
          some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
      | Stmt.forLoop init cond post body => do
          let initCore ←
            match init with
            | some stmt => Stmt.lowerCore? internalFuel none storageNames stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let condCore ←
            match cond with
            | some expr => Expr.toCore? storageNames expr
            | none => some (SolidCore.Solidity.Source.Expr.word 1)
          let postCore ←
            match post with
            | some expr => Stmt.lowerCore? internalFuel none storageNames (Stmt.expr expr)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let bodyCore ← Stmt.lowerCore? internalFuel none storageNames body
          some (SolidCore.Solidity.Source.Stmt.forLoop initCore condCore postCore bodyCore)
      | Stmt.tryCatch expr clauses => do
          match Expr.toExternalCall? storageNames expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) => do
              let catchCore ← CatchClause.listLowerCore? internalFuel none storageNames clauses
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv [] [] expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode [] []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
          | none => do
              let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                Expr.toContractCreation? storageNames expr
              let catchCore ← CatchClause.listLowerCore? internalFuel none storageNames clauses
              some
                (SolidCore.Solidity.Source.Stmt.tryContractCreate
                  contractName argsCore valueCore saltCore? valueBeforeSalt []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
      | Stmt.tryCatchReturns expr returns success clauses => do
          let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
          let returnAbiCleanups ←
            Tys.toCoreAbiCleanups? (returns.map Parameter.ty)
          match Expr.toExternalCall? storageNames expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) => do
              let successCore ← Stmt.lowerCore? internalFuel none storageNames success
              let catchCore ← CatchClause.listLowerCore? internalFuel none storageNames clauses
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv []
                  (returns.map Parameter.ty) expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode returnBindings returnAbiCleanups
                  successCore catchCore)
          | none => do
              let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                Expr.toContractCreation? storageNames expr
              let successCore ← Stmt.lowerCore? internalFuel none storageNames success
              let catchCore ← CatchClause.listLowerCore? internalFuel none storageNames clauses
              some
                (SolidCore.Solidity.Source.Stmt.tryContractCreate
                  contractName argsCore valueCore saltCore? valueBeforeSalt returnBindings
                  successCore catchCore)
      | Stmt.emitEvent (Expr.call (Expr.ident name) args) => do
          -- EMIT-STORAGE-DYNAMIC-ARRAY (#192 follow-up): an event argument is a
          -- value-use boundary — `EventDecl.encodeFields?` ABI-encodes the
          -- argument CONTENTS and cannot read storage. A bare state
          -- bytes/string/array/struct lowers to `Expr.storage key` (eval = the
          -- HEADER word) → encode fails → `Panic(0)`. Materialize each arg exactly
          -- like the other value-use boundaries (abi.encode*/keccak256/…); every
          -- other core shape passes through untouched.
          let coreArgs ← Args.toCoreExprs? storageNames args
          some
            (SolidCore.Solidity.Source.Stmt.emitEvent name
              coreArgs)
      -- EMIT-QUAL (#74): a qualified event emit `emit Base.E(a)` / `emit C.E(a)` has
      -- a member-access callee; it lowers to the bare name (resolved against the
      -- contract's flattened in-scope events plus the added library events).
      -- QUALIFIED-COLLISION (#137): when the callee name is AMBIGUOUS (a library
      -- event shares the name with a differently-signed contract event), an earlier
      -- collision-aware pass (`Stmt.qualifyCollidingEventErrors`) has already
      -- rewritten this member callee to a bare identifier carrying the `.`-joined
      -- `qualifiedConstantKey`, so non-ambiguous qualified emits stay byte-identical
      -- and only the ambiguous ones key by the joined path.
      | Stmt.emitEvent
          (Expr.call (Expr.member _ name) args) => do
          let coreArgs ← Args.toCoreExprs? storageNames args
          some
            (SolidCore.Solidity.Source.Stmt.emitEvent name
              coreArgs)
      | Stmt.revertCall (Expr.call (Expr.ident "revert") []) =>
          some (SolidCore.Solidity.Source.Stmt.revertError none)
      | Stmt.revertCall
          (Expr.call (Expr.ident "revert")
            [Arg.positional (Expr.literal (Literal.string reason))]) =>
          some (SolidCore.Solidity.Source.Stmt.revertError (some reason))
      | Stmt.revertCall
          (Expr.call (Expr.ident "revert") [Arg.positional reason]) => do
          let reasonCore ← Expr.toCore? storageNames reason
          some (SolidCore.Solidity.Source.Stmt.revertErrorExpr reasonCore)
      | Stmt.revertCall (Expr.call (Expr.ident name) args) => do
          -- REVERT-CUSTOM-ERROR-STORAGE-STRING (#192 follow-up): a custom-error
          -- revert argument is a value-use boundary — the argument CONTENTS are
          -- ABI-encoded into the revert data (exactly like emit/abi.encode*/
          -- keccak256). A bare state bytes/string/array lowers to `Expr.storage
          -- key` (eval = the HEADER word) → the error encoder's `asBytes?`/
          -- `abiEncodeValues?` returns `none` → `Panic(0)`. Materialize each arg
          -- like the other value-use boundaries; every other core passes through.
          let coreArgs ← Args.toCoreExprs? storageNames args
          some
            (SolidCore.Solidity.Source.Stmt.revert name
              coreArgs)
      -- REVERT-QUAL (#77): a base-/self-/library-qualified custom-error revert
      -- `revert X.Err(a)` lowers to the bare name (resolved against the contract's
      -- flattened errors plus the added library errors). QUALIFIED-COLLISION (#136):
      -- when the callee name is AMBIGUOUS (a library error shares the name with a
      -- differently-signed contract error), an earlier collision-aware pass
      -- (`Stmt.qualifyCollidingEventErrors`) has already rewritten this member callee
      -- to a bare identifier carrying the `.`-joined `qualifiedConstantKey`, so
      -- non-ambiguous qualified reverts stay byte-identical and only the ambiguous
      -- ones key by the joined path.
      | Stmt.revertCall
          (Expr.call (Expr.member _ name) args) => do
          let coreArgs ← Args.toCoreExprs? storageNames args
          some
            (SolidCore.Solidity.Source.Stmt.revert name
              coreArgs)
      | Stmt.returnValues
          (some
            (Expr.call
              (Expr.ident "__solidcore_internal_function_pointer_panic") [])) =>
          some
            (SolidCore.Solidity.Source.Stmt.panic
              internalFunctionPointerPanicCode)
      | Stmt.returnValues none => some (SolidCore.Solidity.Source.Stmt.returnValues [])
      | Stmt.returnValues
          (some
            (Expr.call (Expr.member (Expr.ident "abi") "decode")
              [Arg.positional data, Arg.positional typesExpr])) => do
          let (tys, cleanups, dataCore) ←
            Expr.toAbiDecode? storageNames data typesExpr
          some
            (SolidCore.Solidity.Source.Stmt.returnValues
              (abiDecodeReturnExprs tys cleanups dataCore))
      | Stmt.returnValues (some (Expr.tuple items)) => do
          let coreExprs ← TupleItems.toCoreExprs? storageNames items
          some (SolidCore.Solidity.Source.Stmt.returnValues coreExprs)
      | Stmt.returnValues (some expr) => do
          match Expr.noReturnEffectStmtCore? storageNames expr with
          | some effect => some (CoreStmt.thenReturnEmpty effect)
          | none => do
              let coreExpr ← Expr.toCore? storageNames expr
              some (SolidCore.Solidity.Source.Stmt.returnValues [coreExpr])
      | _ => none
termination_by ((if ctx?.isSome then 3 else 0), internalFuel, sizeOf stmt, 9)

def Stmt.toCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty) (stmt : Stmt) :
    Option CoreStmt :=
  Stmt.lowerCore? internalFuel
    (some ⟨storageRefEnv, env, externalCallKindEnv, modifiers,
        functions, freeFunctions, returnTys⟩)
    storageNames stmt
termination_by (3, internalFuel, sizeOf stmt, 10)

def Stmt.toCore? (storageNames : List Name) (stmt : Stmt) : Option CoreStmt :=
  Stmt.lowerCore? 0 none storageNames stmt
termination_by (0, 0, sizeOf stmt, 10)

def Stmt.listLowerCore? (internalFuel : Nat) (ctx? : Option StmtLoweringCtx)
    (storageNames : List Name) (stmts : List Stmt) : Option (List CoreStmt) :=
  match ctx? with
  | some ctx =>
      let storageRefEnv := ctx.storageRefEnv
      let env := ctx.env
      let externalCallKindEnv := ctx.externalCallKindEnv
      let modifiers := ctx.modifiers
      let functions := ctx.functions
      let freeFunctions := ctx.freeFunctions
      let returnTys := ctx.returnTys
      -- SHADOW-LOCAL (soundness): see the companion note in `Stmt.lowerCore?` and
      -- `TypeEnv.shadowedStateNames` — drop names a nearer local shadows so the
      -- shadowed identifier lowers as that local, re-derived from the current
      -- `env` (extended per varDecl as the list is threaded) to respect scoping.
      let storageNames :=
        stateNamesExcludingBound (TypeEnv.shadowedStateNames env) storageNames
      (match stmts with
      | [] => some []
      | Stmt.expr (Expr.assign (Expr.ident name) AssignOp.assign rhs) :: rest =>
          let directStorageReturnCall? : Option (List CoreStmt) :=
            if StorageRefEnv.isStorageRef storageRefEnv name then
              match rhs with
              | Expr.call (Expr.ident callee) args =>
                  FunctionDecl.internalSingleStorageReturnRefCorePieces?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions callee args
                    (fun retName =>
                      SolidCore.Solidity.Source.Stmt.storageAliasAssignFrom
                        name retName)
              | _ => none
            else
              none
          match directStorageReturnCall? with
          | some heads => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys rest
              some (heads ++ tail)
          | none =>
          -- R3 (#188): the alias-ASSIGN intercept accepts ANY storage-reference
          -- RHS shape (bare ident as before, plus indexed/member paths — the
          -- storage-pointer-return rewrite shape). Non-storage assignments fall
          -- through to the generic lowering unchanged.
          match
              storageAliasChainedAssignCore?
                storageRefEnv env storageNames name rhs with
          | some heads => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  storageRefEnv env externalCallKindEnv storageNames modifiers functions
                  freeFunctions returnTys rest
              some (heads ++ tail)
          | none =>
              let generic : Option (List CoreStmt) := do
                let head ←
                  Stmt.toCoreWithInternalCalls?
                    (internalFuel := internalFuel)
                    (storageRefEnv := storageRefEnv)
                    (env := env)
                    (externalCallKindEnv := externalCallKindEnv)
                    (storageNames := storageNames)
                    (modifiers := modifiers)
                    (functions := functions)
                    (freeFunctions := freeFunctions)
                    (returnTys := returnTys)
                    (stmt := Stmt.expr
                      (Expr.assign (Expr.ident name) AssignOp.assign rhs))
                let tail ←
                  Stmt.listToCoreWithInternalCallsWithRefs?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions returnTys rest
                some (head :: tail)
              -- A call nested in the RHS storage path must be hoisted as a
              -- sibling. Wrapping the residual rebind in a block discards the
              -- updated storage-pointer binding when that block exits.
              if StorageRefEnv.isStorageRef storageRefEnv name then
                match internalFuel with
                | fuel + 1 =>
                    match Expr.argPositionHoistPrefix? fuel storageRefEnv env
                        externalCallKindEnv storageNames modifiers functions
                        freeFunctions rhs with
                    | some (prefixStmts@(_ :: _), residual) =>
                        match Stmt.listToCoreWithInternalCallsWithRefs? fuel
                            storageRefEnv env externalCallKindEnv storageNames
                            modifiers functions freeFunctions returnTys
                            (Stmt.expr
                              (Expr.assign (Expr.ident name) AssignOp.assign residual)
                              :: rest) with
                        | some lowered => some (prefixStmts ++ lowered)
                        | none => generic
                    | _ => generic
                | 0 => generic
              else
                generic
      | Stmt.varDecl [binding]
          (some (Expr.call (Expr.member target "push") [])) :: rest =>
          match storageArrayPushReturnAliasCore? storageNames binding target with
          | some (pushStmt, aliasStmt) => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (pushStmt :: aliasStmt :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding]
                    (some (Expr.call (Expr.member target "push") [])))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some (Expr.ident source)) :: rest =>
          match storageAliasDeclFromRefCore? storageRefEnv binding source with
          | some head => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some (Expr.ident source)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some source@(Expr.member _ _)) :: rest =>
          match
              storageAliasDeclFromRefPathCore?
                storageRefEnv env storageNames binding source with
          | some head => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some source))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some source@(Expr.index _ _)) :: rest =>
          match
              storageAliasDeclFromRefPathCore?
                storageRefEnv env storageNames binding source with
          | some head => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
          | none =>
              match storageVarDeclArgPositionHoistPieces? internalFuel
                  storageRefEnv env externalCallKindEnv storageNames modifiers
                  functions freeFunctions binding source with
              | some pieces => do
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv storageNames modifiers functions
                      freeFunctions returnTys rest
                  some (pieces ++ tail)
              | none =>
              -- OVERREJECT-CALLPOS-BATCH (B): `T x = m[f()]` — an internal call used
              -- as a mapping/array INDEX in a varDecl initializer. The pure varDecl
              -- lowering has no internal-call fallback for the index operand, so
              -- this used to over-reject. Hoist the index call (via the single-
              -- return expression hoister's `Expr.index base (call)` arm) into a
              -- prefix statement and assign the read to the local. The local's decl
              -- is emitted as a SIBLING in the enclosing statement list (never a
              -- self-scoping sub-block) so it stays in scope for later statements;
              -- solc's declare-then-initialise order and `m[f()]` base-then-index
              -- order (base is a pure reference) are preserved. A non-call index or
              -- a base containing a call makes the hoister return `none`, falling
              -- back to the pure varDecl lowering — no behaviour change.
              match binding.name with
              | some localName =>
                  match (do
                      let (name, args, indexes) ←
                        Expr.callRootedIndexSpine? source
                      let indexCores ←
                        mapOption (Expr.toCore? storageNames) indexes
                      FunctionDecl.internalSingleStorageReturnRefCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions name args
                        (fun retName =>
                          let readCore :=
                            indexCores.foldl
                              (fun base index =>
                                SolidCore.Solidity.Source.Expr.index base index)
                              (SolidCore.Solidity.Source.Expr.var retName)
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (match binding.ty with
                            | some targetTy =>
                                Ty.implicitCleanupCore targetTy readCore
                            | none => readCore))) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv storageNames modifiers functions
                          freeFunctions returnTys rest
                      some (declCore :: assignBlock :: tail)
                  | none =>
                  match FunctionDecl.internalExprSingleReturnUseCore?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions source
                      (fun resultExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          (match binding.ty with
                          | some targetTy =>
                              Ty.implicitCleanupCore targetTy resultExpr
                          | none => resultExpr)) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (declCore :: assignBlock :: tail)
                  | none => do
                      let head ←
                        Stmt.toCoreWithInternalCalls?
                          (internalFuel := internalFuel)
                          (storageRefEnv := storageRefEnv)
                          (env := env)
                          (externalCallKindEnv := externalCallKindEnv)
                          (storageNames := storageNames)
                          (modifiers := modifiers)
                          (functions := functions)
                          (freeFunctions := freeFunctions)
                          (returnTys := returnTys)
                          (stmt := Stmt.varDecl [binding] (some source))
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (head :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := env)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := Stmt.varDecl [binding] (some source))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
      | Stmt.varDecl [binding]
          (some source@(Expr.call (Expr.call _ _) _)) :: rest =>
          -- Keep the declared local in the enclosing statement-list scope while
          -- hoisting an immediate call through a returned internal function
          -- pointer. Wrapping declaration and assignment in the single-statement
          -- block would make the local unavailable to the remaining statements.
          match binding.name with
          | some localName =>
              match FunctionDecl.internalExprSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions source
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (match binding.ty with
                      | some targetTy =>
                          Ty.implicitCleanupCore targetTy resultExpr
                      | none => resultExpr)) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv storageNames modifiers functions
                      freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys
                      (Stmt.varDecl [binding] (some source))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv storageNames modifiers functions
                      freeFunctions returnTys rest
                  some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys
                  (Stmt.varDecl [binding] (some source))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv storageNames modifiers functions
                  freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) :: rest => do
          let pieces? : Option (List CoreStmt) :=
            match storageTupleDeclAllPiecesWithEnv? internalFuel storageRefEnv env
                externalCallKindEnv storageNames modifiers functions freeFunctions
                bindings items with
            | some decls => some decls
            | none =>
            match (if TupleItems.anyAbiArgNeedsEnvCleanup items then do
                if bindings.length == items.length then some () else none
                let tys ←
                  VarBindings.tupleDeclItemTysWithEnv?
                    functions freeFunctions env bindings items
                let coreDecls ← VarBindings.toCoreTupleDecls? bindings
                let targets ← VarBindings.toCoreTupleTargets? bindings
                let body ←
                  FunctionDecl.tupleItemsUseCoreWithInternalCalls?
                    internalFuel storageRefEnv env externalCallKindEnv
                    storageNames modifiers functions freeFunctions
                    "_sol_tuple_decl_cleanup" 0 tys items
                    (fun coreExprs =>
                      SolidCore.Solidity.Source.Stmt.assignTuple targets
                        (SolidCore.Solidity.Source.Expr.tuple coreExprs))
                some (coreDecls ++ [body])
              else none) with
            | some pieces => some pieces
            | none =>
            -- FB1: `(bytesN x, …) = (b << k, …)` decl form — same lane-cleanup
            -- reroute as the tuple-assignment arm (see `tupleAssignBitAwareCore?`).
            -- The literal-tuple decl lowering below (`tupleVarDeclCorePieces?` via
            -- env-less `Expr.toCore?`) drops the mask; fire only when a mask is
            -- inserted, otherwise keep the unchanged path.
            match tupleVarDeclBitAwarePieces? storageNames env bindings items with
            | some pieces => some pieces
            | none =>
            match tupleVarDeclCorePieces? storageNames bindings items with
            | some (coreDecls, assigns) => some (coreDecls ++ assigns)
            | none => do
                -- Stage B (boundary-completion arc), declaration form:
                -- `(uint a, uint b) = (f(), g())`. Same left-to-right hoisting as
                -- the assignment form (`docs/refs-completion-solc-research.md` §4);
                -- the declared binding types are the component target types. The
                -- decls are emitted at LIST level (they must survive for the
                -- following statements); component name resolution is settled at
                -- elaboration against the OUTER env (the bindings extend the env
                -- only for `rest`), so emission order cannot capture. Anonymous
                -- (hole) bindings still evaluate their component.
                if bindings.length == items.length then some () else none
                let tys ←
                  VarBindings.tupleDeclItemTysWithEnv? functions freeFunctions env
                    bindings items
                let coreDecls ← VarBindings.toCoreTupleDecls? bindings
                let targets ← VarBindings.toCoreTupleTargets? bindings
                let hoisted ←
                  FunctionDecl.tupleItemsUseCoreWithInternalCalls?
                    internalFuel storageRefEnv env externalCallKindEnv storageNames
                    modifiers functions freeFunctions "_sol_tuple_decl_item"
                    0 tys items
                    (fun coreExprs =>
                      SolidCore.Solidity.Source.Stmt.assignTuple targets
                        (SolidCore.Solidity.Source.Expr.tuple coreExprs))
                some (coreDecls ++ [hoisted])
          let pieces ← pieces?
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBindings.extendStorageRefEnv storageRefEnv bindings)
              (VarBindings.extendTypeEnv env bindings)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (pieces ++ tail)
      | Stmt.varDecl [binding]
          (some (Expr.ternary cond thenExpr elseExpr)) :: rest =>
          -- G#116 (TERNARY-STORAGE-STATELVALUE): `T storage p = b ? s0 : s1;` — a
          -- storage-pointer local initialized from a conditional of two storage
          -- references. Lower to an `ifElse` selecting the branch's storage alias so
          -- `p` aliases the SELECTED state var at runtime. Only fires for a
          -- `storage`-located binding whose branches are storage references; value /
          -- memory ternaries fall through to the branch-assignment lowering below.
          match
              storageAliasDeclFromTernaryCore?
                storageRefEnv env storageNames binding cond thenExpr elseExpr with
          | some head => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
          | none =>
          match storageTernaryConditionAliasPieces? internalFuel storageRefEnv env
              externalCallKindEnv storageNames modifiers functions freeFunctions
              binding cond thenExpr elseExpr with
          | some pieces => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv storageNames modifiers functions
                  freeFunctions returnTys rest
              some (pieces ++ tail)
          | none =>
          match storageTernaryBranchAliasPieces? internalFuel storageRefEnv env
              externalCallKindEnv storageNames modifiers functions freeFunctions
              binding cond thenExpr elseExpr with
          | some pieces => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv storageNames modifiers functions
                  freeFunctions returnTys rest
              some (pieces ++ tail)
          | none =>
          match binding.name with
          | some localName =>
              let targetTy? := binding.ty
              let conditionBranchAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions thenExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (Ty.implicitCleanupCore targetTy resultExpr))
                let elseCore ←
                  match Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr with
                  | some branchCore =>
                      some
                        (SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          branchCore)
                  | none =>
                      FunctionDecl.internalExprSingleReturnUseCore?
                        internalFuel storageRefEnv env externalCallKindEnv
                        storageNames modifiers functions freeFunctions elseExpr
                        (fun resultExpr =>
                          SolidCore.Solidity.Source.Stmt.assign
                            (SolidCore.Solidity.Source.LValue.var localName)
                            (Ty.implicitCleanupCore targetTy resultExpr))
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.ifElse
                      condCore thenCore elseCore)
              let conditionAssign? : Option CoreStmt := do
                let targetTy ← targetTy?
                let thenCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy thenExpr
                let elseCore ←
                  Expr.toCoreAsWithEnv? storageNames env targetTy elseExpr
                FunctionDecl.conditionUseCoreWithInternalCalls?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond
                  (fun condCore =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      (SolidCore.Solidity.Source.Expr.ternary
                        condCore thenCore elseCore))
              match conditionBranchAssign? with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none =>
                  match conditionAssign? with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (declCore :: assignBlock :: tail)
                  | none =>
                  match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
                      internalFuel storageRefEnv env externalCallKindEnv storageNames
                      modifiers functions freeFunctions cond thenExpr elseExpr
                      (fun resultExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          (match targetTy? with
                          | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                          | none => resultExpr)) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (declCore :: assignBlock :: tail)
                  | none =>
                      match FunctionDecl.internalTernaryBranchSingleReturnUseCore?
                          internalFuel storageRefEnv env externalCallKindEnv storageNames
                          modifiers functions freeFunctions cond thenExpr elseExpr
                          (fun resultExpr =>
                            SolidCore.Solidity.Source.Stmt.assign
                              (SolidCore.Solidity.Source.LValue.var localName)
                              (match targetTy? with
                              | some targetTy => Ty.implicitCleanupCore targetTy resultExpr
                              | none => resultExpr)) with
                      | some assignBlock => do
                          let declCore ←
                            Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                          let tail ←
                            Stmt.listToCoreWithInternalCallsWithRefs?
                              internalFuel
                              (VarBinding.extendStorageRefEnv storageRefEnv binding)
                              (VarBinding.extendTypeEnv env binding)
                              externalCallKindEnv
                              storageNames modifiers functions freeFunctions returnTys rest
                          some (declCore :: assignBlock :: tail)
                      | none => do
                          let head ←
                            Stmt.toCoreWithInternalCalls?
                              (internalFuel := internalFuel)
                              (storageRefEnv := storageRefEnv)
                              (env := env)
                              (externalCallKindEnv := externalCallKindEnv)
                              (storageNames := storageNames)
                              (modifiers := modifiers)
                              (functions := functions)
                              (freeFunctions := freeFunctions)
                              (returnTys := returnTys)
                              (stmt := Stmt.varDecl [binding]
                                (some (Expr.ternary cond thenExpr elseExpr)))
                          let tail ←
                            Stmt.listToCoreWithInternalCallsWithRefs?
                              internalFuel
                              (VarBinding.extendStorageRefEnv storageRefEnv binding)
                              (VarBinding.extendTypeEnv env binding)
                              externalCallKindEnv
                              storageNames modifiers functions freeFunctions returnTys rest
                          some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding]
                    (some (Expr.ternary cond thenExpr elseExpr)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some (Expr.unary op expr)) :: rest =>
          match binding.name with
          | some localName =>
              match FunctionDecl.internalUnarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op expr
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      resultExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := env)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := Stmt.varDecl [binding]
                        (some (Expr.unary op expr)))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding]
                    (some (Expr.unary op expr)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding]
          (some (Expr.call (Expr.typeName targetTy)
            [Arg.positional inner])) :: rest =>
          match binding.name with
          | some localName =>
              match FunctionDecl.internalTypeConversionSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions targetTy inner
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      resultExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := env)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := Stmt.varDecl [binding]
                        (some
                          (Expr.call (Expr.typeName targetTy)
                            [Arg.positional inner])))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding]
                    (some
                      (Expr.call (Expr.typeName targetTy)
                        [Arg.positional inner])))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some (Expr.binary op lhs rhs)) :: rest =>
          match binding.name with
          | some localName =>
              match FunctionDecl.internalBinarySingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions op lhs rhs
                  (fun resultExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      resultExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := env)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := Stmt.varDecl [binding]
                        (some (Expr.binary op lhs rhs)))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
          | none => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding]
                    (some (Expr.binary op lhs rhs)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some expr@(Expr.call (Expr.member _ _) _)) :: rest =>
          match binding.name, binding.ty with
          | some localName, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none =>
                  -- ABI-ENCODE-INTERNAL-CALL-ARG (#174), var-decl position:
                  -- `bytes memory b = abi.encode(g());` (and `abi.encodePacked`/… with
                  -- a nested internal call, incl. wrappers like
                  -- `abi.encode(uint256(g()) + 1)`). The external-call path above
                  -- fails (abi.* is a builtin, not an external call) and the per-
                  -- statement lowering below routes `abi.*` through the env-less
                  -- `Stmt.toCore?`, which cannot lower a nested internal call — so the
                  -- declaration over-rejected (poisoning the contract's executable
                  -- lowering). Peel the strictly-nested internal call into ordered
                  -- SIBLING prefix temps (so the declared local stays in scope for
                  -- later statements) and re-lower the residual
                  -- `abi.encode((retTy)(_tmp))` declaration through the list — which
                  -- reaches the per-statement env-less lowering cleanly (a pure-local
                  -- abi arg). Fires only when a nested call is actually hoisted;
                  -- otherwise the prefix is empty and we fall back to `generic`
                  -- (byte-identical to the prior handling).
                  let generic : Option (List CoreStmt) := do
                    let head ←
                      Stmt.toCoreWithInternalCalls?
                        (internalFuel := internalFuel)
                        (storageRefEnv := storageRefEnv)
                        (env := env)
                        (externalCallKindEnv := externalCallKindEnv)
                        (storageNames := storageNames)
                        (modifiers := modifiers)
                        (functions := functions)
                        (freeFunctions := freeFunctions)
                        (returnTys := returnTys)
                        (stmt := Stmt.varDecl [binding] (some expr))
                    let tail ←
                      Stmt.listToCoreWithInternalCallsWithRefs?
                        internalFuel
                        (VarBinding.extendStorageRefEnv storageRefEnv binding)
                        (VarBinding.extendTypeEnv env binding)
                        externalCallKindEnv
                        storageNames modifiers functions freeFunctions returnTys rest
                    some (head :: tail)
                  -- STAGE-D #174 (concat parity): a `bytes.concat`/`string.concat`
                  -- var-decl initializer nesting a value-returning call
                  -- (`string memory s = string.concat("a", f());`) is not an
                  -- external call, so the branch above declines; and like `abi.*`
                  -- the per-statement env-less concat lowering cannot lower a
                  -- nested internal call, so `generic` over-rejects (or mis-lowers)
                  -- the declaration. Peel the strictly-nested call into ordered
                  -- SIBLING prefix temps exactly as the `abi.*` arm does and
                  -- re-lower the residual `string.concat("a", (retTy)(_tmp))`
                  -- declaration through the list.
                  match expr, internalFuel with
                  | Expr.call (Expr.member (Expr.ident "abi") _) _, fuel + 1
                  | Expr.call (Expr.member (Expr.ident "bytes") "concat") _, fuel + 1
                  | Expr.call (Expr.member (Expr.typeName Ty.bytes) "concat") _, fuel + 1
                  | Expr.call (Expr.member (Expr.ident "string") "concat") _, fuel + 1
                  | Expr.call (Expr.member (Expr.typeName Ty.string) "concat") _, fuel + 1 =>
                      match Expr.argPositionHoistPrefix? fuel storageRefEnv env
                          externalCallKindEnv storageNames modifiers functions
                          freeFunctions expr with
                      | some (prefixStmts@(_ :: _), residualExpr) =>
                          (match
                              Stmt.listToCoreWithInternalCallsWithRefs? fuel
                                storageRefEnv env externalCallKindEnv storageNames
                                modifiers functions freeFunctions returnTys
                                (Stmt.varDecl [binding] (some residualExpr) :: rest) with
                          | some spliced => some (prefixStmts ++ spliced)
                          | none => generic)
                      | _ => generic
                  | _, _ => generic
          | _, _ => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding]
          (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) :: rest =>
          match binding.name, binding.ty with
          | some localName, some expectedTy =>
              match Expr.externalCallSingleReturnCoreWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv expectedTy expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCoreWithInternalCalls?
                      (internalFuel := internalFuel)
                      (storageRefEnv := storageRefEnv)
                      (env := env)
                      (externalCallKindEnv := externalCallKindEnv)
                      (storageNames := storageNames)
                      (modifiers := modifiers)
                      (functions := functions)
                      (freeFunctions := freeFunctions)
                      (returnTys := returnTys)
                      (stmt := Stmt.varDecl [binding] (some expr))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
          | _, _ => do
              let head ←
                Stmt.toCoreWithInternalCalls?
                  (internalFuel := internalFuel)
                  (storageRefEnv := storageRefEnv)
                  (env := env)
                  (externalCallKindEnv := externalCallKindEnv)
                  (storageNames := storageNames)
                  (modifiers := modifiers)
                  (functions := functions)
                  (freeFunctions := freeFunctions)
                  (returnTys := returnTys)
                  (stmt := Stmt.varDecl [binding] (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding]
          (some expr@(Expr.call (Expr.ident name) args)) :: rest =>
          -- #201 (B): a HASH-builtin initializer with a flagged argument
          -- (`bytes32 h = keccak256(abi.encodePacked(a + b))`, `uint8 a,b`) —
          -- list form of the per-statement fix: this arm bottoms out in the
          -- env-less `Stmt.toCore?` WITHOUT consulting the per-statement
          -- dispatcher, so the vardecl fell env-less (hashing 300). `name` is a
          -- builtin, never a user function, when the flag fires; everything else
          -- keeps the chain below byte-identically.
          match (if Expr.abiBuiltinArgsNeedEnvCleanup expr then
              varDeclCoreWithEnv? storageNames env binding expr
            else none) with
          | some head => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
          | none =>
          -- Named-argument order (R1): reorder NAMED arguments into the callee's
          -- parameter-declaration order (as positional) BEFORE the direct-arg
          -- hoister (`hoistDirectInternalCallArgs?`) lifts their nested calls
          -- into `_sol_vardecl_arg_eval*` temps, so `g({b: t(1), a: t(2)})`
          -- evaluates the `a` expression `t(2)` first (solc reorders named args
          -- to parameter order, then evaluates L2R). Binding was already correct
          -- via `orderedArgs?`; positional calls are unchanged.
          let args := Expr.reorderNamedInternalCallArgs functions freeFunctions
            env (Expr.ident name) args
          match binding.name with
          | some localName =>
              match binding.location with
              | some DataLocation.storage =>
                  match FunctionDecl.internalSingleStorageReturnRefCorePieces?
                      internalFuel storageRefEnv env externalCallKindEnv
                      storageNames modifiers functions freeFunctions name args
                      (fun retName =>
                        SolidCore.Solidity.Source.Stmt.storageAliasFrom
                          localName retName) with
                  | some assignPieces => do
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (assignPieces ++ tail)
                  | none => do
                      let head ←
                        Stmt.toCore? storageNames
                          (Stmt.varDecl [binding]
                            (some (Expr.call (Expr.ident name) args)))
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (head :: tail)
              | _ =>
                  match Expr.externalFunctionValueCallSingleReturnCore?
                      storageNames env expr
                      (fun retExpr =>
                        SolidCore.Solidity.Source.Stmt.assign
                          (SolidCore.Solidity.Source.LValue.var localName)
                          retExpr) with
                  | some assignBlock => do
                      let declCore ←
                        Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                      let tail ←
                        Stmt.listToCoreWithInternalCallsWithRefs?
                          internalFuel
                          (VarBinding.extendStorageRefEnv storageRefEnv binding)
                          (VarBinding.extendTypeEnv env binding)
                          externalCallKindEnv
                          storageNames modifiers functions freeFunctions returnTys rest
                      some (declCore :: assignBlock :: tail)
                  | none => do
                      match FunctionDecl.internalSingleReturnCallCore?
                          internalFuel storageRefEnv env externalCallKindEnv
                          storageNames modifiers functions freeFunctions name args
                          (fun retExpr =>
                            SolidCore.Solidity.Source.Stmt.assign
                              (SolidCore.Solidity.Source.LValue.var localName)
                              retExpr) with
                      | some assignBlock => do
                          let declCore ←
                            Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                          let tail ←
                            Stmt.listToCoreWithInternalCallsWithRefs?
                              internalFuel
                              (VarBinding.extendStorageRefEnv storageRefEnv binding)
                              (VarBinding.extendTypeEnv env binding)
                              externalCallKindEnv
                              storageNames modifiers functions freeFunctions returnTys rest
                          some (declCore :: assignBlock :: tail)
                      | none =>
                          match FunctionDecl.abiInternalSingleReturnUseCore?
                              internalFuel storageRefEnv env externalCallKindEnv
                              storageNames modifiers functions freeFunctions
                              "_sol_vardecl_abi_arg" expr
                              (fun replacedExpr =>
                                varDeclCoreWithEnv? storageNames env binding
                                  replacedExpr) with
                          | some coreStmt => do
                              let tail ←
                                Stmt.listToCoreWithInternalCallsWithRefs?
                                  internalFuel
                                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                                  (VarBinding.extendTypeEnv env binding)
                                  externalCallKindEnv
                                  storageNames modifiers functions freeFunctions
                                  returnTys rest
                              some (coreStmt :: tail)
                          | none =>
                              -- OVERREJECT-CALLPOS-BATCH (A) + CALLPOS-FAMILY:
                              -- `T x = outer(inner())`, `T x = f(g(), h())`,
                              -- `T x = f(g(h()))` — a direct internal call whose
                              -- arguments contain direct internal calls (one, many,
                              -- or nested). `internalSingleReturnCallCore?` above
                              -- fails because the pure per-arg lowering
                              -- (`boundaryArgDecls?`) cannot lower a call argument.
                              -- Hoist EVERY call argument into ordered prefix temps
                              -- (`hoistDirectInternalCallArgs?`, solc left-to-right /
                              -- inner-before-outer order, verified via `--ir`), then
                              -- re-lower the outer call against the temp-substituted
                              -- argument list. The temps and the local's decl are
                              -- spliced as SIBLINGS in the enclosing statement list
                              -- (never a self-scoping sub-block) so the local stays
                              -- in scope for later statements.
                              match (do
                                  let (prefixPieces, tempEnv, replacedArgs) ←
                                    FunctionDecl.hoistDirectInternalCallArgs?
                                      internalFuel storageRefEnv env
                                      externalCallKindEnv storageNames modifiers
                                      functions freeFunctions "_sol_vardecl_arg" args
                                  let declCore ←
                                    Stmt.toCore? storageNames
                                      (Stmt.varDecl [binding] none)
                                  let assignCore ←
                                    FunctionDecl.internalSingleReturnCallCore?
                                      internalFuel storageRefEnv (tempEnv ++ env)
                                      externalCallKindEnv storageNames modifiers
                                      functions freeFunctions name replacedArgs
                                      (fun retExpr =>
                                        SolidCore.Solidity.Source.Stmt.assign
                                          (SolidCore.Solidity.Source.LValue.var
                                            localName)
                                          retExpr)
                                  some
                                    (prefixPieces ++ [declCore, assignCore])) with
                              | some pieces => do
                                  let tail ←
                                    Stmt.listToCoreWithInternalCallsWithRefs?
                                      internalFuel
                                      (VarBinding.extendStorageRefEnv storageRefEnv
                                        binding)
                                      (VarBinding.extendTypeEnv env binding)
                                      externalCallKindEnv
                                      storageNames modifiers functions freeFunctions
                                      returnTys rest
                                  some (pieces ++ tail)
                              | none =>
                                  -- CALL-IN-ABI-ENCODE-NESTED (var-decl, ident
                                  -- builtin callee): an initializer like
                                  -- `bytes32 k = keccak256(bytes.concat(abi.encode(f(), g())))`
                                  -- whose ident-headed builtin call transitively
                                  -- nests one or more internal calls in an
                                  -- argument-like position (here f()/g() buried
                                  -- under keccak256/bytes.concat/abi.encode). None
                                  -- of the specific arms above lower it (keccak256
                                  -- is a builtin, not a user/external call; the
                                  -- abi one-call peel needs a residual it can
                                  -- lower and stalls on the SECOND call), so it
                                  -- fell through to the env-less `Stmt.toCore?`,
                                  -- which cannot lower a nested internal call —
                                  -- the declaration over-rejected and poisoned the
                                  -- contract's executable lowering (replay Panics
                                  -- 0). Peel EVERY strictly-nested internal call
                                  -- into ordered SIBLING prefix temps (the generic
                                  -- arg-position hoister descends through arbitrary
                                  -- call wrappers and drains left-to-right, solc's
                                  -- evaluation order) and re-lower the residual
                                  -- (arg-position-call-free) declaration through
                                  -- the list so the local stays in scope for later
                                  -- statements. Fires only when a nested call is
                                  -- actually hoisted; otherwise the prefix is empty
                                  -- and we fall back to `generic` (byte-identical).
                                  let generic : Option (List CoreStmt) := do
                                    let head ←
                                      Stmt.toCore? storageNames
                                        (Stmt.varDecl [binding]
                                          (some (Expr.call (Expr.ident name) args)))
                                    let tail ←
                                      Stmt.listToCoreWithInternalCallsWithRefs?
                                        internalFuel
                                        (VarBinding.extendStorageRefEnv storageRefEnv
                                          binding)
                                        (VarBinding.extendTypeEnv env binding)
                                        externalCallKindEnv
                                        storageNames modifiers functions freeFunctions
                                        returnTys rest
                                    some (head :: tail)
                                  match internalFuel with
                                  | fuel + 1 =>
                                      match Expr.argPositionHoistPrefix? fuel storageRefEnv
                                          env externalCallKindEnv storageNames modifiers
                                          functions freeFunctions expr with
                                      | some (prefixStmts@(_ :: _), residualExpr) =>
                                          (match
                                              Stmt.listToCoreWithInternalCallsWithRefs? fuel
                                                storageRefEnv env externalCallKindEnv
                                                storageNames modifiers functions freeFunctions
                                                returnTys
                                                (Stmt.varDecl [binding] (some residualExpr)
                                                  :: rest) with
                                          | some spliced => some (prefixStmts ++ spliced)
                                          | none => generic)
                                      | _ => generic
                                  | 0 => generic
          | none => do
              let head ←
                Stmt.toCore? storageNames
                  (Stmt.varDecl [binding]
                    (some (Expr.call (Expr.ident name) args)))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding]
          (some expr@(Expr.callWithOptions (Expr.ident _) _ _)) :: rest =>
          match binding.name with
          | some localName =>
              match Expr.externalFunctionValueCallSingleReturnCore?
                  storageNames env expr
                  (fun retExpr =>
                    SolidCore.Solidity.Source.Stmt.assign
                      (SolidCore.Solidity.Source.LValue.var localName)
                      retExpr) with
              | some assignBlock => do
                  let declCore ←
                    Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (declCore :: assignBlock :: tail)
              | none => do
                  let head ←
                    Stmt.toCore? storageNames
                      (Stmt.varDecl [binding] (some expr))
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBinding.extendStorageRefEnv storageRefEnv binding)
                      (VarBinding.extendTypeEnv env binding)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (head :: tail)
          | none => do
              let head ←
                Stmt.toCore? storageNames
                  (Stmt.varDecl [binding] (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBinding.extendStorageRefEnv storageRefEnv binding)
                  (VarBinding.extendTypeEnv env binding)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
      | Stmt.varDecl [binding] (some expr@(Expr.call _ _)) :: rest => do
          let localName ← binding.name
          let expectedTy ← binding.ty
          let assignBlock ←
            FunctionDecl.internalExprSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions expr
              (fun retExpr =>
                SolidCore.Solidity.Source.Stmt.assign
                  (SolidCore.Solidity.Source.LValue.var localName)
                  (Ty.implicitCleanupCore expectedTy retExpr))
          let declCore ←
            Stmt.toCore? storageNames (Stmt.varDecl [binding] none)
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBinding.extendStorageRefEnv storageRefEnv binding)
              (VarBinding.extendTypeEnv env binding)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (declCore :: assignBlock :: tail)
      -- TUPLE-VARDECL-FROM-ABI-DECODE (#171): `(uint x, uint y) = abi.decode(...)`
      -- in DECLARATION position. This member-call varDecl arm is reached on the live
      -- (internal-call-aware) body path; `abi.decode` is neither a low-level nor an
      -- external call, so route it through the shared general tuple-decl lowering
      -- first (mirroring the tuple-ASSIGNMENT path) before the low-level/external
      -- handlers. (Non-decode member calls fall through to the arm below.)
      | Stmt.varDecl bindings
          (some expr@(Expr.call (Expr.member (Expr.ident "abi") "decode") _)) :: rest => do
          let pieces ←
            match tupleVarDeclGeneralCorePieces? storageNames bindings expr with
            | some (coreDecls, assigns) => some (coreDecls ++ assigns)
            | none =>
                match internalFuel with
                | 0 => none
                | fuel + 1 => do
                    let (prefixStmts, residual) ←
                      Expr.argPositionHoistPrefix? fuel storageRefEnv env
                        externalCallKindEnv storageNames modifiers functions
                        freeFunctions expr
                    match prefixStmts with
                    | [] => none
                    | _ :: _ => do
                        let (coreDecls, assigns) ←
                          tupleVarDeclGeneralCorePieces?
                            storageNames bindings residual
                        some (prefixStmts ++ coreDecls ++ assigns)
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBindings.extendStorageRefEnv storageRefEnv bindings)
              (VarBindings.extendTypeEnv env bindings)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (pieces ++ tail)
      | Stmt.varDecl bindings (some expr@(Expr.call (Expr.member _ _) _)) :: rest => do
          let callStmts ←
            match Expr.lowLevelTupleVarDeclCorePieces? storageNames env bindings expr with
            | some pieces => some pieces
            | none =>
                Expr.externalCallAssignBindingsCorePiecesWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv bindings expr
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBindings.extendStorageRefEnv storageRefEnv bindings)
              (VarBindings.extendTypeEnv env bindings)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (callStmts ++ tail)
      | Stmt.varDecl bindings
          (some expr@(Expr.callWithOptions (Expr.member _ _) _ _)) :: rest => do
          let callStmts ←
            match Expr.lowLevelTupleVarDeclCorePieces? storageNames env bindings expr with
            | some pieces => some pieces
            | none =>
                Expr.externalCallAssignBindingsCorePiecesWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
                  storageNames env externalCallKindEnv bindings expr
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBindings.extendStorageRefEnv storageRefEnv bindings)
              (VarBindings.extendTypeEnv env bindings)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (callStmts ++ tail)
      | Stmt.varDecl bindings
          (some expr@(Expr.call (Expr.ident name) args)) :: rest => do
          match FunctionDecl.internalVarDeclAssignReturnCallCorePieces?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args bindings with
          | some pieces => do
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs?
                  internalFuel
                  (VarBindings.extendStorageRefEnv storageRefEnv bindings)
                  (VarBindings.extendTypeEnv env bindings)
                  externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (pieces ++ tail)
          | none => do
              match FunctionDecl.internalTupleVarDeclAssignReturnCallCorePieces?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions name args bindings with
              | some pieces => do
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBindings.extendStorageRefEnv storageRefEnv bindings)
                      (VarBindings.extendTypeEnv env bindings)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (pieces ++ tail)
              | none => do
                  let callStmts ←
                    match Expr.externalFunctionValueCallAssignBindingsCorePieces?
                        storageNames env bindings expr with
                    | some pieces => some pieces
                    | none => do
                        let names ← VarBindings.names? bindings
                        let decls ← VarBindings.toCoreDecls? bindings
                        let callCore ←
                          FunctionDecl.internalAssignReturnCallCore?
                            internalFuel storageRefEnv env externalCallKindEnv
                            storageNames modifiers functions freeFunctions name args
                            names
                        some (decls ++ [callCore])
                  let tail ←
                    Stmt.listToCoreWithInternalCallsWithRefs?
                      internalFuel
                      (VarBindings.extendStorageRefEnv storageRefEnv bindings)
                      (VarBindings.extendTypeEnv env bindings)
                      externalCallKindEnv
                      storageNames modifiers functions freeFunctions returnTys rest
                  some (callStmts ++ tail)
      | Stmt.varDecl bindings
          (some expr@(Expr.callWithOptions (Expr.ident _) _ _)) :: rest => do
          let callStmts ←
            Expr.externalFunctionValueCallAssignBindingsCorePieces?
              storageNames env bindings expr
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              (VarBindings.extendStorageRefEnv storageRefEnv bindings)
              (VarBindings.extendTypeEnv env bindings)
              externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys rest
          some (callStmts ++ tail)
      | Stmt.varDecl bindings (some expr) :: rest =>
          -- GENERAL TUPLE-VARDECL (#172 ternary RHS and the general vein): a
          -- multi-binding tuple decl whose single-expression RHS is not a CALL shape
          -- (handled by the arms above) nor a literal tuple (handled earlier) — e.g.
          -- `(uint a, uint b) = c ? (1, 2) : (3, 4)`. Mirror the tuple-ASSIGNMENT
          -- path: SPLICE the declared locals as siblings (so they stay in scope for
          -- `rest`) followed by an `assignTuple` destructuring the lowered RHS. Falls
          -- back to the per-statement generic lowering when the RHS is not lowerable
          -- as one expression (e.g. it nests internal calls), preserving prior
          -- handling for those shapes.
          let tupleSplice : Option (List CoreStmt) :=
            match bindings with
            | _ :: _ :: _ => do
                let (coreDecls, assigns) ←
                  tupleVarDeclGeneralCorePieces? storageNames bindings expr
                let tail ←
                  Stmt.listToCoreWithInternalCallsWithRefs? internalFuel
                    (VarBindings.extendStorageRefEnv storageRefEnv bindings)
                    (VarBindings.extendTypeEnv env bindings) externalCallKindEnv
                    storageNames modifiers functions freeFunctions returnTys rest
                some (coreDecls ++ assigns ++ tail)
            | _ => none
          -- CALL-POSITION CONSOLIDATED (#148-#150): a variable declaration whose
          -- initializer nests value-returning calls in argument-like positions
          -- (array/struct-tuple element, `new`/constructor argument). Peel those
          -- calls into ordered sibling prefix temps, then re-lower the residual
          -- (arg-position-call-free) declaration through the list so the LOCAL's
          -- decl is spliced as a SIBLING and stays in scope for later statements.
          -- Fires only when a strictly-nested call is actually found; otherwise
          -- falls back to the generic per-statement lowering below (byte-identical).
          let fallback : Option (List CoreStmt) :=
            let generic : Option (List CoreStmt) := do
              let head ←
                Stmt.toCoreWithInternalCalls? internalFuel storageRefEnv env
                  externalCallKindEnv storageNames modifiers functions freeFunctions
                  returnTys (Stmt.varDecl bindings (some expr))
              let tail ←
                Stmt.listToCoreWithInternalCallsWithRefs? internalFuel
                  (VarBindings.extendStorageRefEnv storageRefEnv bindings)
                  (VarBindings.extendTypeEnv env bindings) externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys rest
              some (head :: tail)
            -- Restrict to the initializer shapes that (a) have no specific list arm
            -- above and (b) declare a local that must survive as a sibling: array /
            -- struct-tuple literals and `new` expressions. Every other initializer
            -- keeps its exact prior handling.
            let isTarget : Bool :=
              match expr with
              | Expr.array _ => true
              | Expr.tuple _ => true
              | Expr.newExpr _ _ => true
              -- A calldata-slice initializer (`bytes calldata s = d[1 : f()]`)
              -- likewise declares a local that must survive as a sibling and may
              -- nest a value-returning call in a bound; peel those into ordered
              -- sibling temps (see the `Expr.slice` arm of `findArgPosInnerCall?`).
              | Expr.slice _ _ _ => true
              -- An enum-conversion initializer (`En e = E(f())`, `E(uint8(f()))`)
              -- likewise declares a local surviving as a sibling and may nest a
              -- value-returning call inside the conversion; peel those into
              -- ordered sibling temps (see the `Expr.enumFromUInt` arm of
              -- `findArgPosInnerCall?`).
              | Expr.enumFromUInt _ _ => true
              -- Wrapper expressions can hide the same nested calls handled by
              -- the argument-position walker.  Route these declaration
              -- initializers through it so the generated call temporaries and
              -- the declared local are emitted as sibling statements.
              | Expr.member _ _ => true
              | Expr.assign _ _ _ => true
              | Expr.payableConversion _ => true
              | _ => false
            match internalFuel, isTarget with
            | fuel + 1, true =>
                match
                    Expr.argPositionHoistPrefix? fuel storageRefEnv env
                      externalCallKindEnv storageNames modifiers functions
                      freeFunctions expr with
                | some (prefixStmts@(_ :: _), residualExpr) =>
                    (match
                        Stmt.listToCoreWithInternalCallsWithRefs? fuel storageRefEnv
                          env externalCallKindEnv storageNames modifiers functions
                          freeFunctions returnTys
                          (Stmt.varDecl bindings (some residualExpr) :: rest) with
                    | some spliced => some (prefixStmts ++ spliced)
                    | none => generic)
                | _ => generic
            | _, _ => generic
          match tupleSplice with
          | some spliced => some spliced
          | none => fallback
      | stmt :: rest => do
          let head ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := env)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := stmt)
          let nextEnv :=
            match stmt with
            | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv env bindings
            | _ => env
          let nextStorageRefEnv :=
            match stmt with
            | Stmt.varDecl bindings _ =>
                VarBindings.extendStorageRefEnv storageRefEnv bindings
            | _ => storageRefEnv
          let tail ←
            Stmt.listToCoreWithInternalCallsWithRefs?
              internalFuel
              nextStorageRefEnv nextEnv externalCallKindEnv storageNames modifiers functions
              freeFunctions returnTys rest
          some (head :: tail)
      )
  | none =>
      match stmts with
      | [] => some []
      | Stmt.varDecl bindings@(_ :: _ :: _) (some (Expr.tuple items)) :: rest => do
          let pieces ←
            match tupleVarDeclAllStorageCore? storageNames bindings items with
            | some decls => some decls
            | none => do
                let (coreDecls, assigns) ←
                  tupleVarDeclCorePieces? storageNames bindings items
                some (coreDecls ++ assigns)
          let tail ← Stmt.listLowerCore? internalFuel none storageNames rest
          some (pieces ++ tail)
      -- GENERAL TUPLE-VARDECL (#171 abi.decode RHS, #172 ternary RHS): flatten a
      -- multi-binding tuple decl with a single-expression RHS into the enclosing list
      -- so the declared locals stay in scope for `rest`.
      | Stmt.varDecl bindings@(_ :: _ :: _) (some rhs) :: rest => do
          let (coreDecls, assigns) ←
            tupleVarDeclGeneralCorePieces? storageNames bindings rhs
          let tail ← Stmt.listLowerCore? internalFuel none storageNames rest
          some (coreDecls ++ assigns ++ tail)
      | stmt :: rest => do
          let head ← Stmt.lowerCore? internalFuel none storageNames stmt
          let tail ← Stmt.listLowerCore? internalFuel none storageNames rest
          some (head :: tail)
termination_by ((if ctx?.isSome then 3 else 0), internalFuel, sizeOf stmts, 7)

def Stmt.listToCoreWithInternalCallsWithRefs?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions : List FunctionDecl) (freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (stmts : List Stmt) :
    Option (List CoreStmt) :=
  Stmt.listLowerCore? internalFuel
    (some ⟨storageRefEnv, env, externalCallKindEnv, modifiers,
        functions, freeFunctions, returnTys⟩)
    storageNames stmts
termination_by (3, internalFuel, sizeOf stmts, 8)

def Stmt.listToCore? (storageNames : List Name) (stmts : List Stmt) : Option (List CoreStmt) :=
  Stmt.listLowerCore? 0 none storageNames stmts
termination_by (0, 0, sizeOf stmts, 8)

def CatchClause.lowerCore? (internalFuel : Nat) (ctx? : Option StmtLoweringCtx)
    (storageNames : List Name) (clause : CatchClause) : Option CoreTryCatchClause :=
  match ctx? with
  | some ctx =>
      let storageRefEnv := ctx.storageRefEnv
      let env := ctx.env
      let externalCallKindEnv := ctx.externalCallKindEnv
      let modifiers := ctx.modifiers
      let functions := ctx.functions
      let freeFunctions := ctx.freeFunctions
      let returnTys := ctx.returnTys
      (match clause with
      | CatchClause.clause name params body => do
          let bindings ← Parameters.toCoreTryBindings? "_catch" params
          let catchEnv := Parameters.extendTypeEnv "_catch" env params
          let bodyCore ←
            Stmt.toCoreWithInternalCalls?
              (internalFuel := internalFuel)
              (storageRefEnv := storageRefEnv)
              (env := catchEnv)
              (externalCallKindEnv := externalCallKindEnv)
              (storageNames := storageNames)
              (modifiers := modifiers)
              (functions := functions)
              (freeFunctions := freeFunctions)
              (returnTys := returnTys)
              (stmt := body)
          some (SolidCore.Solidity.Source.TryCatchClause.clause
            name bindings bodyCore)
      )
  | none =>
      match clause with
      | CatchClause.clause name params body => do
          let bindings ← Parameters.toCoreTryBindings? "_catch" params
          let bodyCore ← Stmt.lowerCore? internalFuel none storageNames body
          some (SolidCore.Solidity.Source.TryCatchClause.clause
            name bindings bodyCore)
termination_by ((if ctx?.isSome then 3 else 0), internalFuel, sizeOf clause, 5)

def CatchClause.toCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  CatchClause.lowerCore? internalFuel
    (some ⟨storageRefEnv, env, externalCallKindEnv, modifiers,
        functions, freeFunctions, returnTys⟩)
    storageNames clause
termination_by (3, internalFuel, sizeOf clause, 6)

def CatchClause.toCore? (storageNames : List Name) (clause : CatchClause) : Option CoreTryCatchClause :=
  CatchClause.lowerCore? 0 none storageNames clause
termination_by (0, 0, sizeOf clause, 6)

def CatchClause.listLowerCore? (internalFuel : Nat) (ctx? : Option StmtLoweringCtx)
    (storageNames : List Name) (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match ctx? with
  | some ctx =>
      let storageRefEnv := ctx.storageRefEnv
      let env := ctx.env
      let externalCallKindEnv := ctx.externalCallKindEnv
      let modifiers := ctx.modifiers
      let functions := ctx.functions
      let freeFunctions := ctx.freeFunctions
      let returnTys := ctx.returnTys
      (match clauses with
      | [] => some []
      | clause :: rest => do
          let head ←
            CatchClause.toCoreWithInternalCalls?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys clause
          let tail ←
            CatchClause.listToCoreWithInternalCalls?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys rest
          some (head :: tail)
      )
  | none =>
      match clauses with
      | [] => some []
      | clause :: rest => do
          let head ← CatchClause.lowerCore? internalFuel none storageNames clause
          let tail ← CatchClause.listLowerCore? internalFuel none storageNames rest
          some (head :: tail)
termination_by ((if ctx?.isSome then 3 else 0), internalFuel, sizeOf clauses, 7)

def CatchClause.listToCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv)
    (env : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  CatchClause.listLowerCore? internalFuel
    (some ⟨storageRefEnv, env, externalCallKindEnv, modifiers,
        functions, freeFunctions, returnTys⟩)
    storageNames clauses
termination_by (3, internalFuel, sizeOf clauses, 8)

def CatchClause.listToCore? (storageNames : List Name) (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  CatchClause.listLowerCore? 0 none storageNames clauses
termination_by (0, 0, sizeOf clauses, 8)

end

def Expr.highLevelExternalCallParts? :
    Expr -> Option (Expr × Name × List CallOption × List Arg)
  | Expr.call (Expr.member target name) args => some (target, name, [], args)
  | Expr.callWithOptions (Expr.member target name) options args =>
      some (target, name, options, args)
  | _ => none

def highLevelExternalCallReservedMember
    (env : TypeEnv) (target : Expr) (name : Name) : Bool :=
  highLevelExternalCallReservedMemberWithEnv env target name

def CallOptions.names : List CallOption -> List Name
  | [] => []
  | CallOption.named name _ :: rest => name :: CallOptions.names rest

def Expr.externalFunctionValueCallParts? :
    Expr -> Option (Expr × List CallOption × List Arg)
  | Expr.call fn args => some (fn, [], args)
  | Expr.callWithOptions fn options args => some (fn, options, args)
  | _ => none

def externalFunctionValueTypeParts? (ty : Ty) :
    Option (List Ty × List Ty × StateMutability) :=
  match ty with
  | Ty.functionWithLocations paramTys _ returnTys _ mutability
      Visibility.external_ =>
      some (paramTys, returnTys, mutability)
  | _ => none

def externalFunctionValueOptionsCore? (storageNames : List Name)
    (mutability : StateMutability) (options : List CallOption) :
    Option (CoreExpr × Option CoreExpr × Bool) :=
  let kind := StateMutability.externalFunctionCallKind mutability
  StateMutability.externalCallOptionsCore?
    storageNames (some mutability) kind options

def Expr.contractCreationParts? :
    Expr -> Option (Ty × List CallOption × List Arg)
  | Expr.newExpr ty args => some (ty, [], args)
  | Expr.callWithOptions (Expr.newExpr ty []) options args =>
      some (ty, options, args)
  | _ => none

def ContractCreation.abiSource? (storageNames : List Name)
    (externalCallKindEnv : ExternalCallKindEnv) (contractName : Name)
    (args : List Arg) : Option (List Ty × List CoreTy × List CoreExpr) :=
  match ExternalCallKindEnv.lookupConstructorEntry?
      externalCallKindEnv contractName with
  | some entry =>
      ExternalCallKindEntry.toAbiCallSource? storageNames entry args
  | none =>
      Args.toAbiEncodeSource? storageNames args

def ContractCreation.optionsCore? (storageNames : List Name)
    (options : List CallOption) :
    Option (CoreExpr × Option CoreExpr) := do
  let (value?, salt?, _) ← CallOptions.contractCreationValueSalt? options
  let valueCore ←
    match value? with
    | some value => Expr.toCore? storageNames value
    | none => some (SolidCore.Solidity.Source.Expr.word 0)
  let saltCore? ←
    match salt? with
    | some salt => do
        let saltCore ← Expr.toCore? storageNames salt
        some (some saltCore)
    | none => some none
  some (valueCore, saltCore?)

inductive InternalCallTargetKind where
  | contractFunction
  | freeFunction
  deriving Repr, BEq

inductive InternalExpressionElaborationKind where
  | directCore
  | singleReturnInternalCall
  | unaryWrapper
  | typeConversionWrapper
  | ternaryConditionWrapper
  | ternaryBranchWrapper
  | unsupported
  deriving Repr, BEq

inductive InternalBinaryExpressionElaborationStatus where
  | resolved
  | notBinaryExpression
  | unsupportedOperator
  | coreExpansionFailed
  deriving Repr, BEq

def FunctionDecl.internalExpressionElaborationKind
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (expr : Expr) : InternalExpressionElaborationKind :=
  let useResult : CoreExpr -> CoreStmt :=
    fun resultExpr =>
      SolidCore.Solidity.Source.Stmt.returnValues [resultExpr]
  match Expr.toCore? storageNames expr with
  | some _ => InternalExpressionElaborationKind.directCore
  | none =>
      match expr with
      | Expr.call (Expr.ident name) args =>
          match FunctionDecl.internalSingleReturnCallCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions name args useResult with
          | some _ =>
              InternalExpressionElaborationKind.singleReturnInternalCall
          | none => InternalExpressionElaborationKind.unsupported
      | Expr.unary op inner =>
          match FunctionDecl.internalUnarySingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions op inner useResult with
          | some _ => InternalExpressionElaborationKind.unaryWrapper
          | none => InternalExpressionElaborationKind.unsupported
      | Expr.call (Expr.typeName targetTy) [Arg.positional inner] =>
          match FunctionDecl.internalTypeConversionSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions targetTy inner useResult with
          | some _ => InternalExpressionElaborationKind.typeConversionWrapper
          | none => InternalExpressionElaborationKind.unsupported
      | Expr.ternary cond thenExpr elseExpr =>
          match FunctionDecl.internalTernaryConditionSingleReturnUseCore?
              internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions cond thenExpr elseExpr
              useResult with
          | some _ =>
              InternalExpressionElaborationKind.ternaryConditionWrapper
          | none =>
              match FunctionDecl.internalTernaryBranchSingleReturnUseCore?
                  internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions cond thenExpr elseExpr
                  useResult with
              | some _ =>
                  InternalExpressionElaborationKind.ternaryBranchWrapper
              | none => InternalExpressionElaborationKind.unsupported
      | _ => InternalExpressionElaborationKind.unsupported

def Stmt.listToCoreWithInternalCalls? (env : TypeEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty) (stmts : List Stmt) :
    Option (List CoreStmt) :=
  Stmt.listToCoreWithInternalCallsWithRefs?
    defaultInternalCallInlineFuel [] env [] storageNames modifiers functions
    freeFunctions returnTys stmts

def defaultModifierPlaceholderReplacementFuel : Nat := 1024

mutual

def Stmt.containsModifierPlaceholder : Stmt -> Bool
  | Stmt.modifierPlaceholder => true
  | Stmt.block body => Stmt.listContainsModifierPlaceholder body
  | Stmt.ifElse _ thenBranch elseBranch =>
      Stmt.containsModifierPlaceholder thenBranch ||
        match elseBranch with
        | some stmt => Stmt.containsModifierPlaceholder stmt
        | none => false
  | Stmt.whileLoop _ body => Stmt.containsModifierPlaceholder body
  | Stmt.doWhile body _ => Stmt.containsModifierPlaceholder body
  | Stmt.forLoop init _ _ body =>
      (match init with
        | some stmt => Stmt.containsModifierPlaceholder stmt
        | none => false) ||
        Stmt.containsModifierPlaceholder body
  | Stmt.tryCatch _ clauses =>
      CatchClause.listContainsModifierPlaceholder clauses
  | Stmt.tryCatchReturns _ _ success clauses =>
      Stmt.containsModifierPlaceholder success ||
        CatchClause.listContainsModifierPlaceholder clauses
  | Stmt.unchecked body => Stmt.containsModifierPlaceholder body
  | _ => false

def CatchClause.containsModifierPlaceholder : CatchClause -> Bool
  | CatchClause.clause _ _ body => Stmt.containsModifierPlaceholder body

def CatchClause.listContainsModifierPlaceholder : List CatchClause -> Bool
  | [] => false
  | clause :: rest =>
      CatchClause.containsModifierPlaceholder clause ||
        CatchClause.listContainsModifierPlaceholder rest

def Stmt.listContainsModifierPlaceholder : List Stmt -> Bool
  | [] => false
  | stmt :: rest =>
      Stmt.containsModifierPlaceholder stmt ||
        Stmt.listContainsModifierPlaceholder rest

end

mutual

def Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt) (stmt : Stmt) :
    Option CoreStmt :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match stmt with
      | Stmt.modifierPlaceholder =>
          some (SolidCore.Solidity.Source.Stmt.captureReturn
            returnNames replacement)
      | Stmt.block body => do
          let coreBody ←
            Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.block coreBody)
      | Stmt.ifElse cond thenBranch elseBranch => do
          let thenCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement thenBranch
          let elseCore ←
            match elseBranch with
            | some stmt =>
                Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                  replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys returnNames
                  replacement stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          FunctionDecl.conditionUseCoreWithInternalCalls?
            internalFuel storageRefEnv env externalCallKindEnv storageNames
            modifiers functions freeFunctions cond
            (fun condCore =>
              SolidCore.Solidity.Source.Stmt.ifElse
                condCore thenCore elseCore)
      | Stmt.whileLoop cond body => do
          let condCore ←
            Expr.toCoreAsWithEnv? storageNames env Ty.bool cond
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.whileLoop condCore bodyCore)
      | Stmt.doWhile body cond => do
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          let condCore ←
            Expr.toCoreAsWithEnv? storageNames env Ty.bool cond
          some (SolidCore.Solidity.Source.Stmt.doWhile bodyCore condCore)
      | Stmt.forLoop init cond post body => do
          let initCore ←
            match init with
            | some stmt =>
                Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                  replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
                  modifiers functions freeFunctions returnTys returnNames
                  replacement stmt
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let loopEnv :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                VarBindings.extendTypeEnv env bindings
            | _ => env
          let loopStorageRefEnv :=
            match init with
            | some (Stmt.varDecl bindings _) =>
                VarBindings.extendStorageRefEnv storageRefEnv bindings
            | _ => storageRefEnv
          let condCore ←
            match cond with
            | some expr =>
                Expr.toCoreAsWithEnv? storageNames loopEnv Ty.bool expr
            | none => some (SolidCore.Solidity.Source.Expr.word 1)
          let postCore ←
            match post with
            | some expr =>
                Stmt.toCoreWithInternalCalls?
                  internalFuel loopStorageRefEnv loopEnv externalCallKindEnv
                  storageNames modifiers functions freeFunctions returnTys
                  (Stmt.expr expr)
            | none => some SolidCore.Solidity.Source.Stmt.skip
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel loopStorageRefEnv loopEnv
              externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.forLoop
            initCore condCore postCore bodyCore)
      | Stmt.tryCatch expr clauses => do
          let catchCore ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys
              returnNames replacement clauses
          match Expr.toExternalCallWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) =>
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv env [] expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode [] []
                  SolidCore.Solidity.Source.Stmt.skip catchCore)
          | none => do
              match Expr.externalFunctionValueCallCore? storageNames env expr with
              | some (kind, _, targetCore, calldataCore, valueCore, gasCore?,
                  gasFirst) =>
                  some
                    (SolidCore.Solidity.Source.Stmt.tryExternalCall
                      kind targetCore calldataCore valueCore gasCore? gasFirst
                      true [] []
                      SolidCore.Solidity.Source.Stmt.skip catchCore)
              | none => do
                  let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                    Expr.toContractCreationWithKindEnv?
                      storageNames externalCallKindEnv expr
                  some
                    (SolidCore.Solidity.Source.Stmt.tryContractCreate
                      contractName argsCore valueCore saltCore? valueBeforeSalt []
                      SolidCore.Solidity.Source.Stmt.skip catchCore)
      | Stmt.tryCatchReturns expr returns success clauses => do
          let returnBindings ← Parameters.toCoreTryBindings? "_try" returns
          let returnAbiCleanups ←
            Tys.toCoreAbiCleanups? (returns.map Parameter.ty)
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let successCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv successEnv
              externalCallKindEnv storageNames modifiers functions
              freeFunctions returnTys returnNames replacement success
          let catchCore ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys
              returnNames replacement clauses
          match Expr.toExternalCallWithKindEnv? (argEnvLower := Expr.externalCallArgEnvLower storageNames env)
              storageNames env externalCallKindEnv expr with
          | some (kind, targetCore, calldataCore, valueCore, gasCore?, gasFirst) =>
              let checkTargetCode :=
                Expr.externalCallNeedsCodeCheckWithEnv env
                  (returns.map Parameter.ty) expr
              some
                (SolidCore.Solidity.Source.Stmt.tryExternalCall
                  kind targetCore calldataCore valueCore gasCore? gasFirst
                  checkTargetCode returnBindings returnAbiCleanups
                  successCore catchCore)
          | none => do
              match Expr.externalFunctionValueCallCore? storageNames env expr with
              | some (kind, _, targetCore, calldataCore, valueCore, gasCore?,
                  gasFirst) =>
                  let checkTargetCode := returns.isEmpty
                  some
                    (SolidCore.Solidity.Source.Stmt.tryExternalCall
                      kind targetCore calldataCore valueCore gasCore? gasFirst
                      checkTargetCode returnBindings returnAbiCleanups
                      successCore catchCore)
              | none => do
                  let (contractName, argsCore, valueCore, saltCore?, valueBeforeSalt) ←
                    Expr.toContractCreationWithKindEnv?
                      storageNames externalCallKindEnv expr
                  some
                    (SolidCore.Solidity.Source.Stmt.tryContractCreate
                      contractName argsCore valueCore saltCore? valueBeforeSalt returnBindings
                      successCore catchCore)
      | Stmt.unchecked body => do
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv storageNames
              modifiers functions freeFunctions returnTys returnNames
              replacement body
          some (SolidCore.Solidity.Source.Stmt.unchecked bodyCore)
      | other =>
          Stmt.toCoreWithInternalCalls?
            (internalFuel := internalFuel)
            (storageRefEnv := storageRefEnv)
            (env := env)
            (externalCallKindEnv := externalCallKindEnv)
            (storageNames := storageNames)
            (modifiers := modifiers)
            (functions := functions)
            (freeFunctions := freeFunctions)
            (returnTys := returnTys)
            (stmt := other)

def CatchClause.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (clause : CatchClause) : Option CoreTryCatchClause :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match clause with
      | CatchClause.clause name params body => do
          let bindings ← Parameters.toCoreTryBindings? "_catch" params
          let catchEnv := Parameters.extendTypeEnv "_catch" env params
          let bodyCore ←
            Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv catchEnv
              externalCallKindEnv storageNames modifiers functions freeFunctions
              returnTys returnNames replacement body
          some
            (SolidCore.Solidity.Source.TryCatchClause.clause
              name bindings bodyCore)

def CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (clauses : List CatchClause) : Option (List CoreTryCatchClause) :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match clauses with
      | [] => some []
      | clause :: rest => do
          let head ←
            CatchClause.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys
              returnNames replacement clause
          let tail ←
            CatchClause.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel storageRefEnv env externalCallKindEnv
              storageNames modifiers functions freeFunctions returnTys
              returnNames replacement rest
          some (head :: tail)

def Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    (replaceFuel internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt)
    (stmts : List Stmt) : Option (List CoreStmt) :=
  match replaceFuel with
  | 0 => none
  | replaceFuel + 1 =>
      match stmts with
      | [] => some []
      | stmt :: rest => do
          let head ←
            if Stmt.containsModifierPlaceholder stmt then
              do
                let coreStmt ←
                  Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
                    replaceFuel internalFuel storageRefEnv env
                    externalCallKindEnv storageNames modifiers functions
                    freeFunctions returnTys returnNames replacement stmt
                some [coreStmt]
            else
              Stmt.listToCoreWithInternalCallsWithRefs?
                internalFuel storageRefEnv env externalCallKindEnv storageNames modifiers
                functions freeFunctions returnTys [stmt]
          let nextEnv :=
            match stmt with
            | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv env bindings
            | _ => env
          let nextStorageRefEnv :=
            match stmt with
            | Stmt.varDecl bindings _ =>
                VarBindings.extendStorageRefEnv storageRefEnv bindings
            | _ => storageRefEnv
          let tail ←
            Stmt.listToCoreWithInternalCallsReplacingModifierPlaceholderFuel?
              replaceFuel internalFuel nextStorageRefEnv nextEnv
              externalCallKindEnv storageNames modifiers functions freeFunctions
              returnTys returnNames replacement rest
          some (head ++ tail)

end

def Stmt.toCoreWithInternalCallsReplacingModifierPlaceholder?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (returnNames : List Name) (replacement : CoreStmt) (stmt : Stmt) :
    Option CoreStmt :=
  Stmt.toCoreWithInternalCallsReplacingModifierPlaceholderFuel?
    defaultModifierPlaceholderReplacementFuel internalFuel storageRefEnv env
    externalCallKindEnv storageNames modifiers functions freeFunctions
    returnTys returnNames replacement stmt

def modifierApplyToCoreWithInternalCalls? (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (decl : SourceModifierDecl)
    (invocation : SourceModifierInvocation) (inner : CoreStmt) :
    Option CoreStmt := do
  let body ← decl.body
  let body := ModifierDecl.aliasParamsInBody decl body
  let prefixStmts ← modifierParamBindingsWithArgs? decl invocation.args
  let prefixCore ←
    Stmt.listToCoreWithInternalCallsWithRefs?
      internalFuel storageRefEnv env externalCallKindEnv storageNames available functions
      freeFunctions returnTys prefixStmts
  let modifierParams := ModifierDecl.aliasedParams decl
  let modifierEnv := Parameters.extendTypeEnv "_mod" env modifierParams
  let modifierStorageRefEnv :=
    Parameters.extendStorageRefEnv "_mod" storageRefEnv modifierParams
  let body := Stmt.annotateAbi modifierEnv body
  let bodyCore ←
    Stmt.toCoreWithInternalCallsReplacingModifierPlaceholder?
      internalFuel modifierStorageRefEnv modifierEnv externalCallKindEnv
      storageNames available functions freeFunctions returnTys returnNames
      inner body
  some (SolidCore.Solidity.Source.Stmt.block (prefixCore ++ [bodyCore]))

/-- Body-level ANF preprocessing. Recurses into every child statement, then
    normalizes every top-level expression which contains a hoistable call into
    a `block` of flat statements. Surface lowering success is not a sufficient
    reason to skip this pass: some legacy dispatcher arms build a Core term
    which fails only during checked-executable generation. -/
def Stmt.anfPreprocess (structEnv : StructEnv) (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames : List Name)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (eventIndexedEnv : EventIndexedEnv) :
    Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | fuel + 1, stmt =>
      let recur := Stmt.anfPreprocess structEnv internalFuel storageRefEnv env
        externalCallKindEnv storageNames modifiers functions freeFunctions
        returnTys eventIndexedEnv fuel
      let stmt1 :=
        match stmt with
        | Stmt.block ss =>
            -- `anfNormalizeSelf?` represents a generated prelude as
            -- `block (pre ++ [tail])`.  At statement-list level those pieces
            -- must be siblings: in particular, a normalized variable
            -- declaration has to remain in scope for the statements that
            -- follow it.  Splice only blocks introduced while recurring over
            -- a non-block child; preserve every block that existed in the
            -- source, since that block carries Solidity lexical scope.
            let step := fun
                (acc : List Stmt × TypeEnv × StorageRefEnv) (child : Stmt) =>
              let (out, childEnv, childStorageRefEnv) := acc
              let normalized :=
                Stmt.anfPreprocess structEnv internalFuel childStorageRefEnv
                  childEnv externalCallKindEnv storageNames modifiers functions
                  freeFunctions returnTys eventIndexedEnv fuel child
              let pieces :=
                match child, normalized with
                | Stmt.block _, _ => [normalized]
                | _, Stmt.block inner => inner
                | _, _ => [normalized]
              let nextEnv :=
                match child with
                | Stmt.varDecl bindings _ =>
                    VarBindings.extendTypeEnv childEnv bindings
                | _ => childEnv
              let nextStorageRefEnv :=
                match child with
                | Stmt.varDecl bindings _ =>
                    VarBindings.extendStorageRefEnv childStorageRefEnv bindings
                | _ => childStorageRefEnv
              (out ++ pieces, nextEnv, nextStorageRefEnv)
            let (out, _, _) := ss.foldl step ([], env, storageRefEnv)
            Stmt.block out
        | Stmt.ifElse c t e => Stmt.ifElse c (recur t) (e.map recur)
        | Stmt.whileLoop c b =>
            let b' := recur b
            let (_, pre, c') :=
              Expr.anfHoist functions freeFunctions env externalCallKindEnv
                storageNames anfHoistFuel 0 c
            if pre.isEmpty then Stmt.whileLoop c b'
            else
              Stmt.annotateAbi env
                (Stmt.resolveStructs structEnv env
                  (Stmt.whileLoop (Expr.literal (Literal.bool true))
                    (Stmt.block
                      (pre ++ [Stmt.ifElse c' b' (some Stmt.break)]))))
        | Stmt.doWhile b c =>
            let b' := recur b
            let (_, pre, c') :=
              Expr.anfHoist functions freeFunctions env externalCallKindEnv
                storageNames anfHoistFuel 0 c
            if pre.isEmpty then Stmt.doWhile b' c
            else
              let check :=
                Stmt.block
                  (pre ++ [Stmt.ifElse c' Stmt.empty (some Stmt.break)])
              let loop :=
                if Stmt.mentionsBareContinue b then
                  let first := "__solidcore_anf_loop_first"
                  Stmt.block
                    [ Stmt.varDecl
                        [{ name := some first, ty := some Ty.bool,
                           location := none }]
                        (some (Expr.literal (Literal.bool true)))
                    , Stmt.whileLoop (Expr.literal (Literal.bool true))
                        (Stmt.block
                          [ Stmt.ifElse (Expr.ident first)
                              (Stmt.expr
                                (Expr.assign (Expr.ident first)
                                  AssignOp.assign
                                  (Expr.literal (Literal.bool false))))
                              (some check)
                          , b' ]) ]
                else
                  Stmt.whileLoop (Expr.literal (Literal.bool true))
                    (Stmt.block [b', check])
              Stmt.annotateAbi env (Stmt.resolveStructs structEnv env loop)
        | Stmt.forLoop i c p b =>
            let loopEnv :=
              match i with
              | some (Stmt.varDecl bindings _) =>
                  VarBindings.extendTypeEnv env bindings
              | _ => env
            let loopStorageRefEnv :=
              match i with
              | some (Stmt.varDecl bindings _) =>
                  VarBindings.extendStorageRefEnv storageRefEnv bindings
              | _ => storageRefEnv
            let b' :=
              Stmt.anfPreprocess structEnv internalFuel loopStorageRefEnv
                loopEnv externalCallKindEnv storageNames modifiers functions
                freeFunctions returnTys eventIndexedEnv fuel b
            let (counter, condPre, c') :=
              match c with
              | some cond =>
                  Expr.anfHoist functions freeFunctions loopEnv
                    externalCallKindEnv storageNames anfHoistFuel 0 cond
              | none =>
                  (0, [], Expr.literal (Literal.bool true))
            let (_, postPre, p') :=
              match p with
              | some post =>
                  Expr.anfHoist functions freeFunctions loopEnv
                    externalCallKindEnv storageNames anfHoistFuel counter post
              | none =>
                  (counter, [], Expr.literal (Literal.bool true))
            if condPre.isEmpty && postPre.isEmpty then
              -- Keep a green initializer on the dedicated for-init lowering
              -- path.  In particular, normalizing `uint i = f()` into a block
              -- would scope `i` out before the condition.
              Stmt.forLoop i c p b'
            else
              let initPieces :=
                match i with
                | some init =>
                    let init' := recur init
                    match init, init' with
                    | Stmt.block _, _ => [init']
                    | _, Stmt.block inner => inner
                    | _, _ => [init']
                | none => []
              let check :=
                Stmt.block
                  (condPre ++ [Stmt.ifElse c' Stmt.empty (some Stmt.break)])
              let postStmt :=
                match p with
                | some _ => Stmt.block (postPre ++ [Stmt.expr p'])
                | none => Stmt.empty
              let loop :=
                if Stmt.mentionsBareContinue b then
                  let first := "__solidcore_anf_loop_first"
                  Stmt.block
                    (initPieces ++
                      [ Stmt.varDecl
                          [{ name := some first, ty := some Ty.bool,
                             location := none }]
                          (some (Expr.literal (Literal.bool true)))
                      , Stmt.whileLoop (Expr.literal (Literal.bool true))
                          (Stmt.block
                            [ Stmt.ifElse (Expr.ident first)
                                (Stmt.expr
                                  (Expr.assign (Expr.ident first)
                                    AssignOp.assign
                                    (Expr.literal (Literal.bool false))))
                                (some postStmt)
                            , check
                            , b' ]) ])
                else
                  Stmt.block
                    (initPieces ++
                      [ Stmt.whileLoop (Expr.literal (Literal.bool true))
                          (Stmt.block [check, b', postStmt]) ])
              Stmt.annotateAbi env (Stmt.resolveStructs structEnv env loop)
        | Stmt.unchecked b => Stmt.unchecked (recur b)
        | Stmt.tryCatch e clauses =>
            Stmt.tryCatch e
              (clauses.map (fun cl =>
                match cl with
                | CatchClause.clause n ps body =>
                    CatchClause.clause n ps (recur body)))
        | Stmt.tryCatchReturns e ps s clauses =>
            Stmt.tryCatchReturns e ps (recur s)
              (clauses.map (fun cl =>
                match cl with
                | CatchClause.clause n ps' body =>
                    CatchClause.clause n ps' (recur body)))
        | other => other
      -- A generated ANF block is returned unconditionally. Requiring it to pass
      -- a function-entry lowerability probe would reject valid hoists whose
      -- residual depends on a preceding block-local declaration.
      -- STAGE-D #195: a `Stmt.emitEvent` with a NON-identity two-phase schedule
      -- (an indexed argument follows a data argument in source order, e.g.
      -- `emit E3(f(), g())` both-indexed) must be normalized EVEN IF it already
      -- lowers directly — the direct path's call hoisting runs the args in
      -- source L2R order, defeating the interpreter's two-phase emit schedule.
      -- `emitTwoPhaseHoist?` declines identity schedules and hoist-free emits,
      -- so every previously-green emit keeps the byte-identical direct
      -- lowering. The normalized block is kept only if it itself lowers (never
      -- trading a green statement for a red one).
      match (match stmt1 with
        | Stmt.emitEvent e =>
            (match emitTwoPhaseHoist? functions freeFunctions env
                externalCallKindEnv storageNames eventIndexedEnv e with
             | some (pre, e') =>
                 some (Stmt.annotateAbi env
                   (Stmt.resolveStructs structEnv env
                     (Stmt.block (pre ++ [Stmt.emitEvent e']))))
             | none => none)
        | _ => none) with
      | some stmt2 =>
          stmt2
      | none =>
        -- A few statement families have dedicated lowering that carries
        -- semantics the general value ANF does not yet encode: storage aliases,
        -- tuple target/return scheduling, and `.selector` receiver effects.
        -- Preserve those specialized paths while applying ANF eagerly to the
        -- ordinary expression positions above.
        let normalized? :=
          match stmt1 with
          | Stmt.varDecl bindings _ =>
              if bindings.any (fun b =>
                  b.location == some DataLocation.storage) then none
              else
                Stmt.anfNormalizeSelf? structEnv functions freeFunctions env
                  externalCallKindEnv storageNames eventIndexedEnv stmt1
          | Stmt.returnValues (some (Expr.tuple _)) => none
          | Stmt.returnValues
              (some (Expr.call (Expr.typeName _)
                [Arg.positional (Expr.member _ "selector")])) => none
          | Stmt.expr e@(Expr.call _ _) =>
              match Expr.anfHoistableCallTy? functions freeFunctions env
                  externalCallKindEnv storageNames e with
              | some _ => none
              | none =>
                  Stmt.anfNormalizeSelf? structEnv functions freeFunctions env
                    externalCallKindEnv storageNames eventIndexedEnv stmt1
          | Stmt.expr e@(Expr.callWithOptions _ _ _) =>
              match Expr.anfHoistableCallTy? functions freeFunctions env
                  externalCallKindEnv storageNames e with
              | some _ => none
              | none =>
                  Stmt.anfNormalizeSelf? structEnv functions freeFunctions env
                    externalCallKindEnv storageNames eventIndexedEnv stmt1
          | Stmt.expr (Expr.member _ "selector") => none
          | Stmt.expr (Expr.assign (Expr.tuple _) _ _) => none
          | _ =>
              Stmt.anfNormalizeSelf? structEnv functions freeFunctions env
                externalCallKindEnv storageNames eventIndexedEnv stmt1
        match normalized? with
        | some stmt2 => stmt2
        | none => stmt1
termination_by fuel _ => fuel

def defaultAnfPreprocessFuel : Nat := 1024

def functionExpandModifiersToCoreWithInternalCallsFull?
    (internalFuel : Nat)
    (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (bodyStorageNames : List Name)
    (returnNames : List Name)
    (available : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl) (returnTys : List Ty)
    (invocations : List SourceModifierInvocation) (body : Stmt)
    (structEnv : StructEnv := [])
    (eventIndexedEnv : EventIndexedEnv := []) :
    Option CoreStmt :=
  -- `storageNames` is the FULL contract state-name set used to lower the
  -- surrounding modifier prefixes/bodies (a modifier is a separate scope: the
  -- modified function's params never shadow into it). `bodyStorageNames` is the
  -- set for the function's OWN body, from which the function's param/named-return
  -- names have been removed (param-shadows-statevar soundness fix), so a bare
  -- read of such a name resolves to the local, not the state variable.
  match invocations with
  | [] =>
      let body :=
        Stmt.anfPreprocess structEnv internalFuel storageRefEnv env
          externalCallKindEnv bodyStorageNames available functions freeFunctions
          returnTys eventIndexedEnv defaultAnfPreprocessFuel body
      Stmt.toCoreWithInternalCalls?
        (internalFuel := internalFuel)
        (storageRefEnv := storageRefEnv)
        (env := env)
        (externalCallKindEnv := externalCallKindEnv)
        (storageNames := bodyStorageNames)
        (modifiers := available)
        (functions := functions)
        (freeFunctions := freeFunctions)
        (returnTys := returnTys)
        (stmt := body)
  | invocation :: rest => do
      let inner ←
        functionExpandModifiersToCoreWithInternalCallsFull?
          internalFuel storageRefEnv env externalCallKindEnv storageNames
          bodyStorageNames returnNames available functions freeFunctions
          returnTys rest body
          (structEnv := structEnv) (eventIndexedEnv := eventIndexedEnv)
      let modifierDecl ← modifierResolve? available invocation.target
      modifierApplyToCoreWithInternalCalls? internalFuel storageRefEnv env
        externalCallKindEnv storageNames returnNames available functions
        freeFunctions returnTys modifierDecl invocation inner
termination_by invocations.length

def libraryHelperNameForIndex (libraryName functionName : Name)
    (index : Nat) : Name :=
  if index == 0 then
    libraryHelperName libraryName functionName
  else
    libraryHelperName libraryName functionName ++ "_overload_" ++ toString index

def ContractDecl.isLibrary (decl : ContractDecl) : Bool :=
  match decl.kind with
  | ContractKind.library => true
  | _ => false

def ContractDecls.hasLibrary : List ContractDecl -> Bool
  | [] => false
  | decl :: rest =>
      ContractDecl.isLibrary decl || ContractDecls.hasLibrary rest

def ContractDecl.findLibraryByName? (contracts : List ContractDecl)
    (name : Name) : Option ContractDecl :=
  contracts.find? (fun decl => decl.name == name && ContractDecl.isLibrary decl)

def FunctionDecl.isInlineLibraryFunction (decl : FunctionDecl) : Bool :=
  match decl.visibility with
  | some Visibility.public_ | some Visibility.external_ => false
  | _ => !FunctionDecl.isConstructor decl

def FunctionDecl.isExternalLibraryFunction (decl : FunctionDecl) : Bool :=
  match decl.visibility with
  | some Visibility.public_ | some Visibility.external_ =>
      !FunctionDecl.isConstructor decl
  | _ => false

/-- Does `library` declare a PUBLIC/EXTERNAL function named `name`? Such a function
    is a delegatecall entry point, not an internal-jump helper (`isInlineLibrary
    Function`), so `Lib.name` has no internal-function VALUE. -/
def ContractDecl.hasExternalLibraryFunction (decl : ContractDecl) (name : Name) :
    Bool :=
  decl.items.any (fun item =>
    match item with
    | ContractItem.function fn =>
        fn.name == some name && FunctionDecl.isExternalLibraryFunction fn
    | _ => false)

/-- A builtin `abi.*` function member (`abi.encode`, `abi.decode`, ...). Naming
    one as a bare VALUE (`abi.decode;`) has no internal-function pointer and no
    side effects; solc accepts it only when the value is immediately DISCARDED. -/
def Expr.isAbiFunctionMemberName (member : Name) : Bool :=
  member == "encode" || member == "encodePacked" ||
    member == "encodeWithSelector" || member == "encodeWithSignature" ||
    member == "decode"

/-- LIBRARY-STRAY-VALUE / ABI-STRAY-VALUE / UDVT-STRAY-VALUE: a member access
    naming a function as a VALUE that solc accepts only when the value is
    immediately DISCARDED (a stray `Lib.m;`, `abi.decode;`, or `MyAddress.wrap;`
    statement). `Lib.m` names a PUBLIC/EXTERNAL library function (a delegatecall
    entry point, no internal-function pointer); `abi.<fn>` names a builtin `abi.*`
    function; `T.wrap` / `T.unwrap` names a user-value-type builtin. None has side
    effects (a bare member-value expression statement never does) nor a lowerable
    value form, so the statement lowers to a no-op (see
    `Stmt.dropStrayLibraryFunctionValues`). -/
def Expr.isStrayLibraryFunctionValue
    (contracts : List ContractDecl) : Expr -> Bool
  | Expr.member (Expr.typeName (Ty.user path)) member =>
      (member == "wrap" || member == "unwrap") ||
      (match path.segments.getLast? with
       | some libraryName =>
           match ContractDecl.findLibraryByName? contracts libraryName with
           | some decl => ContractDecl.hasExternalLibraryFunction decl member
           | none => false
       | none => false)
  | Expr.member (Expr.ident "abi") member =>
      Expr.isAbiFunctionMemberName member
  -- ARRAY-MUTATION-STRAY-VALUE: `data.pop;` / `data.push;` names the builtin
  -- storage-array `push`/`pop` mutation member over a plain identifier base as a
  -- discarded VALUE. TypeCheck accepts this only when the base is a storage
  -- dynamic array / `bytes` (see the ARRAY-MUTATION-STRAY-VALUE arm in
  -- `checkStmt`), so any such statement that survives to lowering is that
  -- effect-free no-op; the uncalled `push`/`pop` never runs (it has no lowerable
  -- value form), so the statement lowers to nothing.
  | Expr.member (Expr.ident _) member =>
      member == "push" || member == "pop"
  | _ => false

mutual

/-- Replace each stray public/external library-function-value statement `Lib.m;`
    with a no-op (solc accepts it as a discarded, effect-free expression; it has
    no lowerable value form). Recurses through nested control flow so a stray
    reference inside a block/branch/loop is dropped too. -/
def Stmt.dropStrayLibraryFunctionValuesFuel :
    Nat -> List ContractDecl -> Stmt -> Stmt
  | 0, _, stmt => stmt
  | fuel + 1, contracts, stmt =>
      let recStmt := Stmt.dropStrayLibraryFunctionValuesFuel fuel contracts
      let recClause := CatchClause.dropStrayLibraryFunctionValuesFuel fuel contracts
      match stmt with
      | Stmt.expr expr =>
          if Expr.isStrayLibraryFunctionValue contracts expr then
            Stmt.empty
          else
            Stmt.expr expr
      | Stmt.block body => Stmt.block (body.map recStmt)
      | Stmt.ifElse cond thenBranch elseBranch =>
          Stmt.ifElse cond (recStmt thenBranch) (elseBranch.map recStmt)
      | Stmt.whileLoop cond body => Stmt.whileLoop cond (recStmt body)
      | Stmt.doWhile body cond => Stmt.doWhile (recStmt body) cond
      | Stmt.forLoop init cond post body =>
          Stmt.forLoop (init.map recStmt) cond post (recStmt body)
      | Stmt.tryCatch expr clauses =>
          Stmt.tryCatch expr (clauses.map recClause)
      | Stmt.tryCatchReturns expr returns success clauses =>
          Stmt.tryCatchReturns expr returns (recStmt success)
            (clauses.map recClause)
      | Stmt.unchecked body => Stmt.unchecked (recStmt body)
      | other => other

def CatchClause.dropStrayLibraryFunctionValuesFuel :
    Nat -> List ContractDecl -> CatchClause -> CatchClause
  | 0, _, clause => clause
  | fuel + 1, contracts, clause =>
      match clause with
      | CatchClause.clause name params body =>
          CatchClause.clause name params
            (Stmt.dropStrayLibraryFunctionValuesFuel fuel contracts body)

end

def Stmt.dropStrayLibraryFunctionValues
    (contracts : List ContractDecl) (stmt : Stmt) : Stmt :=
  Stmt.dropStrayLibraryFunctionValuesFuel defaultResolveInterfaceIdsFuel
    contracts stmt

def ContractItems.findOrdinaryFunctionByName?
    (items : List ContractItem) (name : Name) : Option FunctionDecl :=
  match items with
  | [] => none
  | ContractItem.function fn :: rest =>
      if FunctionDecl.isInlineLibraryFunction fn then
        match fn.name with
        | some fnName =>
            if fnName == name then
              some fn
            else
              ContractItems.findOrdinaryFunctionByName? rest name
        | none =>
            ContractItems.findOrdinaryFunctionByName? rest name
      else
        ContractItems.findOrdinaryFunctionByName? rest name
  | _ :: rest =>
      ContractItems.findOrdinaryFunctionByName? rest name
termination_by items.length

def ContractDecl.findOrdinaryFunctionByName? (decl : ContractDecl)
    (name : Name) : Option FunctionDecl :=
  ContractItems.findOrdinaryFunctionByName? decl.items name

def ContractItems.ordinaryFunctionsByName (items : List ContractItem)
    (name : Name) : List FunctionDecl :=
  items.filterMap (fun item =>
    match item with
    | ContractItem.function fn =>
        if FunctionDecl.isInlineLibraryFunction fn then
          match fn.name with
          | some fnName => if fnName == name then some fn else none
          | none => none
        else
          none
    | _ => none)

def ContractDecl.ordinaryFunctionsByName (decl : ContractDecl)
    (name : Name) : List FunctionDecl :=
  ContractItems.ordinaryFunctionsByName decl.items name

def ContractItems.findExternalLibraryFunctionByName?
    (items : List ContractItem) (name : Name) : Option FunctionDecl :=
  match items with
  | [] => none
  | ContractItem.function fn :: rest =>
      if FunctionDecl.isExternalLibraryFunction fn then
        match fn.name with
        | some fnName =>
            if fnName == name then
              some fn
            else
              ContractItems.findExternalLibraryFunctionByName? rest name
        | none =>
            ContractItems.findExternalLibraryFunctionByName? rest name
      else
        ContractItems.findExternalLibraryFunctionByName? rest name
  | _ :: rest =>
      ContractItems.findExternalLibraryFunctionByName? rest name
termination_by items.length

def ContractDecl.findExternalLibraryFunctionByName? (decl : ContractDecl)
    (name : Name) : Option FunctionDecl :=
  ContractItems.findExternalLibraryFunctionByName? decl.items name

def ContractItems.externalLibraryFunctionsByName (items : List ContractItem)
    (name : Name) : List FunctionDecl :=
  items.filterMap (fun item =>
    match item with
    | ContractItem.function fn =>
        if FunctionDecl.isExternalLibraryFunction fn then
          match fn.name with
          | some fnName => if fnName == name then some fn else none
          | none => none
        else
          none
    | _ => none)

def ContractDecl.externalLibraryFunctionsByName (decl : ContractDecl)
    (name : Name) : List FunctionDecl :=
  ContractItems.externalLibraryFunctionsByName decl.items name

def FunctionDecl.firstParamMatches? (env : TypeEnv)
    (receiver : Expr) (decl : FunctionDecl) : Option Bool := do
  match decl.params with
  | first :: _ =>
      let receiverTy ← Expr.abiTyWithEnv? env receiver
      some (Ty.matchesShape receiverTy first.ty)
  | [] => some false

def FunctionDecl.firstParamMatchesWithInternalFunctions?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (receiver : Expr) (decl : FunctionDecl) : Option Bool := do
  match decl.params with
  | first :: _ =>
      let receiverTy ←
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env receiver
      -- USING-FOR function usability (Types.cpp `Type::attachedFunctions`):
      -- the receiver need only be IMPLICITLY CONVERTIBLE to the function's
      -- first-parameter type (directional), NOT exact-width. e.g. a `uint8`
      -- receiver binds `f(uint256 self)` (widened, zero-extended). The wider
      -- direction (uint256 receiver → uint8 self) stays rejected because
      -- `canImplicitlyConvert` is directional. Directive APPLICABILITY
      -- (receiver == target type) is a separate, still-exact check.
      --
      -- USINGFOR-WIDEN-BIND regression fix: `canImplicitlyConvert`'s struct/user
      -- arms are exact `==` only, so a storage struct receiver whose reflected
      -- `abiTy` path differs from the parameter's resolved struct type (e.g.
      -- OpenZeppelin EnumerableMap's `_owners.set(...)`) stopped binding. Fall
      -- back to nominal `Ty.matchesShape` (the pre-#158 predicate) for those
      -- cases. Additive: the widening case succeeds via `canImplicitlyConvert`,
      -- and every `canImplicitlyConvert` reject is also a `matchesShape` reject
      -- (verified: narrowing, uint→bytes32, signedness), so the #158 over-accept
      -- guards are preserved.
      some (Ty.canImplicitlyConvert receiverTy first.ty ||
        Ty.matchesShape receiverTy first.ty)
  | [] => some false

def FunctionDecl.annotateSingleCoreReturn (decl : FunctionDecl)
    (expr : Expr) : Expr :=
  match decl.returns with
  | [ret] =>
      match Ty.internalCallConversionCore? ret.ty with
      | some _ => Expr.call (Expr.typeName ret.ty) [Arg.positional expr]
      | none => expr
  | _ => expr

def UsingDecl.targetMatches? (env : TypeEnv)
    (receiver : Expr) (decl : UsingDecl) : Option Bool :=
  match decl.target with
  | some targetTy => do
      let receiverTy ←
        match receiver, targetTy with
        | Expr.enumFromUInt maxValue _, Ty.enum path _ =>
            some (Ty.enum path maxValue)
        | _, _ => Expr.abiTyWithEnv? env receiver
      some (Ty.matchesShape receiverTy targetTy)
  | none => some true

def UsingDecl.targetMatchesWithInternalFunctions?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (receiver : Expr) (decl : UsingDecl) : Option Bool :=
  match decl.target with
  | some targetTy => do
      let receiverTy ←
        match receiver, targetTy with
        | Expr.enumFromUInt maxValue _, Ty.enum path _ =>
            some (Ty.enum path maxValue)
        | _, _ =>
            Expr.abiTyWithInternalFunctionsEnv?
              functions freeFunctions env receiver
      some (Ty.matchesShape receiverTy targetTy)
  | none => some true

def UsingDecl.targetMatchesBinary? (env : TypeEnv)
    (lhs rhs : Expr) (decl : UsingDecl) : Option Bool :=
  match decl.target with
  | some targetTy => do
      let lhsTy? := Expr.abiTyWithEnv? env lhs
      let rhsTy? := Expr.abiTyWithEnv? env rhs
      match lhsTy?, rhsTy? with
      | some lhsTy, some rhsTy =>
          some (Ty.matchesShape lhsTy targetTy ||
            Ty.matchesShape rhsTy targetTy)
      | some lhsTy, none => some (Ty.matchesShape lhsTy targetTy)
      | none, some rhsTy => some (Ty.matchesShape rhsTy targetTy)
      | none, none => none
  | none => some true

def UsingDecl.targetMatchesBinaryWithInternalFunctions?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (lhs rhs : Expr) (decl : UsingDecl) : Option Bool :=
  match decl.target with
  | some targetTy => do
      let lhsTy? :=
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env lhs
      let rhsTy? :=
        Expr.abiTyWithInternalFunctionsEnv?
          functions freeFunctions env rhs
      match lhsTy?, rhsTy? with
      | some lhsTy, some rhsTy =>
          some (Ty.matchesShape lhsTy targetTy ||
            Ty.matchesShape rhsTy targetTy)
      | some lhsTy, none => some (Ty.matchesShape lhsTy targetTy)
      | none, some rhsTy => some (Ty.matchesShape rhsTy targetTy)
      | none, none => none
  | none => some true

def FunctionDecl.usingFreeFunctionArgs?
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (functionName : Name)
    (args : List Arg) : Option (List Expr) := do
  let candidates :=
    freeFunctions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == functionName &&
            fn.params.length == args.length + 1 &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  let shapeMatch? :=
    candidates.find? (fun fn =>
      match Args.toExprsForParams? (fn.params.drop 1) args with
      | some orderedArgs =>
          match
              Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
                functions freeFunctions env fn.params
              (receiver :: orderedArgs) with
          | some true => true
          | _ => false
      | none => false)
  let fn ←
    match shapeMatch? with
    | some fn => some fn
    | none =>
        -- Stage-4 (decf368 twin, using-for free functions): when no
        -- candidate passes the full shape gate, accept one whose FIRST
        -- param still matches the receiver and whose remaining args merely
        -- ORDER against its params — the arity fallback the internal-call
        -- path (`findInternalCalleeWithArgs?`) already has. Fires only on
        -- calls that previously failed to rewrite (fail-closed downstream).
        candidates.find? (fun fn =>
          match fn.params with
          | firstParam :: _ =>
              (match
                  Parameter.matchesArgAllowingInternalFunctionName?
                    env firstParam receiver with
              | some true =>
                  (Args.toExprsForParams? (fn.params.drop 1) args).isSome
              | _ => false)
          | [] => false)
  let orderedArgs ← Args.toExprsForParams? (fn.params.drop 1) args
  some (receiver :: orderedArgs)

def FunctionDecl.usingFreeFunctionOperands?
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (targetTy? : Option Ty) (functionName : Name)
    (operands : List Expr) : Option (List Expr) := do
  let candidates :=
    freeFunctions.filter (fun fn =>
      match fn.name with
      | some fnName =>
          fnName == functionName &&
            fn.params.length == operands.length &&
            FunctionDecl.isExternallyNamedFunction fn
      | none => false)
  let _ ←
    match
        candidates.find? (fun fn =>
          match
              Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
                functions freeFunctions env fn.params operands with
          | some true => true
          | _ => false) with
    | some fn => some fn
    | none =>
        -- ITEM-5 (operator using-for, SOUND fallback): solc's operator
        -- binding rule (`using {f as +} for T global`) requires the bound
        -- free function's parameters to ALL be exactly the target UDVT `T`
        -- (TypeChecker: "operands of user-defined operators must all have
        -- the same user-defined value type"), so among same-name/same-arity
        -- candidates the one whose EVERY parameter type matches the using
        -- directive's target IS the solc binding — no overload ambiguity is
        -- possible. This fires only when the operand shape gate above found
        -- no candidate (an operand `Expr.abiTy*` cannot type, e.g. a nested
        -- rewritten operator call), i.e. only on previously fail-closed
        -- calls, so accepted programs keep their byte-identical lowering.
        match targetTy? with
        | some targetTy =>
            candidates.find? (fun fn =>
              !fn.params.isEmpty &&
                fn.params.all (fun p =>
                  p.ty == targetTy ||
                    Ty.matchesShape p.ty targetTy ||
                    Ty.matchesShape targetTy p.ty))
        | none => none
  some operands

def Path.qualifyIfUnqualified (scope : Name) (path : Path) : Path :=
  match path.segments with
  | [name] => { segments := [scope, name] }
  | _ => path

mutual

def Ty.qualifyUnqualifiedUserTypes (scope : Name) : Ty -> Ty
  | Ty.array element size =>
      Ty.array (Ty.qualifyUnqualifiedUserTypes scope element) size
  | Ty.mapping key value =>
      Ty.mapping
        (Ty.qualifyUnqualifiedUserTypes scope key)
        (Ty.qualifyUnqualifiedUserTypes scope value)
  | Ty.tuple tys =>
      Ty.tuple (tys.map (Ty.qualifyUnqualifiedUserTypes scope))
  | Ty.struct path tys =>
      Ty.struct
        (Path.qualifyIfUnqualified scope path)
        (tys.map (Ty.qualifyUnqualifiedUserTypes scope))
  | Ty.user path =>
      Ty.user (Path.qualifyIfUnqualified scope path)
  | Ty.functionWithLocations params paramLocations returns returnLocations
      mutability visibility =>
      Ty.functionWithLocations
        (params.map (Ty.qualifyUnqualifiedUserTypes scope))
        paramLocations
        (returns.map (Ty.qualifyUnqualifiedUserTypes scope))
        returnLocations mutability visibility
  | other => other

end

def Parameter.qualifyUnqualifiedUserTypes (scope : Name)
    (param : Parameter) : Parameter :=
  { param with ty := Ty.qualifyUnqualifiedUserTypes scope param.ty }

def FunctionDecl.qualifyUnqualifiedUserTypes (scope : Name)
    (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    params := decl.params.map (Parameter.qualifyUnqualifiedUserTypes scope)
    returns := decl.returns.map (Parameter.qualifyUnqualifiedUserTypes scope) }

def FunctionDecl.rewriteUsingLibraryCandidateWithSignature?
    (_libraryName _method : Name) (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (helperName : Name) (sourceFn matchFn : FunctionDecl) : Option Expr := do
  let firstMatches ←
    FunctionDecl.firstParamMatchesWithInternalFunctions?
      functions freeFunctions env receiver matchFn
  if firstMatches then
    some ()
  else
    none
  let orderedArgs ← Args.toExprsForParams? (matchFn.params.drop 1) args
  match
      Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
        functions freeFunctions env matchFn.params
        (receiver :: orderedArgs) with
  | some true =>
      some <|
        FunctionDecl.annotateSingleCoreReturn sourceFn
          (Expr.call
            (Expr.ident helperName)
            ((receiver :: orderedArgs).map Arg.positional))
  | _ => none

def FunctionDecl.rewriteUsingLibraryCandidate? (libraryName _method : Name)
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (helperName : Name) (fn : FunctionDecl) : Option Expr :=
  match
      FunctionDecl.rewriteUsingLibraryCandidateWithSignature?
        libraryName _method functions freeFunctions env receiver args
        helperName fn fn with
  | some rewritten => some rewritten
  | none =>
      let matchFn := FunctionDecl.qualifyUnqualifiedUserTypes libraryName fn
      FunctionDecl.rewriteUsingLibraryCandidateWithSignature?
        libraryName _method functions freeFunctions env receiver args
        helperName fn matchFn

def FunctionDecl.rewriteUsingExternalLibraryCandidateWithSignature?
    (_libraryName method : Name) (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (sourceFn matchFn : FunctionDecl) : Option Expr := do
  let firstMatches ←
    FunctionDecl.firstParamMatchesWithInternalFunctions?
      functions freeFunctions env receiver matchFn
  if firstMatches then
    some ()
  else
    none
  let orderedArgs ← Args.toExprsForParams? (matchFn.params.drop 1) args
  match
      Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
        functions freeFunctions env matchFn.params
        (receiver :: orderedArgs) with
  | some true =>
      some <|
        FunctionDecl.annotateSingleCoreReturn sourceFn
          (Expr.call
            (Expr.member (Expr.ident (generatedLibraryAddressIdent _libraryName))
              method)
            ((receiver :: orderedArgs).map Arg.positional))
  | _ => none

def FunctionDecl.rewriteUsingExternalLibraryCandidate? (libraryName method : Name)
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (fn : FunctionDecl) : Option Expr :=
  match
      FunctionDecl.rewriteUsingExternalLibraryCandidateWithSignature?
        libraryName method functions freeFunctions env receiver args fn fn with
  | some rewritten => some rewritten
  | none =>
      let matchFn := FunctionDecl.qualifyUnqualifiedUserTypes libraryName fn
      FunctionDecl.rewriteUsingExternalLibraryCandidateWithSignature?
        libraryName method functions freeFunctions env receiver args fn matchFn

def FunctionDecls.rewriteUsingLibraryCandidateFrom? (libraryName method : Name)
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg) (index : Nat) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      let helperName := libraryHelperNameForIndex libraryName method index
      match
          FunctionDecl.rewriteUsingLibraryCandidate?
            libraryName method functions freeFunctions env receiver args
            helperName fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteUsingLibraryCandidateFrom?
            libraryName method functions freeFunctions env receiver args
            (index + 1) rest

/-- Stage-4 (decf368 twin, attached path): arity fallback for an attached
    using-for library call whose ARG shape the gate does not model (e.g. an
    explicit enum-conversion argument reported as its underlying uint). The
    receiver-first-param gate is KEPT — it is the attachment selector — and
    only the argument shape check is relaxed to ordering. Fires only when the
    shape-gated scan found NO candidate, i.e. only on calls that previously
    failed to rewrite (fail-closed downstream), so accepted programs are
    unchanged. -/
def FunctionDecl.rewriteUsingLibraryCandidateByArity?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (receiver : Expr) (args : List Arg) (helperName : Name)
    (fn : FunctionDecl) : Option Expr := do
  let firstMatches ←
    FunctionDecl.firstParamMatchesWithInternalFunctions?
      functions freeFunctions env receiver fn
  if firstMatches then some () else none
  let orderedArgs ← Args.toExprsForParams? (fn.params.drop 1) args
  -- Wrong-callee guard: exclude a same-arity overload whose KNOWN arg types
  -- definitely mismatch (`Parameters.arityFallbackCompatible`);
  -- accept-when-unknown preserved.
  if Parameters.arityFallbackCompatible env (fn.params.drop 1) orderedArgs then
    some <|
      FunctionDecl.annotateSingleCoreReturn fn
        (Expr.call (Expr.ident helperName)
          ((receiver :: orderedArgs).map Arg.positional))
  else
    none

def FunctionDecls.rewriteUsingLibraryCandidateByArityFrom?
    (functions freeFunctions : List FunctionDecl) (env : TypeEnv)
    (libraryName method : Name) (receiver : Expr) (args : List Arg)
    (index : Nat) : List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      let helperName := libraryHelperNameForIndex libraryName method index
      match
          FunctionDecl.rewriteUsingLibraryCandidateByArity?
            functions freeFunctions env receiver args helperName fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteUsingLibraryCandidateByArityFrom?
            functions freeFunctions env libraryName method receiver args
            (index + 1) rest

def FunctionDecls.rewriteUsingLibraryCandidate? (libraryName method : Name)
    (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (candidates : List FunctionDecl) : Option Expr :=
  match
      FunctionDecls.rewriteUsingLibraryCandidateFrom?
        libraryName method functions freeFunctions env receiver args 0
        candidates with
  | some rewritten => some rewritten
  | none =>
      FunctionDecls.rewriteUsingLibraryCandidateByArityFrom?
        functions freeFunctions env libraryName method receiver args 0
        candidates

def FunctionDecls.rewriteUsingExternalLibraryCandidateGated?
    (libraryName method : Name) (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      match
          FunctionDecl.rewriteUsingExternalLibraryCandidate?
            libraryName method functions freeFunctions env receiver args fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteUsingExternalLibraryCandidateGated?
            libraryName method functions freeFunctions env receiver args rest

/-- Stage-4 (decf368 twin, attached EXTERNAL path): the same arity fallback as
    the internal attached path — receiver gate kept, args relaxed to
    ordering; fires only when the shape-gated scan found nothing. -/
def FunctionDecls.rewriteUsingExternalLibraryCandidateByArity?
    (libraryName method : Name) (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      (match (do
          let firstMatches ←
            FunctionDecl.firstParamMatchesWithInternalFunctions?
              functions freeFunctions env receiver fn
          if firstMatches then some () else none
          let orderedArgs ← Args.toExprsForParams? (fn.params.drop 1) args
          -- Wrong-callee guard: same `Parameters.arityFallbackCompatible`
          -- filter as the internal attached-path fallback.
          if Parameters.arityFallbackCompatible env
              (fn.params.drop 1) orderedArgs then
            some <|
              FunctionDecl.annotateSingleCoreReturn fn
                (Expr.call
                  (Expr.member
                    (Expr.ident (generatedLibraryAddressIdent libraryName))
                    method)
                  ((receiver :: orderedArgs).map Arg.positional))
          else
            none) with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteUsingExternalLibraryCandidateByArity?
            libraryName method functions freeFunctions env receiver args rest)

def FunctionDecls.rewriteUsingExternalLibraryCandidate?
    (libraryName method : Name) (functions freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (args : List Arg)
    (candidates : List FunctionDecl) : Option Expr :=
  match
      FunctionDecls.rewriteUsingExternalLibraryCandidateGated?
        libraryName method functions freeFunctions env receiver args
        candidates with
  | some rewritten => some rewritten
  | none =>
      FunctionDecls.rewriteUsingExternalLibraryCandidateByArity?
        libraryName method functions freeFunctions env receiver args
        candidates

def UsingFunction.rewriteCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) (binding : UsingFunction) : Option Expr := do
  match binding.operator? with
  | some _ => none
  | none => some ()
  let (libraryPath, functionName) ← pathInitLast? binding.function
  if functionName == method then
    some ()
  else
    none
  if libraryPath.segments.isEmpty then
    let orderedArgs ←
      FunctionDecl.usingFreeFunctionArgs?
        freeFunctions freeFunctions env receiver functionName args
    some
      (Expr.call (Expr.ident functionName)
        (orderedArgs.map Arg.positional))
  else
    let libraryName ← pathLast? libraryPath
    let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
    FunctionDecls.rewriteUsingLibraryCandidate?
      libraryName functionName freeFunctions freeFunctions env receiver args
      (ContractDecl.ordinaryFunctionsByName libraryDecl functionName)

def UsingFunction.rewriteBinaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (targetTy? : Option Ty) (op : BinaryOp) (lhs rhs : Expr)
    (binding : UsingFunction) : Option Expr := do
  match binding.operator? with
  | some (UsingOperator.binary bindingOp) =>
      if bindingOp == op then some () else none
  | _ => none
  let (libraryPath, functionName) ← pathInitLast? binding.function
  if libraryPath.segments.isEmpty then
    some ()
  else
    none
  let orderedArgs ←
    FunctionDecl.usingFreeFunctionOperands?
      freeFunctions freeFunctions env targetTy? functionName [lhs, rhs]
  some
    (Expr.call (Expr.ident functionName)
      (orderedArgs.map Arg.positional))

def UsingFunction.rewriteUnaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (targetTy? : Option Ty) (op : UnaryOp) (operand : Expr)
    (binding : UsingFunction) : Option Expr := do
  match binding.operator? with
  | some (UsingOperator.unary bindingOp) =>
      if bindingOp == op then some () else none
  | _ => none
  let (libraryPath, functionName) ← pathInitLast? binding.function
  if libraryPath.segments.isEmpty then
    some ()
  else
    none
  let orderedArgs ←
    FunctionDecl.usingFreeFunctionOperands?
      freeFunctions freeFunctions env targetTy? functionName [operand]
  some
    (Expr.call (Expr.ident functionName)
      (orderedArgs.map Arg.positional))

def UsingFunctions.rewriteCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : List UsingFunction -> Option Expr
  | [] => none
  | binding :: rest =>
      match
          UsingFunction.rewriteCall?
            contracts freeFunctions env receiver method args binding with
      | some rewritten => some rewritten
      | none =>
          UsingFunctions.rewriteCall?
            contracts freeFunctions env receiver method args rest

def UsingFunctions.rewriteBinaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (targetTy? : Option Ty) (op : BinaryOp) (lhs rhs : Expr) :
    List UsingFunction -> Option Expr
  | [] => none
  | binding :: rest =>
      match
          UsingFunction.rewriteBinaryOperator?
            freeFunctions env targetTy? op lhs rhs binding with
      | some rewritten => some rewritten
      | none =>
          UsingFunctions.rewriteBinaryOperator?
            freeFunctions env targetTy? op lhs rhs rest

def UsingFunctions.rewriteUnaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (targetTy? : Option Ty) (op : UnaryOp) (operand : Expr) :
    List UsingFunction -> Option Expr
  | [] => none
  | binding :: rest =>
      match
          UsingFunction.rewriteUnaryOperator?
            freeFunctions env targetTy? op operand binding with
      | some rewritten => some rewritten
      | none =>
          UsingFunctions.rewriteUnaryOperator?
            freeFunctions env targetTy? op operand rest

def UsingDecl.rewriteCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) (decl : UsingDecl) : Option Expr :=
  match
      UsingDecl.targetMatchesWithInternalFunctions?
        freeFunctions freeFunctions env receiver decl with
  | some true =>
      if !decl.functions.isEmpty then
        UsingFunctions.rewriteCall?
          contracts freeFunctions env receiver method args decl.functions
      else
        do
        let libraryName ← pathLast? decl.library
        let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
        FunctionDecls.rewriteUsingLibraryCandidate?
          libraryName method freeFunctions freeFunctions env receiver args
          (ContractDecl.ordinaryFunctionsByName libraryDecl method)
  | _ => none

def UsingDecl.rewriteBinaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (op : BinaryOp) (lhs rhs : Expr)
    (decl : UsingDecl) : Option Expr :=
  match
      UsingDecl.targetMatchesBinaryWithInternalFunctions?
        freeFunctions freeFunctions env lhs rhs decl with
  | some true =>
      UsingFunctions.rewriteBinaryOperator?
        freeFunctions env decl.target op lhs rhs decl.functions
  | _ => none

def UsingDecl.rewriteUnaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (op : UnaryOp) (operand : Expr)
    (decl : UsingDecl) : Option Expr :=
  match
      UsingDecl.targetMatchesWithInternalFunctions?
        freeFunctions freeFunctions env operand decl with
  | some true =>
      UsingFunctions.rewriteUnaryOperator?
        freeFunctions env decl.target op operand decl.functions
  | _ => none

def libraryExternalCallTarget (libraryName method : Name) : Expr :=
  Expr.member (Expr.ident (generatedLibraryAddressIdent libraryName)) method

/-- The struct/user path a resolved type points at, if any. Post-`resolveStructs`
    a struct type is `Ty.struct path _`; before it (or for a mapping's user value)
    it can still be `Ty.user path`. -/
def Ty.structPath? : Ty -> Option Path
  | Ty.user path => some path
  | Ty.struct path _ => some path
  | _ => none

/-- Find a struct declaration named `name` anywhere in the contract set. Field
    names survive `resolveStructs` (only field TYPES are resolved), so this
    recovers the field ordering a resolved `Ty.struct` type has dropped. -/
def ContractDecls.findStructDeclByName? (contracts : List ContractDecl)
    (name : Name) : Option StructDecl :=
  contracts.findSome? (fun decl =>
    decl.items.findSome? (fun item =>
      match item with
      | ContractItem.structDecl structDecl =>
          if structDecl.name == name then some structDecl else none
      | _ => none))

/-- The struct declaration of a callee's single STRUCT return. Used to recover
    field ordering so `.field` on a call result lowers to `[fieldIndex]` for
    both memory values and storage references.

    Historically this gated on the WHOLE-param `return s;` shape only, because
    the boundary did not re-base nested sub-path returns. Since the R3 (#188)
    runtime re-pointing, a returned storage pointer from a nested path / local /
    conditional return resolves onto the caller's storage, so the gate is the
    widened predicate; each newly-rewritten callee shape is pinned against the
    real EVM in `tests/forge-harness/storage-return-subfield-ops`. -/
def Expr.callSingleStorageStructReturnDecl?
    (contracts : List ContractDecl) (freeFunctions : List FunctionDecl) :
    Expr -> Option StructDecl
  | Expr.call (Expr.member (Expr.typeName (Ty.user libraryPath)) method) _ => do
      let libraryName ← pathLast? libraryPath
      let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
      let fn ← ContractDecl.findOrdinaryFunctionByName? libraryDecl method
      match fn.returns with
      | [ret] => do
          let path ← Ty.structPath? ret.ty
          let structName ← pathLast? path
          ContractDecls.findStructDeclByName? contracts structName
      | _ => none
  | Expr.call (Expr.ident name) _ => do
      let fn ← freeFunctions.find? (fun fn => fn.name == some name)
      match fn.returns with
      | [ret] => do
          let path ← Ty.structPath? ret.ty
          let structName ← pathLast? path
          ContractDecls.findStructDeclByName? contracts structName
      | _ => none
  | _ => none

def UsingFunction.rewriteExternalCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) (binding : UsingFunction) : Option Expr := do
  match binding.operator? with
  | some _ => none
  | none => some ()
  let (libraryPath, functionName) ← pathInitLast? binding.function
  if functionName == method && !libraryPath.segments.isEmpty then
    some ()
  else
    none
  let libraryName ← pathLast? libraryPath
  let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
  FunctionDecls.rewriteUsingExternalLibraryCandidate?
    libraryName functionName freeFunctions freeFunctions env receiver args
    (ContractDecl.externalLibraryFunctionsByName libraryDecl functionName)

def UsingFunctions.rewriteExternalCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : List UsingFunction -> Option Expr
  | [] => none
  | binding :: rest =>
      match
          UsingFunction.rewriteExternalCall?
            contracts freeFunctions env receiver method args binding with
      | some rewritten => some rewritten
      | none =>
          UsingFunctions.rewriteExternalCall?
            contracts freeFunctions env receiver method args rest

def UsingDecl.rewriteExternalCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) (decl : UsingDecl) : Option Expr :=
  match
      UsingDecl.targetMatchesWithInternalFunctions?
        freeFunctions freeFunctions env receiver decl with
  | some true =>
      if !decl.functions.isEmpty then
        UsingFunctions.rewriteExternalCall?
          contracts freeFunctions env receiver method args decl.functions
      else
        do
        let libraryName ← pathLast? decl.library
        let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
        FunctionDecls.rewriteUsingExternalLibraryCandidate?
          libraryName method freeFunctions freeFunctions env receiver args
          (ContractDecl.externalLibraryFunctionsByName libraryDecl method)
  | _ => none

def UsingDecls.rewriteCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : List UsingDecl -> Option Expr
  | [] => none
  | decl :: rest =>
      match
          UsingDecl.rewriteCall?
            contracts freeFunctions env receiver method args decl with
      | some rewritten => some rewritten
      | none =>
          UsingDecls.rewriteCall?
            contracts freeFunctions env receiver method args rest

def UsingDecls.rewriteBinaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (op : BinaryOp) (lhs rhs : Expr) :
    List UsingDecl -> Option Expr
  | [] => none
  | decl :: rest =>
      match UsingDecl.rewriteBinaryOperator?
          freeFunctions env op lhs rhs decl with
      | some rewritten => some rewritten
      | none =>
          UsingDecls.rewriteBinaryOperator?
            freeFunctions env op lhs rhs rest

def UsingDecls.rewriteUnaryOperator? (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (op : UnaryOp) (operand : Expr) :
    List UsingDecl -> Option Expr
  | [] => none
  | decl :: rest =>
      match UsingDecl.rewriteUnaryOperator?
          freeFunctions env op operand decl with
      | some rewritten => some rewritten
      | none =>
          UsingDecls.rewriteUnaryOperator?
            freeFunctions env op operand rest

def UsingDecls.rewriteExternalCall? (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : List UsingDecl -> Option Expr
  | [] => none
  | decl :: rest =>
      match
          UsingDecl.rewriteExternalCall?
            contracts freeFunctions env receiver method args decl with
      | some rewritten => some rewritten
      | none =>
          UsingDecls.rewriteExternalCall?
            contracts freeFunctions env receiver method args rest

def FunctionDecl.rewriteLibraryDirectCallCandidateWithSignature?
    (_libraryName _method : Name)
    (env : TypeEnv) (args : List Arg) (helperName : Name)
    (sourceFn matchFn : FunctionDecl) : Option Expr := do
  let orderedArgs ← Args.toExprsForParams? matchFn.params args
  match
      Parameters.matchArgsAllowingInternalFunctionNamesWithEnv?
        env matchFn.params orderedArgs with
  | some true =>
      some <|
        FunctionDecl.annotateSingleCoreReturn sourceFn
          (Expr.call (Expr.ident helperName)
            (orderedArgs.map Arg.positional))
  | _ => none

def FunctionDecl.rewriteLibraryDirectCallCandidate? (libraryName _method : Name)
    (env : TypeEnv) (args : List Arg) (helperName : Name)
    (fn : FunctionDecl) : Option Expr :=
  match
      FunctionDecl.rewriteLibraryDirectCallCandidateWithSignature?
        libraryName _method env args helperName fn fn with
  | some rewritten => some rewritten
  | none =>
      let matchFn := FunctionDecl.qualifyUnqualifiedUserTypes libraryName fn
      FunctionDecl.rewriteLibraryDirectCallCandidateWithSignature?
        libraryName _method env args helperName fn matchFn

def FunctionDecls.rewriteLibraryDirectCallCandidateFrom?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg)
    (index : Nat) : List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      let helperName := libraryHelperNameForIndex libraryName method index
      match
          FunctionDecl.rewriteLibraryDirectCallCandidate?
            libraryName method env args helperName fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteLibraryDirectCallCandidateFrom?
            libraryName method env args (index + 1) rest

/-- Arity fallback: accept a candidate whose args order against its params
    without the exact shape gate, EXCLUDING candidates whose param types are
    definitely incompatible with the args
    (`Parameters.arityFallbackCompatible`). -/
def FunctionDecl.rewriteLibraryDirectCallCandidateByArity?
    (env : TypeEnv) (args : List Arg) (helperName : Name)
    (fn : FunctionDecl) : Option Expr := do
  let orderedArgs ← Args.toExprsForParams? fn.params args
  if Parameters.arityFallbackCompatible env fn.params orderedArgs then
    some <|
      FunctionDecl.annotateSingleCoreReturn fn
        (Expr.call (Expr.ident helperName)
          (orderedArgs.map Arg.positional))
  else
    none

def FunctionDecls.rewriteLibraryDirectCallCandidateByArityFrom?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg)
    (index : Nat) : List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      let helperName := libraryHelperNameForIndex libraryName method index
      match
          FunctionDecl.rewriteLibraryDirectCallCandidateByArity?
            env args helperName fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteLibraryDirectCallCandidateByArityFrom?
            libraryName method env args (index + 1) rest

def FunctionDecls.rewriteLibraryDirectCallCandidate?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg)
    (candidates : List FunctionDecl) : Option Expr :=
  match
      FunctionDecls.rewriteLibraryDirectCallCandidateFrom?
        libraryName method env args 0 candidates with
  | some rewritten => some rewritten
  | none =>
      -- The shape gate lacks the arity fallback the contract-internal path
      -- (`findInternalCalleeWithArgs?`) has, so shapes it does not model
      -- would otherwise leave the call unrewritten. The fallback is
      -- type-safe: definitely-incompatible same-arity overloads are excluded
      -- (`Parameters.arityFallbackCompatible`).
      FunctionDecls.rewriteLibraryDirectCallCandidateByArityFrom?
        libraryName method env args 0 candidates

def libraryDirectCallRewrite? (contracts : List ContractDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : Option Expr := do
  let libraryName ←
    match receiver with
    | Expr.ident name => some name
    | Expr.typeName (Ty.user path) => pathLast? path
    | _ => none
  let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
  let candidates := ContractDecl.ordinaryFunctionsByName libraryDecl method
  FunctionDecls.rewriteLibraryDirectCallCandidate?
    libraryName method env args candidates

def FunctionDecl.rewriteLibraryExternalDirectCallCandidateWithSignature?
    (libraryName method : Name)
    (env : TypeEnv) (args : List Arg)
    (sourceFn matchFn : FunctionDecl) : Option Expr := do
  let orderedArgs ← Args.toExprsForParams? matchFn.params args
  match Parameters.matchArgsWithEnv? env matchFn.params orderedArgs with
  | some true =>
      some <|
        FunctionDecl.annotateSingleCoreReturn sourceFn
          (Expr.call (libraryExternalCallTarget libraryName method)
            (orderedArgs.map Arg.positional))
  | _ => none

def FunctionDecl.rewriteLibraryExternalDirectCallCandidate?
    (libraryName method : Name)
    (env : TypeEnv) (args : List Arg) (fn : FunctionDecl) : Option Expr :=
  match
      FunctionDecl.rewriteLibraryExternalDirectCallCandidateWithSignature?
        libraryName method env args fn fn with
  | some rewritten => some rewritten
  | none =>
      let matchFn := FunctionDecl.qualifyUnqualifiedUserTypes libraryName fn
      FunctionDecl.rewriteLibraryExternalDirectCallCandidateWithSignature?
        libraryName method env args fn matchFn

def FunctionDecls.rewriteLibraryExternalDirectCallCandidateFrom?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      match
          FunctionDecl.rewriteLibraryExternalDirectCallCandidate?
            libraryName method env args fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteLibraryExternalDirectCallCandidateFrom?
            libraryName method env args rest

/-- Stage-4 (decf368 twin, external/public direct path): arity fallback —
    accept a candidate whose args order against its params without the exact
    shape gate, EXCLUDING definitely-incompatible candidates
    (`Parameters.arityFallbackCompatible`). -/
def FunctionDecl.rewriteLibraryExternalDirectCallCandidateByArity?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg)
    (fn : FunctionDecl) : Option Expr := do
  let orderedArgs ← Args.toExprsForParams? fn.params args
  if Parameters.arityFallbackCompatible env fn.params orderedArgs then
    some <|
      FunctionDecl.annotateSingleCoreReturn fn
        (Expr.call (libraryExternalCallTarget libraryName method)
          (orderedArgs.map Arg.positional))
  else
    none

def FunctionDecls.rewriteLibraryExternalDirectCallCandidateByArityFrom?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      match
          FunctionDecl.rewriteLibraryExternalDirectCallCandidateByArity?
            libraryName method env args fn with
      | some rewritten => some rewritten
      | none =>
          FunctionDecls.rewriteLibraryExternalDirectCallCandidateByArityFrom?
            libraryName method env args rest

def FunctionDecls.rewriteLibraryExternalDirectCallCandidate?
    (libraryName method : Name) (env : TypeEnv) (args : List Arg)
    (candidates : List FunctionDecl) : Option Expr :=
  match
      FunctionDecls.rewriteLibraryExternalDirectCallCandidateFrom?
        libraryName method env args candidates with
  | some rewritten => some rewritten
  | none =>
      -- The shape gate lacks the arity fallback the contract-internal path
      -- (`findInternalCalleeWithArgs?`) and the internal-visibility direct
      -- library path (decf368) have, so shapes it does not model (e.g. an
      -- explicit enum-conversion argument reported as its underlying uint)
      -- would otherwise leave a `public`/`external` library direct call
      -- unrewritten — poisoning the whole contract's elaboration. The
      -- fallback is type-safe: definitely-incompatible same-arity overloads
      -- are excluded (`Parameters.arityFallbackCompatible`).
      FunctionDecls.rewriteLibraryExternalDirectCallCandidateByArityFrom?
        libraryName method env args candidates

def libraryExternalDirectCallRewrite? (contracts : List ContractDecl)
    (env : TypeEnv) (receiver : Expr) (method : Name)
    (args : List Arg) : Option Expr := do
  let libraryName ←
    match receiver with
    | Expr.ident name => some name
    | Expr.typeName (Ty.user path) => pathLast? path
    | _ => none
  let libraryDecl ← ContractDecl.findLibraryByName? contracts libraryName
  let candidates := ContractDecl.externalLibraryFunctionsByName libraryDecl method
  FunctionDecls.rewriteLibraryExternalDirectCallCandidate?
    libraryName method env args candidates

mutual

def Expr.expandUsingFuel :
    Nat -> List ContractDecl -> List FunctionDecl -> List UsingDecl ->
    TypeEnv -> Expr -> Expr
  | 0, _, _, _, _, expr => expr
  | fuel + 1, contracts, freeFunctions, usingDecls, env, expr =>
      let expand :=
        Expr.expandUsingFuel fuel contracts freeFunctions usingDecls env
      let expandArg :=
        Arg.expandUsingFuel fuel contracts freeFunctions usingDecls env
      let expandOption :=
        CallOption.expandUsingFuel fuel contracts freeFunctions usingDecls env
      let expandTupleItem :=
        TupleItem.expandUsingFuel fuel contracts freeFunctions usingDecls env
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member =>
          -- LIB-STORAGE-RETURN-USE (#156): `L.ref(s).x` / `f(s).x` on a call
          -- whose single return is a `storage` struct reference. `resolveStructs`
          -- cannot type a call result, so `.x` never became `[fieldIndex]`;
          -- recover the struct declaration from the callee and rewrite the field
          -- access to an index over the (expanded) call, which the storage-ref
          -- lowering handles. Non-call / non-struct-storage bases are untouched.
          match Expr.callSingleStorageStructReturnDecl? contracts freeFunctions base with
          | some structDecl =>
              match StructDecl.fieldIndex? structDecl member with
              | some index =>
                  Expr.index (expand base)
                    (Expr.literal (Literal.number (toString index)))
              | none => Expr.member (expand base) member
          | none => Expr.member (expand base) member
      | Expr.index base index => Expr.index (expand base) (expand index)
      | Expr.slice base start stop =>
          Expr.slice (expand base) (start.map expand) (stop.map expand)
      | Expr.call (Expr.typeName ty@(Ty.address _))
          [Arg.positional (Expr.ident libraryName)] =>
          match ContractDecl.findLibraryByName? contracts libraryName with
          | some _ =>
              Expr.call (Expr.typeName ty)
                [Arg.positional
                  (Expr.ident (generatedLibraryAddressIdent libraryName))]
          | none =>
              Expr.call (Expr.typeName ty)
                [Arg.positional (Expr.ident libraryName)]
      | Expr.call (Expr.member receiver method) args =>
          let receiver' := expand receiver
          let args' := args.map expandArg
          match libraryDirectCallRewrite? contracts env receiver' method args' with
          | some rewritten => rewritten
          | none =>
              match
                  libraryExternalDirectCallRewrite?
                    contracts env receiver' method args' with
              | some rewritten => rewritten
              | none =>
                  match UsingDecls.rewriteCall?
                      contracts freeFunctions env receiver' method args'
                      usingDecls with
                  | some rewritten => rewritten
                  | none =>
                      match UsingDecls.rewriteExternalCall?
                          contracts freeFunctions env receiver' method args'
                          usingDecls with
                      | some rewritten => rewritten
                      | none => Expr.call (Expr.member receiver' method) args'
      | Expr.call fn args =>
          Expr.call (expand fn) (args.map expandArg)
      | Expr.callWithOptions (Expr.member receiver method) options args =>
          let receiver' := expand receiver
          let options' := options.map expandOption
          let args' := args.map expandArg
          match libraryDirectCallRewrite? contracts env receiver' method args' with
          | some rewritten =>
              match rewritten with
              | Expr.call fn args => Expr.callWithOptions fn options' args
              | other => other
          | none =>
              match
                  libraryExternalDirectCallRewrite?
                    contracts env receiver' method args' with
              | some rewritten =>
                  match rewritten with
                  | Expr.call fn args => Expr.callWithOptions fn options' args
                  | other => other
              | none =>
                  match UsingDecls.rewriteCall?
                      contracts freeFunctions env receiver' method args'
                      usingDecls with
                  | some rewritten =>
                      match rewritten with
                      | Expr.call fn args =>
                          Expr.callWithOptions fn options' args
                      | other => other
                  | none =>
                      match UsingDecls.rewriteExternalCall?
                          contracts freeFunctions env receiver' method args'
                          usingDecls with
                      | some rewritten =>
                          match rewritten with
                          | Expr.call fn args =>
                              Expr.callWithOptions fn options' args
                          | other => other
                      | none =>
                          Expr.callWithOptions
                            (Expr.member receiver' method) options' args'
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (expand fn)
            (options.map expandOption) (args.map expandArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map expandArg)
      | Expr.tuple items => Expr.tuple (items.map expandTupleItem)
      | Expr.array exprs => Expr.array (exprs.map expand)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (expand inner)
      | Expr.unary op inner =>
          let inner' := expand inner
          match UsingDecls.rewriteUnaryOperator?
              freeFunctions env op inner' usingDecls with
          | some rewritten => rewritten
          | none => Expr.unary op inner'
      | Expr.binary op lhs rhs =>
          let lhs' := expand lhs
          let rhs' := expand rhs
          match UsingDecls.rewriteBinaryOperator?
              freeFunctions env op lhs' rhs' usingDecls with
          | some rewritten => rewritten
          | none => Expr.binary op lhs' rhs'
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (expand cond) (expand thenExpr) (expand elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (expand lhs) op (expand rhs)
      | Expr.payableConversion inner => Expr.payableConversion (expand inner)

def Arg.expandUsingFuel :
    Nat -> List ContractDecl -> List FunctionDecl -> List UsingDecl ->
    TypeEnv -> Arg -> Arg
  | 0, _, _, _, _, arg => arg
  | fuel + 1, contracts, freeFunctions, usingDecls, env, arg =>
      let expand :=
        Expr.expandUsingFuel fuel contracts freeFunctions usingDecls env
      match arg with
      | Arg.positional expr => Arg.positional (expand expr)
      | Arg.named name expr => Arg.named name (expand expr)

def CallOption.expandUsingFuel :
    Nat -> List ContractDecl -> List FunctionDecl -> List UsingDecl ->
    TypeEnv -> CallOption -> CallOption
  | 0, _, _, _, _, option => option
  | fuel + 1, contracts, freeFunctions, usingDecls, env, option =>
      let expand :=
        Expr.expandUsingFuel fuel contracts freeFunctions usingDecls env
      match option with
      | CallOption.named name expr => CallOption.named name (expand expr)

def TupleItem.expandUsingFuel :
    Nat -> List ContractDecl -> List FunctionDecl -> List UsingDecl ->
    TypeEnv -> TupleItem -> TupleItem
  | 0, _, _, _, _, item => item
  | fuel + 1, contracts, freeFunctions, usingDecls, env, item =>
      let expand :=
        Expr.expandUsingFuel fuel contracts freeFunctions usingDecls env
      match item with
      | TupleItem.hole => TupleItem.hole
      | TupleItem.value expr => TupleItem.value (expand expr)

end

def defaultExpandUsingFuel : Nat := 1024

def Expr.expandUsing (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (expr : Expr) : Expr :=
  Expr.expandUsingFuel
    defaultExpandUsingFuel contracts freeFunctions usingDecls env expr

def Arg.expandUsing (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (arg : Arg) : Arg :=
  Arg.expandUsingFuel
    defaultExpandUsingFuel contracts freeFunctions usingDecls env arg

inductive UsingExpansionKind where
  | unchanged
  | libraryHelper
  | externalLibrary
  | freeFunction
  | binaryOperator
  | unaryOperator
  deriving Repr, BEq

def Expr.callIdentName? : Expr -> Option Name
  | Expr.call (Expr.ident name) _ => some name
  | Expr.callWithOptions (Expr.ident name) _ _ => some name
  | Expr.call (Expr.typeName _) [Arg.positional inner] =>
      Expr.callIdentName? inner
  | _ => none

def Expr.callArgumentCount? : Expr -> Option Nat
  | Expr.call (Expr.typeName _) [Arg.positional inner] =>
      Expr.callArgumentCount? inner
  | Expr.call _ args => some args.length
  | Expr.callWithOptions _ _ args => some args.length
  | _ => none

def ContractItems.libraryHelperSourceFor? (libraryName helperName : Name) :
    List ContractItem -> Option (Name × Name)
  | [] => none
  | ContractItem.function fn :: rest =>
      match fn.name with
      | some functionName =>
          if FunctionDecl.isInlineLibraryFunction fn &&
              libraryHelperName libraryName functionName == helperName then
            some (libraryName, functionName)
          else
            ContractItems.libraryHelperSourceFor? libraryName helperName rest
      | none =>
          ContractItems.libraryHelperSourceFor? libraryName helperName rest
  | _ :: rest =>
      ContractItems.libraryHelperSourceFor? libraryName helperName rest

def ContractDecls.libraryHelperSourceFor?
    (contracts : List ContractDecl) (helperName : Name) :
    Option (Name × Name) :=
  match contracts with
  | [] => none
  | decl :: rest =>
      if ContractDecl.isLibrary decl then
        match ContractItems.libraryHelperSourceFor?
            decl.name helperName decl.items with
        | some source => some source
        | none => ContractDecls.libraryHelperSourceFor? rest helperName
      else
        ContractDecls.libraryHelperSourceFor? rest helperName

def ContractDecls.generatedLibraryAddressSourceFor?
    (contracts : List ContractDecl) (generatedName : Name) :
    Option Name :=
  match contracts with
  | [] => none
  | decl :: rest =>
      if ContractDecl.isLibrary decl &&
          generatedLibraryAddressIdent decl.name == generatedName then
        some decl.name
      else
        ContractDecls.generatedLibraryAddressSourceFor? rest generatedName

def Expr.externalLibraryCallSourceFor? (contracts : List ContractDecl) :
    Expr -> Option (Name × Name)
  | Expr.call (Expr.member (Expr.ident generatedName) method) _ => do
      let libraryName ←
        ContractDecls.generatedLibraryAddressSourceFor? contracts generatedName
      some (libraryName, method)
  | Expr.callWithOptions
      (Expr.member (Expr.ident generatedName) method) _ _ => do
      let libraryName ←
        ContractDecls.generatedLibraryAddressSourceFor? contracts generatedName
      some (libraryName, method)
  | Expr.call (Expr.typeName _) [Arg.positional inner] =>
      Expr.externalLibraryCallSourceFor? contracts inner
  | _ => none

def FunctionDecl.freeFunctionNames (functions : List FunctionDecl) :
    List Name :=
  functions.filterMap (fun fn => fn.name)

def UsingDecls.globalCount : List UsingDecl -> Nat
  | [] => 0
  | decl :: rest =>
      (if decl.global then 1 else 0) + UsingDecls.globalCount rest

def ModifierInvocation.expandUsing (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv)
    (invocation : ModifierInvocation) : ModifierInvocation :=
  { invocation with
    args :=
      invocation.args.map
        (Arg.expandUsing contracts freeFunctions usingDecls env) }

def Stmt.expandUsingInSeqFuel :
    Nat -> List ContractDecl -> List FunctionDecl -> List UsingDecl ->
    TypeEnv -> Stmt ->
    Stmt × TypeEnv
  | 0, _, _, _, env, stmt => (stmt, env)
  | fuel + 1, contracts, freeFunctions, usingDecls, env, stmt =>
      let expandExpr :=
        Expr.expandUsingFuel fuel contracts freeFunctions usingDecls env
      let expandStmt (child : Stmt) :=
        (Stmt.expandUsingInSeqFuel
          fuel contracts freeFunctions usingDecls env child).fst
      let expandSeq (seqEnv : TypeEnv) (body : List Stmt) :
          List Stmt × TypeEnv :=
        let step (acc : List Stmt × TypeEnv) (head : Stmt) :
            List Stmt × TypeEnv :=
          let (done, seqEnv) := acc
          let (head', seqEnv') :=
            Stmt.expandUsingInSeqFuel
              fuel contracts freeFunctions usingDecls seqEnv head
          (head' :: done, seqEnv')
        let (revBody, finalEnv) :=
          body.foldl step (([] : List Stmt), seqEnv)
        (revBody.reverse, finalEnv)
      let expandClause : CatchClause -> CatchClause
        | CatchClause.clause name params body =>
            let clauseEnv := Parameters.extendTypeEnv "_catch" env params
            CatchClause.clause name params
              ((Stmt.expandUsingInSeqFuel
                fuel contracts freeFunctions usingDecls clauseEnv body).fst)
      match stmt with
      | Stmt.empty => (Stmt.empty, env)
      | Stmt.block body =>
          let (body', _) := expandSeq env body
          (Stmt.block body', env)
      | Stmt.varDecl bindings init =>
          let init' := init.map expandExpr
          let env' := VarBindings.extendTypeEnv env bindings
          (Stmt.varDecl bindings init', env')
      | Stmt.expr expr => (Stmt.expr (expandExpr expr), env)
      | Stmt.ifElse cond thenBranch elseBranch =>
          (Stmt.ifElse (expandExpr cond) (expandStmt thenBranch)
            (elseBranch.map expandStmt), env)
      | Stmt.whileLoop cond body =>
          (Stmt.whileLoop (expandExpr cond) (expandStmt body), env)
      | Stmt.doWhile body cond =>
          (Stmt.doWhile (expandStmt body) (expandExpr cond), env)
      | Stmt.forLoop init cond post body =>
          let (init', loopEnv) :=
            match init with
            | some initStmt =>
                let (stmt', env') :=
                  Stmt.expandUsingInSeqFuel
                    fuel contracts freeFunctions usingDecls env initStmt
                (some stmt', env')
            | none => (none, env)
          let expandLoopExpr :=
            Expr.expandUsingFuel
              fuel contracts freeFunctions usingDecls loopEnv
          let body' :=
            (Stmt.expandUsingInSeqFuel
              fuel contracts freeFunctions usingDecls loopEnv body).fst
          (Stmt.forLoop init' (cond.map expandLoopExpr)
            (post.map expandLoopExpr) body', env)
      | Stmt.tryCatch expr clauses =>
          (Stmt.tryCatch (expandExpr expr) (clauses.map expandClause), env)
      | Stmt.tryCatchReturns expr returns success clauses =>
          let successEnv := Parameters.extendTypeEnv "_try" env returns
          let success' :=
            (Stmt.expandUsingInSeqFuel
              fuel contracts freeFunctions usingDecls successEnv success).fst
          (Stmt.tryCatchReturns (expandExpr expr) returns success'
            (clauses.map expandClause), env)
      | Stmt.emitEvent expr => (Stmt.emitEvent (expandExpr expr), env)
      | Stmt.revertCall expr => (Stmt.revertCall (expandExpr expr), env)
      | Stmt.returnValues expr? =>
          (Stmt.returnValues (expr?.map expandExpr), env)
      | Stmt.break => (Stmt.break, env)
      | Stmt.continue => (Stmt.continue, env)
      | Stmt.unchecked body => (Stmt.unchecked (expandStmt body), env)
      | Stmt.inlineAssembly code => (Stmt.inlineAssembly code, env)
      | Stmt.modifierPlaceholder => (Stmt.modifierPlaceholder, env)

def Stmt.expandUsing (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv) (stmt : Stmt) : Stmt :=
  (Stmt.expandUsingInSeqFuel
    defaultExpandUsingFuel contracts freeFunctions usingDecls env stmt).fst

def FunctionDecl.internalLibraryCallMatches? (libraryFunctions : List FunctionDecl)
    (env : TypeEnv) (args : List Arg) (decl : FunctionDecl) : Bool :=
  match FunctionDecl.orderedArgs? decl args with
  | some orderedArgs =>
      match
          Parameters.matchArgsAllowingInternalFunctionNamesWithFunctionsEnv?
            libraryFunctions libraryFunctions env decl.params orderedArgs with
      | some true => true
      | _ => false
  | none => false

def FunctionDecls.libraryInternalHelperCallByMatchFrom?
    (libraryName functionName : Name) (libraryFunctions : List FunctionDecl)
    (env : TypeEnv) (args : List Arg) (index : Nat) :
    List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      match fn.name with
      | some fnName =>
          if FunctionDecl.isInlineLibraryFunction fn && fnName == functionName then
            if FunctionDecl.internalLibraryCallMatches?
                libraryFunctions env args fn then
              some
                (Expr.ident
                  (libraryHelperNameForIndex libraryName functionName index))
            else
              FunctionDecls.libraryInternalHelperCallByMatchFrom?
                libraryName functionName libraryFunctions env args
                (index + 1) rest
          else
            FunctionDecls.libraryInternalHelperCallByMatchFrom?
              libraryName functionName libraryFunctions env args index rest
      | none =>
          FunctionDecls.libraryInternalHelperCallByMatchFrom?
            libraryName functionName libraryFunctions env args index rest

def FunctionDecls.libraryInternalHelperCallByArityFrom?
    (libraryName functionName : Name) (env : TypeEnv) (args : List Arg)
    (index : Nat) : List FunctionDecl -> Option Expr
  | [] => none
  | fn :: rest =>
      match fn.name with
      | some fnName =>
          if FunctionDecl.isInlineLibraryFunction fn && fnName == functionName then
            -- Wrong-callee guard: a same-arity overload whose KNOWN arg types
            -- definitely mismatch is excluded
            -- (`Parameters.arityFallbackCompatible`); args that fail to order
            -- against the params (`none`) cannot be disproven and keep the
            -- prior accept-by-arity behaviour.
            let compatible :=
              fn.params.length == args.length &&
                (match Args.toExprsForParams? fn.params args with
                 | some orderedArgs =>
                     Parameters.arityFallbackCompatible env fn.params
                       orderedArgs
                 | none => true)
            if compatible then
              some
                (Expr.ident
                  (libraryHelperNameForIndex libraryName functionName index))
            else
              FunctionDecls.libraryInternalHelperCallByArityFrom?
                libraryName functionName env args (index + 1) rest
          else
            FunctionDecls.libraryInternalHelperCallByArityFrom?
              libraryName functionName env args index rest
      | none =>
          FunctionDecls.libraryInternalHelperCallByArityFrom?
            libraryName functionName env args index rest

def libraryInternalHelperCall? (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv)
    (name : Name) (args : List Arg) : Option Expr :=
  match
      FunctionDecls.libraryInternalHelperCallByMatchFrom?
        libraryName name libraryFunctions env args 0 libraryFunctions with
  | some helper => some helper
  | none =>
      FunctionDecls.libraryInternalHelperCallByArityFrom?
        libraryName name env args 0 libraryFunctions

mutual

def Expr.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) : Nat -> Expr -> Expr
  | 0, expr => expr
  | fuel + 1, expr =>
      let rewrite :=
        Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel
      let rewriteArg :=
        Arg.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel
      let rewriteOption :=
        CallOption.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel
      let rewriteTupleItem :=
        TupleItem.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel
      match expr with
      | Expr.literal literal => Expr.literal literal
      | Expr.ident name => Expr.ident name
      | Expr.typeName ty => Expr.typeName ty
      | Expr.member base member => Expr.member (rewrite base) member
      | Expr.index base index => Expr.index (rewrite base) (rewrite index)
      | Expr.slice base start stop =>
          Expr.slice (rewrite base) (start.map rewrite) (stop.map rewrite)
      | Expr.call (Expr.ident name) args =>
          let args' := args.map rewriteArg
          match
              libraryInternalHelperCall?
                libraryName libraryFunctions env name args' with
          | some helper => Expr.call helper args'
          | none => Expr.call (Expr.ident name) args'
      | Expr.call fn args => Expr.call (rewrite fn) (args.map rewriteArg)
      | Expr.callWithOptions (Expr.ident name) options args =>
          let options' := options.map rewriteOption
          let args' := args.map rewriteArg
          match
              libraryInternalHelperCall?
                libraryName libraryFunctions env name args' with
          | some helper =>
              Expr.callWithOptions helper options' args'
          | none => Expr.callWithOptions (Expr.ident name) options' args'
      | Expr.callWithOptions fn options args =>
          Expr.callWithOptions (rewrite fn)
            (options.map rewriteOption) (args.map rewriteArg)
      | Expr.newExpr ty args => Expr.newExpr ty (args.map rewriteArg)
      | Expr.tuple items => Expr.tuple (items.map rewriteTupleItem)
      | Expr.array exprs => Expr.array (exprs.map rewrite)
      | Expr.enumFromUInt maxValue inner =>
          Expr.enumFromUInt maxValue (rewrite inner)
      | Expr.unary op inner => Expr.unary op (rewrite inner)
      | Expr.binary op lhs rhs => Expr.binary op (rewrite lhs) (rewrite rhs)
      | Expr.ternary cond thenExpr elseExpr =>
          Expr.ternary (rewrite cond) (rewrite thenExpr) (rewrite elseExpr)
      | Expr.assign lhs op rhs => Expr.assign (rewrite lhs) op (rewrite rhs)
      | Expr.payableConversion inner => Expr.payableConversion (rewrite inner)
termination_by fuel _ => fuel

def Arg.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) : Nat -> Arg -> Arg
  | 0, arg => arg
  | fuel + 1, Arg.positional expr =>
      Arg.positional
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
  | fuel + 1, Arg.named name expr =>
      Arg.named name
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
termination_by fuel _ => fuel

def CallOption.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) :
    Nat -> CallOption -> CallOption
  | 0, option => option
  | fuel + 1, CallOption.named name expr =>
      CallOption.named name
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
termination_by fuel _ => fuel

def TupleItem.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) :
    Nat -> TupleItem -> TupleItem
  | 0, item => item
  | _ + 1, TupleItem.hole => TupleItem.hole
  | fuel + 1, TupleItem.value expr =>
      TupleItem.value
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
termination_by fuel _ => fuel

def Stmt.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) : Nat -> Stmt -> Stmt
  | 0, stmt => stmt
  | _ + 1, Stmt.empty => Stmt.empty
  | fuel + 1, Stmt.block body =>
      -- Overload-selection env fidelity: thread each `varDecl`'s bindings into
      -- the env for the REST of the sequence, so an intra-library call whose
      -- argument is a LOCAL (`Pair memory p = ...; comb(p, 7)`) type-selects
      -- among same-name overloads instead of falling through to the
      -- declaration-order arity fallback (wrong-callee class).
      let step (acc : List Stmt × TypeEnv) (head : Stmt) :
          List Stmt × TypeEnv :=
        let (done, seqEnv) := acc
        let head' :=
          Stmt.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions seqEnv fuel head
        let seqEnv' :=
          match head with
          | Stmt.varDecl bindings _ => VarBindings.extendTypeEnv seqEnv bindings
          | _ => seqEnv
        (head' :: done, seqEnv')
      let (revBody, _) := body.foldl step (([] : List Stmt), env)
      Stmt.block revBody.reverse
  | fuel + 1, Stmt.varDecl bindings init =>
      Stmt.varDecl bindings
        (init.map
          (Expr.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
  | fuel + 1, Stmt.expr expr =>
      Stmt.expr
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
  | fuel + 1, Stmt.ifElse cond thenBranch elseBranch =>
      Stmt.ifElse
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel cond)
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel thenBranch)
        (elseBranch.map
          (Stmt.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
  | fuel + 1, Stmt.whileLoop cond body =>
      Stmt.whileLoop
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel cond)
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel body)
  | fuel + 1, Stmt.doWhile body cond =>
      Stmt.doWhile
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel body)
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel cond)
  | fuel + 1, Stmt.forLoop init cond post body =>
      -- A `for`-init var decl scopes over cond/post/body (same env-fidelity
      -- threading as the block arm).
      let loopEnv :=
        match init with
        | some (Stmt.varDecl bindings _) =>
            VarBindings.extendTypeEnv env bindings
        | _ => env
      Stmt.forLoop
        (init.map
          (Stmt.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
        (cond.map
          (Expr.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions loopEnv fuel))
        (post.map
          (Expr.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions loopEnv fuel))
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions loopEnv fuel body)
  | fuel + 1, Stmt.tryCatch expr clauses =>
      Stmt.tryCatch
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
        (clauses.map
          (CatchClause.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
  | fuel + 1, Stmt.tryCatchReturns expr returns success clauses =>
      Stmt.tryCatchReturns
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
        returns
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel success)
        (clauses.map
          (CatchClause.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
  | fuel + 1, Stmt.emitEvent expr =>
      Stmt.emitEvent
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
  | fuel + 1, Stmt.revertCall expr =>
      Stmt.revertCall
        (Expr.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel expr)
  | fuel + 1, Stmt.returnValues expr? =>
      Stmt.returnValues
        (expr?.map
          (Expr.rewriteLibraryInternalCallsFuel
            libraryName libraryFunctions env fuel))
  | _ + 1, Stmt.break => Stmt.break
  | _ + 1, Stmt.continue => Stmt.continue
  | fuel + 1, Stmt.unchecked body =>
      Stmt.unchecked
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel body)
  | _ + 1, Stmt.inlineAssembly code => Stmt.inlineAssembly code
  | _ + 1, Stmt.modifierPlaceholder => Stmt.modifierPlaceholder
termination_by fuel _ => fuel

def CatchClause.rewriteLibraryInternalCallsFuel (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (env : TypeEnv) :
    Nat -> CatchClause -> CatchClause
  | 0, clause => clause
  | fuel + 1, CatchClause.clause name params body =>
      CatchClause.clause name params
        (Stmt.rewriteLibraryInternalCallsFuel
          libraryName libraryFunctions env fuel body)
termination_by fuel _ => fuel

end

def FunctionDecl.rewriteLibraryInternalCalls
    (libraryName : Name) (libraryFunctions : List FunctionDecl)
    (decl : FunctionDecl) : FunctionDecl :=
  let env := FunctionDecl.typeEnv [] decl
  { decl with
    body := decl.body.map
      (Stmt.rewriteLibraryInternalCallsFuel
        libraryName libraryFunctions env defaultExpandUsingFuel) }

def ModifierDecl.expandUsing (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl)
    (usingDecls : List UsingDecl) (env : TypeEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  let modifierEnv := Parameters.extendTypeEnv "_mod" env decl.params
  { decl with
    body := decl.body.map
      (fun body =>
        Stmt.expandUsing contracts freeFunctions usingDecls modifierEnv body) }

def FunctionDecl.toCore? (storageNames : List Name) (constants : ConstantEnv)
    (extraEnv : TypeEnv)
    (contracts : List ContractDecl) (usingDecls : List UsingDecl)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl)
    (decl : FunctionDecl) (superFunctions : List FunctionDecl := [])
    (contractName? : Option Name := none)
    (baseNames : List Name := [])
    (externalCallKindEnv : ExternalCallKindEnv := [])
    (eventArgEnv : NamedArgParamEnv := [])
    (errorArgEnv : NamedArgParamEnv := [])
    (internalFnIds : List (Name × Nat) := [])
    (structEnv : StructEnv := [])
    (eventIndexedEnv : EventIndexedEnv := [])
    (overloadEvents : List EventDecl := []) :
    Option CoreFunctionDef := do
  let decl := FunctionDecl.inlineConstants constants decl
  let selectorEnv :=
    FunctionDecls.selectorEntries (decl :: functions ++ freeFunctions)
  let decl := FunctionDecl.resolveFunctionAddresses selectorEnv decl
  let decl := FunctionDecl.resolveSelectors selectorEnv decl
  let name ← FunctionDecl.coreName? decl
  let params ← Parameters.toCoreBindings? "_arg" decl.params
  -- Stage E: ABI cleanups are an ENTRY-only concern; storage-ref parameters
  -- (which can never appear in an ABI entrypoint signature) get `none` instead
  -- of failing the whole elaboration when their type has no ABI cleanup form.
  let paramAbiCleanups ←
    mapOption
      (fun (param : Parameter) =>
        if param.location == some DataLocation.storage then
          some SolidCore.Solidity.Source.AbiCleanup.none
        else do
          -- A `memory`-location aggregate parameter is copied out of calldata
          -- at decode and each element validated eagerly (solc reverts
          -- `revert(0,0)` on any dirty element, even an unread one); a
          -- `calldata` aggregate keeps lazy per-access validation. Mark memory
          -- params with `memoryEager` so decode validates them eagerly.
          let cleanup ← Ty.toCoreAbiCleanup? param.ty
          if param.location == some DataLocation.memory then
            some (SolidCore.Solidity.Source.AbiCleanup.memoryEager cleanup)
          else
            some cleanup)
      decl.params
  let returns ← Parameters.toCoreBindings? "_ret" decl.returns
  let body ← decl.body
  -- LIBRARY-STRAY-VALUE: a discarded public/external library-function-value
  -- statement (`Lib.m;`) is an effect-free no-op solc accepts; drop it here (in
  -- both this body and any modifier bodies) so it never reaches core lowering,
  -- which has no value form for a delegatecall-entry function pointer.
  let body := Stmt.dropStrayLibraryFunctionValues contracts body
  let modifiers :=
    modifiers.map (fun modifier =>
      { modifier with
        body := modifier.body.map
          (Stmt.dropStrayLibraryFunctionValues contracts) })
  let env := FunctionDecl.typeEnv
    (TypeEnv.extendThis extraEnv contractName?) decl
  let usingFunctionScope := functions ++ freeFunctions
  let body :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      body
    else
      Stmt.expandUsing contracts usingFunctionScope usingDecls env body
  let modifiers :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      modifiers
    else
      modifiers.map
        (ModifierDecl.expandUsing contracts usingFunctionScope usingDecls env)
  let modifierInvocations :=
    if usingDecls.isEmpty && !ContractDecls.hasLibrary contracts then
      decl.modifiers
    else
      decl.modifiers.map
        (ModifierInvocation.expandUsing
          contracts usingFunctionScope usingDecls env)
  let body :=
    match contractName? with
    | some contractName => Stmt.rewriteSuperCalls contractName body
    | none => body
  let body := Stmt.rewriteBaseCalls baseNames storageNames body
  let body := Stmt.resolveNamedEventErrorArgs eventArgEnv errorArgEnv body
  let modifiers :=
    modifiers.map
      (fun modifier =>
        { modifier with
          body := modifier.body.map
            (Stmt.resolveNamedEventErrorArgs eventArgEnv errorArgEnv) })
  -- EVENT-OVERLOAD (soundness): after named args are ordered, rewrite
  -- overloaded bare-name emits to their signature-mangled table keys (the
  -- assembly registers matching signature-keyed event entries). Runs with the
  -- same env `annotateAbi` uses; a contract with no same-name event overloads
  -- is untouched byte-identically (the resolver requires >= 2 in-scope decls).
  let body := Stmt.resolveOverloadedEventEmits overloadEvents env body
  let modifiers :=
    modifiers.map
      (fun modifier =>
        { modifier with
          body := modifier.body.map
            (Stmt.resolveOverloadedEventEmits overloadEvents
              (Parameters.extendTypeEnv "_mod" env modifier.params)) })
  let body := Stmt.inlineInternalFunctionAliasesInBody functions freeFunctions body
  -- A call THROUGH a ternary that selects between internal functions
  -- (`(cond ? a : b)(args)`) is distributed over the branches
  -- (`cond ? a(args) : b(args)`) BEFORE the fn-value rewrite below, so the
  -- selected functions stay NAME-resolved direct calls instead of becoming
  -- opaque dispatch-ID literals whose pointer type can no longer be recovered.
  let body := Stmt.distributeTernaryCallCallee body
  -- Stage C (boundary-completion arc): function identifiers still used as
  -- VALUES after alias inlining (fn-ptr state vars, data-dependent locals,
  -- fn-typed arguments/returns) become their dispatch-ID literals; the
  -- statically-aliasable local uses were already inlined above (status quo).
  let body :=
    Stmt.rewriteInternalFnValueIdents internalFnIds
      (FunctionDecl.fnValueScopeBoundNames decl) body
  -- Modifier bodies are inlined into this function during core elaboration
  -- (`functionExpandModifiersToCoreWithInternalCallsFull?`), AFTER the body
  -- rewrite above; rewrite their fn-value uses here too so a function-pointer
  -- VALUE created/assigned in a modifier body becomes its dispatch-ID literal
  -- (boundary-completion arc, ctor/modifier residue).
  let modifiers :=
    modifiers.map
      (fun modifier =>
        { modifier with
          body :=
            modifier.body.map
              (Stmt.rewriteInternalFnValueIdents internalFnIds
                (Parameters.boundNames modifier.params)) })
  -- Reference-signature extension: a `T storage` RETURN is a storage pointer the
  -- body re-points (`result = x`, or `return x` rewritten to `result = x;
  -- return;`). The inline-splice path registered returns in its storageRefEnv and
  -- rewrote its `return`s; the boundary path elaborates each function ONCE here,
  -- so `toCore?` must do the same so a boundary storage-ref-return callee's body
  -- treats its return as a storage pointer. Inert for value returns
  -- (`rewriteStorageReturnAssignments` only touches storage returns; the env
  -- entry marks non-storage returns `false`) and impossible for entry functions
  -- (storage pointers cannot cross the external boundary). -/
  let body := Stmt.rewriteStorageReturnAssignments "_ret" decl.returns body
  let body := Stmt.annotateAbi env body
  let storageRefEnv :=
    Parameters.extendStorageRefEnv "_ret"
      (Parameters.extendStorageRefEnv "_arg" [] decl.params) decl.returns
  let functions :=
    match contractName? with
    | some contractName =>
        functions ++ FunctionDecl.superHelpers contractName superFunctions
    | none => functions
  -- A parameter or named return shadows a same-named state variable inside the
  -- function's OWN body (solc resolves the nearest declaration), so lower the
  -- body against the state-name set with those names removed. Modifier
  -- prefixes/bodies keep the full `storageNames` (they cannot see these params).
  let bodyStorageNames :=
    stateNamesExcludingBound (FunctionDecl.fnValueScopeBoundNames decl)
      storageNames
  let bodyCore ←
    functionExpandModifiersToCoreWithInternalCallsFull?
      defaultInternalCallInlineFuel storageRefEnv env externalCallKindEnv
      storageNames bodyStorageNames
      (returns.map SolidCore.Solidity.Source.BindingDecl.name)
      modifiers functions freeFunctions (decl.returns.map Parameter.ty)
      modifierInvocations body (structEnv := structEnv)
      (eventIndexedEnv := eventIndexedEnv)
  let paramCleanups ← Parameters.toCoreCleanupStmts? "_arg" decl.params
  let returnMemoryLocalizes ←
    Parameters.toCoreMemoryLocalizeStmts? "_ret" decl.returns
      (localizeCalldata :=
        match decl.visibility with
        | some Visibility.external_ => true
        | some Visibility.public_ => true
        | _ => false)
  let bodyCore :=
    SolidCore.Solidity.Source.Stmt.block
      (paramCleanups ++ returnMemoryLocalizes ++ [bodyCore])
  -- R3 (#192) endgame: THE single storage value-use normalization pass, run
  -- once over the fully-assembled body (modifier splices, internal-call
  -- inlines and param cleanups included). Replaces the ~40 per-boundary
  -- `materializeStorageValueUseCore` call sites and covers storage reads
  -- NESTED inside array literals / tuples / concats / struct-constructor
  -- args, which the shallow rewrite missed.
  let bodyCore :=
    SolidCore.Solidity.Source.Stmt.normalizeStorageValueUses bodyCore
  some
    { name := name
      selector? := FunctionDecl.abiSelector? decl
      payable := FunctionDecl.isPayable decl
      params := params
      paramAbiCleanups := paramAbiCleanups
      returns := returns
      body := bodyCore }

def FunctionDecl.rewriteDispatchCalls (contractName : Name)
    (baseNames stateNames : List Name) (decl : FunctionDecl) : FunctionDecl :=
  { decl with
    body :=
      decl.body.map (fun body =>
        Stmt.rewriteBaseCalls baseNames stateNames
          (Stmt.rewriteSuperCalls contractName body)) }

end SolidCore.Solidity.Executable

import SolidCore.Solidity.StagedK

/-!
# The translation of one function in stages

`FunctionDecl.toCore?` lowers a function's body after a run of cheap passes; for the largest
functions the kernel cannot evaluate it in one declaration within 6 GB. This module splits it
into the passes before the lowering (`FunctionDecl.toCorePre?`), the ANF preprocessing and the
lowering of the body, and the rest (`FunctionDecl.toCoreRest?`), and proves the composition
equal to `FunctionDecl.toCore?` (`FunctionDecl.toCore_eq_staged`) and, for a contract's context,
to `FromOrdersCtx.pairF` (`FromOrdersCtx.pairF_of_stages`), so each stage is checked in a module of
its own.
-/

namespace SolidCore.Solidity.Executable

/-- What `FunctionDecl.toCore?` computes before it lowers the body. -/
structure ToCorePre where
  decl : FunctionDecl
  name : Name
  params : List SolidCore.Solidity.Source.BindingDecl
  paramAbiCleanups : List SolidCore.Solidity.Source.AbiCleanup
  returns : List SolidCore.Solidity.Source.BindingDecl
  body : Stmt
  env : TypeEnv
  storageRefEnv : StorageRefEnv
  modifiers : List SourceModifierDecl
  modifierInvocations : List SourceModifierInvocation
  functions : List FunctionDecl
  bodyStorageNames : List Name
  deriving Repr

/-- `FunctionDecl.toCore?` up to the lowering of the body. -/
def FunctionDecl.toCorePre? (storageNames : List Name) (constants : ConstantEnv)
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
    Option ToCorePre := do
  let decl := FunctionDecl.inlineConstants constants decl
  let selectorEnv :=
    FunctionDecls.selectorEntries (decl :: functions ++ freeFunctions)
  let decl := FunctionDecl.resolveFunctionAddresses selectorEnv decl
  let decl := FunctionDecl.resolveSelectors selectorEnv decl
  let name ← FunctionDecl.coreName? decl
  let params ← Parameters.toCoreBindings? "_arg" decl.params
  let paramAbiCleanups ←
    mapOption
      (fun (param : Parameter) =>
        if param.location == some DataLocation.storage then
          some SolidCore.Solidity.Source.AbiCleanup.none
        else do
          let cleanup ← Ty.toCoreAbiCleanup? param.ty
          if param.location == some DataLocation.memory then
            some (SolidCore.Solidity.Source.AbiCleanup.memoryEager cleanup)
          else
            some cleanup)
      decl.params
  let returns ← Parameters.toCoreBindings? "_ret" decl.returns
  let body ← decl.body
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
  let body := Stmt.resolveOverloadedEventEmits overloadEvents env body
  let modifiers :=
    modifiers.map
      (fun modifier =>
        { modifier with
          body := modifier.body.map
            (Stmt.resolveOverloadedEventEmits overloadEvents
              (Parameters.extendTypeEnv "_mod" env modifier.params)) })
  let body := Stmt.inlineInternalFunctionAliasesInBody functions freeFunctions body
  let body := Stmt.distributeTernaryCallCallee body
  let body :=
    Stmt.rewriteInternalFnValueIdents internalFnIds
      (FunctionDecl.fnValueScopeBoundNames decl) body
  let modifiers :=
    modifiers.map
      (fun modifier =>
        { modifier with
          body :=
            modifier.body.map
              (Stmt.rewriteInternalFnValueIdents internalFnIds
                (Parameters.boundNames modifier.params)) })
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
  let bodyStorageNames :=
    stateNamesExcludingBound (FunctionDecl.fnValueScopeBoundNames decl)
      storageNames
  pure (ToCorePre.mk decl name params paramAbiCleanups returns body env storageRefEnv modifiers
    modifierInvocations functions bodyStorageNames)

/-- `functionExpandModifiersToCoreWithInternalCallsFull?` given the lowering of the body. -/
def expandWith? (internalFuel : Nat) (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (inner : Option CoreStmt) (structEnv : StructEnv)
    (eventIndexedEnv : EventIndexedEnv) : List SourceModifierInvocation → Option CoreStmt
  | [] => inner
  | invocation :: rest => do
      let inner ← expandWith? internalFuel storageRefEnv env externalCallKindEnv storageNames
        returnNames available functions freeFunctions returnTys inner structEnv eventIndexedEnv rest
      let modifierDecl ← modifierResolve? available invocation.target
      modifierApplyToCoreWithInternalCalls? internalFuel storageRefEnv env
        externalCallKindEnv storageNames returnNames available functions
        freeFunctions returnTys modifierDecl invocation inner
        (structEnv := structEnv) (eventIndexedEnv := eventIndexedEnv)

theorem expand_eq (internalFuel : Nat) (storageRefEnv : StorageRefEnv) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv) (storageNames bodyStorageNames returnNames : List Name)
    (available : List SourceModifierDecl) (functions freeFunctions : List FunctionDecl)
    (returnTys : List Ty) (body : Stmt) (structEnv : StructEnv) (eventIndexedEnv : EventIndexedEnv) :
    ∀ invocations : List SourceModifierInvocation,
    functionExpandModifiersToCoreWithInternalCallsFull? internalFuel storageRefEnv env
        externalCallKindEnv storageNames bodyStorageNames returnNames available functions
        freeFunctions returnTys invocations body (structEnv := structEnv)
        (eventIndexedEnv := eventIndexedEnv) =
      expandWith? internalFuel storageRefEnv env externalCallKindEnv storageNames returnNames
        available functions freeFunctions returnTys
        (Stmt.toCoreWithInternalCalls? internalFuel storageRefEnv env externalCallKindEnv
          bodyStorageNames available functions freeFunctions returnTys
          (Stmt.anfPreprocess structEnv internalFuel storageRefEnv env externalCallKindEnv
            bodyStorageNames available functions freeFunctions returnTys eventIndexedEnv
            defaultAnfPreprocessFuel body))
        structEnv eventIndexedEnv invocations
  | [] => by rw [functionExpandModifiersToCoreWithInternalCallsFull?]; rfl
  | invocation :: rest => by
      rw [functionExpandModifiersToCoreWithInternalCallsFull?, expandWith?,
        expand_eq internalFuel storageRefEnv env externalCallKindEnv storageNames bodyStorageNames
          returnNames available functions freeFunctions returnTys body structEnv eventIndexedEnv rest]

/-- The lowering of a function's body after its ANF preprocessing, as
`functionExpandModifiersToCoreWithInternalCallsFull?` does. -/
def ToCorePre.anf (pre : ToCorePre) (externalCallKindEnv : ExternalCallKindEnv)
    (freeFunctions : List FunctionDecl) (structEnv : StructEnv) (eventIndexedEnv : EventIndexedEnv) :
    Stmt :=
  Stmt.anfPreprocess structEnv defaultInternalCallInlineFuel pre.storageRefEnv pre.env
    externalCallKindEnv pre.bodyStorageNames pre.modifiers pre.functions freeFunctions
    (pre.decl.returns.map Parameter.ty) eventIndexedEnv defaultAnfPreprocessFuel pre.body

/-- The lowering of a function's preprocessed body. -/
def ToCorePre.lower (pre : ToCorePre) (externalCallKindEnv : ExternalCallKindEnv)
    (freeFunctions : List FunctionDecl) (body : Stmt) : Option CoreStmt :=
  Stmt.toCoreWithInternalCalls? defaultInternalCallInlineFuel pre.storageRefEnv pre.env
    externalCallKindEnv pre.bodyStorageNames pre.modifiers pre.functions freeFunctions
    (pre.decl.returns.map Parameter.ty) body

/-- `FunctionDecl.toCore?` after the lowering of the body. -/
def FunctionDecl.toCoreRest? (storageNames : List Name) (freeFunctions : List FunctionDecl)
    (externalCallKindEnv : ExternalCallKindEnv) (structEnv : StructEnv)
    (eventIndexedEnv : EventIndexedEnv) (pre : ToCorePre) (inner : Option CoreStmt) :
    Option CoreFunctionDef := do
  let decl := pre.decl
  let name := pre.name
  let params := pre.params
  let paramAbiCleanups := pre.paramAbiCleanups
  let returns := pre.returns
  let bodyCore ←
    expandWith? defaultInternalCallInlineFuel pre.storageRefEnv pre.env externalCallKindEnv
      storageNames (returns.map SolidCore.Solidity.Source.BindingDecl.name) pre.modifiers
      pre.functions freeFunctions (decl.returns.map Parameter.ty) inner structEnv eventIndexedEnv
      pre.modifierInvocations
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
theorem FunctionDecl.toCore_eq_staged (storageNames : List Name) (constants : ConstantEnv)
    (extraEnv : TypeEnv)
    (contracts : List ContractDecl) (usingDecls : List UsingDecl)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl)
    (decl : FunctionDecl) (superFunctions : List FunctionDecl)
    (contractName? : Option Name)
    (baseNames : List Name)
    (externalCallKindEnv : ExternalCallKindEnv)
    (eventArgEnv : NamedArgParamEnv)
    (errorArgEnv : NamedArgParamEnv)
    (internalFnIds : List (Name × Nat))
    (structEnv : StructEnv)
    (eventIndexedEnv : EventIndexedEnv)
    (overloadEvents : List EventDecl) :
    FunctionDecl.toCore? storageNames constants extraEnv contracts usingDecls modifiers functions
        freeFunctions decl superFunctions contractName? baseNames externalCallKindEnv eventArgEnv
        errorArgEnv internalFnIds structEnv eventIndexedEnv overloadEvents =
      (FunctionDecl.toCorePre? storageNames constants extraEnv contracts usingDecls modifiers
          functions freeFunctions decl superFunctions contractName? baseNames externalCallKindEnv
          eventArgEnv errorArgEnv internalFnIds structEnv eventIndexedEnv overloadEvents) >>=
        fun pre => FunctionDecl.toCoreRest? storageNames freeFunctions externalCallKindEnv structEnv
          eventIndexedEnv pre
          (pre.lower externalCallKindEnv freeFunctions
            (pre.anf externalCallKindEnv freeFunctions structEnv eventIndexedEnv)) := by
  simp only [FunctionDecl.toCore?, FunctionDecl.toCorePre?, FunctionDecl.toCoreRest?,
    ToCorePre.lower, ToCorePre.anf, expand_eq, bind_assoc, pure_bind]
  rfl

/-- `FromOrdersCtx.pairF` up to the lowering of the function's body. -/
def FromOrdersCtx.preF (c : FromOrdersCtx) (decl : ContractDecl) (fn : FunctionDecl) :
    Option ToCorePre := do
  let supers ← ContractDecls.afterName? c.dispatchOrder decl.name
  FunctionDecl.toCorePre? c.storageNames
    (ContractDecl.scopedConstantEnv c.dispatchOrder c.sharedConstantTail decl)
    c.stateEnv c.allContracts (ContractDecl.directUsingDecls decl ++ c.sourceUsingDecls)
    c.modifiers c.availableFunctions c.sourceFunctions fn
    (concatMapList ContractDecl.directOrdinaryFunctions supers)
    (some decl.name) (c.dispatchOrder.map ContractDecl.name)
    c.externalCallKindEnv c.eventArgEnv c.errorArgEnv c.internalFnIds
    (ContractDecl.structEnvFromContracts c.allContracts) c.eventIndexedEnv
    (c.contractEvents ++ c.visibleSourceEvents)

/-- The ANF preprocessing of a function's body in a contract's context. -/
def FromOrdersCtx.anfF (c : FromOrdersCtx) (pre : ToCorePre) : Stmt :=
  pre.anf c.externalCallKindEnv c.sourceFunctions
    (ContractDecl.structEnvFromContracts c.allContracts) c.eventIndexedEnv

/-- The lowering of a function's preprocessed body in a contract's context. -/
def FromOrdersCtx.lowF (c : FromOrdersCtx) (pre : ToCorePre) (body : Stmt) : Option CoreStmt :=
  pre.lower c.externalCallKindEnv c.sourceFunctions body

/-- `FromOrdersCtx.pairF` after the lowering of the function's body. -/
def FromOrdersCtx.restF (c : FromOrdersCtx) (decl : ContractDecl) (fn : FunctionDecl)
    (pre : ToCorePre) (inner : Option CoreStmt) : Option (FunctionDecl × CoreFunctionDef) := do
  let fd ← FunctionDecl.toCoreRest? c.storageNames c.sourceFunctions c.externalCallKindEnv
    (ContractDecl.structEnvFromContracts c.allContracts) c.eventIndexedEnv pre inner
  let fd :=
    if decl.kind == ContractKind.library then
      { fd with
        selector? :=
          FunctionDecl.libraryAbiSelector?
            (ContractDecl.structEnvFromContracts c.allContracts) fn }
    else
      fd
  some (fn, fd)

theorem FromOrdersCtx.pairF_eq_staged (c : FromOrdersCtx) (decl : ContractDecl)
    (fn : FunctionDecl) :
    c.pairF decl fn = c.preF decl fn >>= fun pre => c.restF decl fn pre (c.lowF pre (c.anfF pre)) := by
  simp only [FromOrdersCtx.pairF, ContractDecl.directCoreFunctionPair?, FromOrdersCtx.preF,
    FromOrdersCtx.restF, FromOrdersCtx.lowF, FromOrdersCtx.anfF, FunctionDecl.toCore_eq_staged,
    bind_assoc]

/-- A function's translation in a contract's context from its stages. -/
theorem FromOrdersCtx.pairF_of_stages {c : FromOrdersCtx} {decl : ContractDecl} {fn : FunctionDecl}
    {pre : ToCorePre} {body : Stmt} {inner : CoreStmt} {p : FunctionDecl × CoreFunctionDef}
    (h₁ : c.preF decl fn = some pre) (h₂ : some (c.anfF pre) = some body)
    (h₃ : c.lowF pre body = some inner) (h₄ : c.restF decl fn pre (some inner) = some p) :
    c.pairF decl fn = some p := by
  rw [FromOrdersCtx.pairF_eq_staged, h₁]
  show c.restF decl fn pre (c.lowF pre (c.anfF pre)) = some p
  rw [Option.some.inj h₂, h₃]
  exact h₄

end SolidCore.Solidity.Executable

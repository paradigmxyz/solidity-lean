import SolidCore.Solidity.Interface.Statements
import SolidCore.Solidity.Interface.ContractMetadata

namespace SolidCore.Solidity.Executable

def StateVarDecl.isImmutable (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.immutable => true
  | _ => false

def StateVarDecl.isStorageBacked (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.mutable => true
  | VarMutability.transient => false
  | VarMutability.constant => false
  | VarMutability.immutable => false

def StateVarDecl.isTransient (decl : StateVarDecl) : Bool :=
  match decl.mutability with
  | VarMutability.transient => true
  | _ => false

def StateVarDecl.constantEntry? (decl : StateVarDecl) :
    Option (Name × Ty × Expr) :=
  match decl.mutability, decl.init with
  | VarMutability.constant, some expr => some (decl.name, decl.ty, expr)
  | _, _ => none

def StateVarDecl.hasRequiredConstantInit (decl : StateVarDecl) : Bool :=
  match decl.mutability, decl.init with
  | VarMutability.constant, some _ => true
  | VarMutability.constant, none => false
  | _, _ => true

def StateVars.constantEnv (decls : List StateVarDecl) : ConstantEnv :=
  decls.filterMap StateVarDecl.constantEntry?

inductive StateVarSourceClass where
  | storage
  | transient
  | constant
  | immutable
  deriving Repr, BEq

def StateVarDecl.sourceClass (decl : StateVarDecl) : StateVarSourceClass :=
  match decl.mutability with
  | VarMutability.mutable => StateVarSourceClass.storage
  | VarMutability.transient => StateVarSourceClass.transient
  | VarMutability.constant => StateVarSourceClass.constant
  | VarMutability.immutable => StateVarSourceClass.immutable

def StateVarDecl.sourceStateName? (decl : StateVarDecl) :
    Option Name :=
  match decl.mutability with
  | VarMutability.constant => none
  | VarMutability.immutable => some (immutableNameTag decl.name)
  | _ => some decl.name

def StateVars.constantsHaveInits : List StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.hasRequiredConstantInit decl &&
        StateVars.constantsHaveInits rest

def StateVars.allConstants : List StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.isConstant decl && StateVars.allConstants rest

def ContractDecl.directStorageStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isStorageBacked

def ContractDecl.directTransientStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isTransient

def ContractDecl.directImmutableStateVars (decl : ContractDecl) :
    List StateVarDecl :=
  (ContractDecl.directStateVars decl).filter StateVarDecl.isImmutable

def ContractDecl.storageNames (decl : ContractDecl) : List Name :=
  (ContractDecl.directStorageStateVars decl).map StateVarDecl.name ++
    (ContractDecl.directTransientStateVars decl).map StateVarDecl.name

def ContractDecl.directModifiers (decl : ContractDecl) : List SourceModifierDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.modifierDecl modifier => some modifier
    | _ => none)

def ContractDecl.modifiers (decl : ContractDecl) : List SourceModifierDecl :=
  ContractDecl.directModifiers decl

/-- Like `directModifiers`, but stamps each modifier with `declaringContract :=
some decl.name` so a later statically-QUALIFIED invocation `Base.m` can bind to
the exact declaring base's modifier (solc `VirtualLookup::Static`) instead of
the most-derived override that name-first lookup returns. -/
def ContractDecl.directModifiersStamped (decl : ContractDecl) :
    List SourceModifierDecl :=
  (ContractDecl.directModifiers decl).map
    (fun modifier => { modifier with declaringContract := some decl.name })

def ContractDecl.constructorPayable? (decl : ContractDecl) : Option Bool :=
  match ContractDecl.directConstructors decl with
  | [] => some false
  | [ctor] => some (FunctionDecl.isPayable ctor)
  | _ => none

def ContractDecl.directOrdinaryFunctions (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directFunctions decl).filter
    (fun fn => !FunctionDecl.isConstructor fn)

def FunctionDecl.externalCallKindEntry? (contractName : Name)
    (decl : FunctionDecl) : Option ExternalCallKindEntry :=
  match decl.kind, decl.name, decl.visibility with
  | FunctionKind.function, some _, some Visibility.internal_ => none
  | FunctionKind.function, some _, some Visibility.private_ => none
  | FunctionKind.function, some functionName, _ =>
      some
        { contractName := contractName
          functionName := functionName
          paramTys := decl.params.map Parameter.ty
          paramNames := decl.params.map Parameter.name
          paramLocations := decl.params.map Parameter.location
          returnTys := decl.returns.map Parameter.ty
          mutability := decl.mutability }
  | _, _, _ => none

def FunctionDecl.constructorCallKindEntry? (contractName : Name)
    (decl : FunctionDecl) : Option ExternalCallKindEntry :=
  match decl.kind with
  | FunctionKind.constructor =>
      some
        { contractName := contractName
          functionName := constructorExternalCallKindName
          paramTys := decl.params.map Parameter.ty
          paramNames := decl.params.map Parameter.name
          mutability := decl.mutability
          isConstructor := true }
  | _ => none

def ContractDecl.constructorCallKindEntry?
    (decl : ContractDecl) : Option ExternalCallKindEntry := do
  let ctor? ← ContractDecl.directConstructor? decl
  match ctor? with
  | some ctor =>
      FunctionDecl.constructorCallKindEntry? decl.name ctor
  | none =>
      some
        { contractName := decl.name
          functionName := constructorExternalCallKindName
          paramTys := []
          paramNames := []
          mutability := StateMutability.nonpayable
          isConstructor := true }

def StateVarDecl.externalGetterParamTys? (decl : StateVarDecl) :
    Option (List Ty) :=
  match decl.visibility with
  | some Visibility.public_ => do
      let shape ← Ty.publicGetterShape? 64 decl.ty
      some shape.fst
  | _ => none

def StateVarDecl.externalCallKindEntry? (contractName : Name)
    (decl : StateVarDecl) : Option ExternalCallKindEntry := do
  if decl.visibility != some Visibility.public_ then
    none
  else
    some ()
  let shape ← Ty.publicGetterShape? 64 decl.ty
  let params := shape.fst
  some
    { contractName := contractName
      functionName := decl.name
      paramTys := params
      paramNames := List.replicate params.length none
      returnTys := shape.snd.map Prod.snd
      mutability := StateMutability.view }

def ContractDecl.directExternalCallKindEntriesAs
    (targetName : Name) (decl : ContractDecl)
    (structEnv : StructEnv := []) : List ExternalCallKindEntry :=
  let functionEntries :=
    (ContractDecl.directOrdinaryFunctions decl).filterMap
      (fun fn => do
        let entry ← FunctionDecl.externalCallKindEntry? targetName fn
        -- BUG#6: LIBRARY entries carry the library-qualified signature the
        -- caller-side delegatecall payload must hash.
        if decl.kind == ContractKind.library then
          some
            { entry with
              librarySignature? :=
                FunctionDecl.libraryAbiSignature? structEnv fn }
        else
          some entry)
  let getterEntries :=
    (ContractDecl.directStateVars decl).filterMap
      (StateVarDecl.externalCallKindEntry? targetName)
  functionEntries ++ getterEntries

def ContractDecl.isInterface (decl : ContractDecl) : Bool :=
  match decl.kind with
  | ContractKind.interface => true
  | _ => false

-- solc (`Types.cpp:4271-4285`): `type(T).interfaceId` is exposed for any
-- NON-deployable contract — an interface OR an abstract contract — and rejected
-- for a concrete deployable contract.
def ContractDecl.isNonDeployable (decl : ContractDecl) : Bool :=
  ContractDecl.isInterface decl || decl.abstract

-- A directly-declared function counts toward the external interface exactly when
-- it is an ordinary function that is externally visible (public/external), i.e.
-- NOT internal/private — matching solc's `isPartOfExternalInterface` filter used
-- by `interfaceFunctionList` (`AST.cpp`). (For an interface every function is
-- external, so this keeps the interface case identical to before.)
def FunctionDecl.isInterfaceFunction (decl : FunctionDecl) : Bool :=
  match decl.kind, decl.visibility with
  | FunctionKind.function, some Visibility.internal_ => false
  | FunctionKind.function, some Visibility.private_ => false
  | FunctionKind.function, _ => true
  | _, _ => false

-- solc `ContractDefinition::interfaceId()` (`AST.cpp:315-321`) XORs the 4-byte
-- selectors of `interfaceFunctionList(false)` — the externally-visible functions
-- AND public state-variable getters declared DIRECTLY in the contract (`false`
-- excludes inherited). Interfaces cannot have state variables so the getter fold
-- is vacuous there (F2 unchanged); abstract contracts CAN, and solc includes
-- their getters — verified by pinned-solc/Forge probe
-- (`type(A).interfaceId` = foo ^ bar ^ stateVar-getter).
def ContractDecl.interfaceId? (decl : ContractDecl) : Option Word := do
  if ContractDecl.isNonDeployable decl then
    some ()
  else
    none
  let fnList := (ContractDecl.directOrdinaryFunctions decl).filter
    FunctionDecl.isInterfaceFunction
  let fnId ← FunctionDecls.interfaceId? fnList
  let getterId :=
    ((ContractDecl.directStateVars decl).filterMap
        (fun d => (StateVarDecl.selectorEntry? d).map Prod.snd)).foldl
      SolidCore.Solidity.Shared.xorWord 0
  some (SolidCore.Solidity.Shared.xorWord fnId getterId)

def ContractDecl.interfaceIdEntry? (decl : ContractDecl) :
    Option (Option (Name × Word)) :=
  if ContractDecl.isNonDeployable decl then
    do
    let interfaceId ← ContractDecl.interfaceId? decl
    some (some (decl.name, interfaceId))
  else
    some none

def ContractDecls.interfaceIdEnv (decls : List ContractDecl) :
    Option InterfaceIdEnv :=
  filterMapOption ContractDecl.interfaceIdEntry? decls

def ContractItem.resolveInterfaceIds (env : InterfaceIdEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.resolveInterfaceIds env decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.resolveInterfaceIds env decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.resolveInterfaceIds env decl)
  | item => item

def BaseSpecifier.resolveInterfaceIds (env : InterfaceIdEnv)
    (spec : BaseSpecifier) : BaseSpecifier :=
  { spec with args := spec.args.map (Arg.resolveInterfaceIds env) }

def ContractDecl.resolveInterfaceIds (env : InterfaceIdEnv)
    (decl : ContractDecl) : ContractDecl :=
  { decl with
    layoutBase := decl.layoutBase.map (Expr.resolveInterfaceIds env)
    bases := decl.bases.map (BaseSpecifier.resolveInterfaceIds env)
    items := decl.items.map (ContractItem.resolveInterfaceIds env) }

def ContractDecl.contextualOrdinaryFunctions (constants : ConstantEnv)
    (baseNames stateNames : List Name) (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.directOrdinaryFunctions decl).map
    (fun fn =>
      FunctionDecl.rewriteDispatchCalls decl.name baseNames stateNames
        (FunctionDecl.inlineConstants constants fn))

def ContractDecl.contextualBaseHelpers (constants : ConstantEnv)
    (baseNames stateNames : List Name) (decl : ContractDecl) : List FunctionDecl :=
  (ContractDecl.contextualOrdinaryFunctions constants baseNames stateNames decl).filterMap
    (FunctionDecl.asBaseHelper? decl.name)

def ContractDecl.directUsingDecls (decl : ContractDecl) : List UsingDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.usingDecl usingDecl => some usingDecl
    | _ => none)

def StateVarDecl.expandUsingSurface (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl) (usingDecls : List UsingDecl)
    (env : TypeEnv) (decl : StateVarDecl) : StateVarDecl :=
  { decl with
    init := decl.init.map
      (Expr.expandUsing contracts freeFunctions usingDecls env) }

def FunctionDecl.expandUsingSurface (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl) (usingDecls : List UsingDecl)
    (extraEnv : TypeEnv) (contractName? : Option Name)
    (decl : FunctionDecl) : FunctionDecl :=
  let env :=
    FunctionDecl.typeEnv (TypeEnv.extendThis extraEnv contractName?) decl
  { decl with
    modifiers :=
      decl.modifiers.map
        (ModifierInvocation.expandUsing contracts freeFunctions usingDecls env)
    body := decl.body.map
      (Stmt.expandUsing contracts freeFunctions usingDecls env) }

def ContractItem.expandUsingSurface (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl) (usingDecls : List UsingDecl)
    (stateEnv : TypeEnv) (contractName : Name) :
    ContractItem -> Option ContractItem
  | ContractItem.stateVar decl =>
      some (ContractItem.stateVar
        (StateVarDecl.expandUsingSurface
          contracts freeFunctions usingDecls stateEnv decl))
  | ContractItem.function decl =>
      some (ContractItem.function
        (FunctionDecl.expandUsingSurface contracts freeFunctions usingDecls
          stateEnv (some contractName) decl))
  | ContractItem.modifierDecl decl =>
      some (ContractItem.modifierDecl
        (ModifierDecl.expandUsing contracts freeFunctions usingDecls stateEnv decl))
  | ContractItem.usingDecl decl => some (ContractItem.usingDecl decl)
  | other => some other

def ContractDecl.expandUsingSurface (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl) (sourceUsingDecls : List UsingDecl)
    (decl : ContractDecl) : ContractDecl :=
  let usingDecls := ContractDecl.directUsingDecls decl ++ sourceUsingDecls
  let usingFunctionScope :=
    freeFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions contracts
  let stateEnv := StateVars.extendTypeEnv [] (ContractDecl.directStateVars decl)
  { decl with
    items :=
      decl.items.filterMap
        (ContractItem.expandUsingSurface contracts usingFunctionScope usingDecls
          stateEnv decl.name) }

def ContractDecl.expandDirectUsingSurface (contracts : List ContractDecl)
    (freeFunctions : List FunctionDecl) (decl : ContractDecl) : ContractDecl :=
  if (ContractDecl.directUsingDecls decl).isEmpty then
    decl
  else
    ContractDecl.expandUsingSurface contracts freeFunctions [] decl

def namesCount (target : Name) : List Name -> Nat
  | [] => 0
  | name :: rest =>
      (if name == target then 1 else 0) + namesCount target rest

def duplicateNames (names : List Name) : List Name :=
  names.filter (fun name => namesCount name names > 1)

structure ScopedStateVarDecl where
  contractName : Name
  decl : StateVarDecl
  deriving Repr

def ContractDecl.scopedDirectStateVars (decl : ContractDecl) :
    List ScopedStateVarDecl :=
  (ContractDecl.directStateVars decl).map
    (fun stateVar => { contractName := decl.name, decl := stateVar })

def ContractDecls.scopedStateVars :
    List ContractDecl -> List ScopedStateVarDecl
  | [] => []
  | decl :: rest =>
      ContractDecl.scopedDirectStateVars decl ++
        ContractDecls.scopedStateVars rest

def StateVarDecl.visibleFromDerived (decl : StateVarDecl) : Bool :=
  decl.visibility != some Visibility.private_

def ScopedStateVarDecl.visibleFrom (contractName : Name)
    (scopedVar : ScopedStateVarDecl) : Bool :=
  scopedVar.contractName == contractName ||
    StateVarDecl.visibleFromDerived scopedVar.decl

def ScopedStateVarDecl.coreName (duplicateSourceNames : List Name)
    (scopedVar : ScopedStateVarDecl) : Name :=
  if nameIn scopedVar.decl.name duplicateSourceNames then
    scopedVar.contractName ++ "." ++ scopedVar.decl.name
  else
    scopedVar.decl.name

def ScopedStateVarDecl.coreDecl (duplicateSourceNames : List Name)
    (scopedVar : ScopedStateVarDecl) : StateVarDecl :=
  { scopedVar.decl with
    name := ScopedStateVarDecl.coreName duplicateSourceNames scopedVar }

def ScopedStateVarDecl.runtimeAlias? (duplicateSourceNames : List Name)
    (scopedVar : ScopedStateVarDecl) : Option (Name × Name) :=
  let key := ScopedStateVarDecl.coreName duplicateSourceNames scopedVar
  if key == scopedVar.decl.name then
    none
  else
    some (scopedVar.decl.name, key)

def ScopedStateVarDecl.runtimeNameAliasEntry?
    (duplicateSourceNames : List Name)
    (scopedVar : ScopedStateVarDecl) : Option Name := do
  let (source, key) ←
    ScopedStateVarDecl.runtimeAlias? duplicateSourceNames scopedVar
  match scopedVar.decl.mutability with
  | VarMutability.immutable =>
      some (stateNameAliasEntry (immutableNameTag source) (immutableNameTag key))
  | VarMutability.mutable | VarMutability.transient =>
      some (stateNameAliasEntry source key)
  | VarMutability.constant => none

def ScopedStateVarDecl.nameAliasEntry?
    (duplicateSourceNames : List Name)
    (scopedVar : ScopedStateVarDecl) : Option (Name × Name) :=
  ScopedStateVarDecl.runtimeAlias? duplicateSourceNames scopedVar

def ScopedStateVarDecls.coreDecls (duplicateSourceNames : List Name) :
    List ScopedStateVarDecl -> List StateVarDecl
  | [] => []
  | scopedVar :: rest =>
      ScopedStateVarDecl.coreDecl duplicateSourceNames scopedVar ::
        ScopedStateVarDecls.coreDecls duplicateSourceNames rest

def ScopedStateVarDecls.runtimeNameAliasEntries
    (duplicateSourceNames : List Name) :
    List ScopedStateVarDecl -> List Name
  | [] => []
  | scopedVar :: rest =>
      match ScopedStateVarDecl.runtimeNameAliasEntry?
          duplicateSourceNames scopedVar with
      | some entry =>
          entry ::
            ScopedStateVarDecls.runtimeNameAliasEntries
              duplicateSourceNames rest
      | none =>
          ScopedStateVarDecls.runtimeNameAliasEntries
            duplicateSourceNames rest

def ScopedStateVarDecls.nameAliasEnv (duplicateSourceNames : List Name) :
    List ScopedStateVarDecl -> NameAliasEnv
  | [] => []
  | scopedVar :: rest =>
      match ScopedStateVarDecl.nameAliasEntry?
          duplicateSourceNames scopedVar with
      | some entry =>
          entry ::
            ScopedStateVarDecls.nameAliasEnv duplicateSourceNames rest
      | none =>
          ScopedStateVarDecls.nameAliasEnv duplicateSourceNames rest

def ScopedStateVarDecls.visibleFrom (contractName : Name) :
    List ScopedStateVarDecl -> List ScopedStateVarDecl
  | [] => []
  | scopedVar :: rest =>
      let tail := ScopedStateVarDecls.visibleFrom contractName rest
      if ScopedStateVarDecl.visibleFrom contractName scopedVar then
        scopedVar :: tail
      else
        tail

def FunctionDecl.rewriteStateAliases (aliases : NameAliasEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  let aliases := Parameters.removeNameAliases aliases decl.params
  let aliases := Parameters.removeNameAliases aliases decl.returns
  { decl with
    modifiers :=
      decl.modifiers.map (ModifierInvocation.renameIdents aliases)
    body := decl.body.map (Stmt.renameIdents aliases) }

def ModifierDecl.rewriteStateAliases (aliases : NameAliasEnv)
    (decl : ModifierDecl) : ModifierDecl :=
  let aliases := Parameters.removeNameAliases aliases decl.params
  { decl with body := decl.body.map (Stmt.renameIdents aliases) }

def StateVarDecl.rewriteStateAliases (aliases : NameAliasEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  { decl with
    name := NameAliasEnv.resolve aliases decl.name
    init := decl.init.map (Expr.renameIdents aliases) }

def ContractItem.rewriteStateAliases (aliases : NameAliasEnv) :
    ContractItem -> ContractItem
  | ContractItem.stateVar decl =>
      ContractItem.stateVar (StateVarDecl.rewriteStateAliases aliases decl)
  | ContractItem.function decl =>
      ContractItem.function (FunctionDecl.rewriteStateAliases aliases decl)
  | ContractItem.modifierDecl decl =>
      ContractItem.modifierDecl (ModifierDecl.rewriteStateAliases aliases decl)
  | item => item

def ContractDecl.rewriteStateAliases
    (duplicateSourceNames : List Name)
    (visibleScoped : List ScopedStateVarDecl)
    (decl : ContractDecl) : ContractDecl :=
  let aliases :=
    ScopedStateVarDecls.nameAliasEnv duplicateSourceNames visibleScoped
  { decl with items := decl.items.map (ContractItem.rewriteStateAliases aliases) }

def ContractDecls.rewriteStateAliases
    (duplicateSourceNames : List Name)
    (scopedStateVars : List ScopedStateVarDecl) :
    List ContractDecl -> List ContractDecl
  | [] => []
  | decl :: rest =>
      let visibleScoped :=
        ScopedStateVarDecls.visibleFrom decl.name scopedStateVars
      ContractDecl.rewriteStateAliases duplicateSourceNames visibleScoped decl ::
        ContractDecls.rewriteStateAliases
          duplicateSourceNames scopedStateVars rest

def FunctionDecl.asLibraryHelper? (libraryName helperName : Name)
    (libraryFunctions : List FunctionDecl)
    (decl : FunctionDecl) : Option FunctionDecl :=
  if !FunctionDecl.isInlineLibraryFunction decl then
    none
  else
    match decl.name with
    | some _ =>
        let decl :=
          FunctionDecl.rewriteLibraryInternalCalls
            libraryName libraryFunctions decl
        -- An unqualified modifier on a library function is resolved in the
        -- library's lexical scope. Qualify it before this function becomes a
        -- contract-independent helper, otherwise a same-named modifier on the
        -- calling contract can capture the invocation.
        let decl :=
          { decl with
            modifiers := decl.modifiers.map (fun (invocation : ModifierInvocation) =>
              match invocation.target.segments with
              | [name] =>
                  { invocation with
                    target := { segments := [libraryName, name] } }
              | _ => invocation) }
        some { decl with
          name := some helperName }
    | none => none

def FunctionDecls.libraryHelperFunctionsFor (libraryName : Name)
    (libraryFunctions : List FunctionDecl) (constants : ConstantEnv)
    (seen : List Name) : List FunctionDecl -> List FunctionDecl
  | [] => []
  | fn :: rest =>
      let seen' :=
        match fn.name with
        | some functionName =>
            if FunctionDecl.isInlineLibraryFunction fn then
              functionName :: seen
            else
              seen
        | none => seen
      let tail :=
        FunctionDecls.libraryHelperFunctionsFor
          libraryName libraryFunctions constants seen' rest
      match fn.name with
      | some functionName =>
          let helperName :=
            libraryHelperNameForIndex libraryName functionName
              (namesCount functionName seen)
          match
              FunctionDecl.asLibraryHelper?
                libraryName helperName libraryFunctions fn with
          | some helper =>
              FunctionDecl.inlineConstants constants helper :: tail
          | none => tail
      | none => tail

def ContractDecl.libraryHelperFunctions
    (sourceConstants : ConstantEnv) (contracts : List ContractDecl) :
    List FunctionDecl :=
  concatMapList
    (fun decl =>
      if ContractDecl.isLibrary decl then
        let functions := ContractDecl.directOrdinaryFunctions decl
        let usingDecls := ContractDecl.directUsingDecls decl
        let usingFunctionScope :=
          concatMapList ContractDecl.directOrdinaryFunctions contracts
        let functions :=
          functions.map
            (FunctionDecl.expandUsingSurface
              contracts usingFunctionScope usingDecls [] (some decl.name))
        let constants :=
          StateVars.constantEnv (ContractDecl.directStateVars decl) ++
            sourceConstants
        FunctionDecls.libraryHelperFunctionsFor
          decl.name functions constants [] functions
      else
        [])
    contracts

def ContractDecls.libraryModifiers (contracts : List ContractDecl) :
    List SourceModifierDecl :=
  concatMapList
    (fun decl =>
      if ContractDecl.isLibrary decl then
        ContractDecl.directModifiersStamped decl
      else
        [])
    contracts

def ContractDecls.afterName? : List ContractDecl -> Name ->
    Option (List ContractDecl)
  | [], _ => none
  | decl :: rest, name =>
      if decl.name == name then
        some rest
      else
        ContractDecls.afterName? rest name

def ContractDecl.directStructs (decl : ContractDecl) : List StructDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.structDecl structDecl => some structDecl
    | _ => none)

def ContractDecl.directEnums (decl : ContractDecl) : List EnumDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.enumDecl enumDecl => some enumDecl
    | _ => none)

def ContractDecl.directUserValueTypes
    (decl : ContractDecl) : List UserValueTypeDecl :=
  decl.items.filterMap (fun item =>
    match item with
    | ContractItem.userValueTypeDecl userTy => some userTy
    | _ => none)

def UserTypeEnv.extendDecls (env : UserTypeEnv) :
    List UserValueTypeDecl -> UserTypeEnv
  | [] => env
  | decl :: rest =>
      UserTypeEnv.extendDecls
        (UserTypeEnv.extendDecl env decl) rest

def UserTypeEnv.extendQualifiedDecls (scope : Name)
    (env : UserTypeEnv) : List UserValueTypeDecl -> UserTypeEnv
  | [] => env
  | decl :: rest =>
      UserTypeEnv.extendQualifiedDecls scope
        (UserTypeEnv.extendQualifiedDecl env scope decl) rest

def UserTypeEnv.extendContractDecls (env : UserTypeEnv)
    (decl : ContractDecl) : UserTypeEnv :=
  UserTypeEnv.extendDecls
    (UserTypeEnv.extendQualifiedDecls decl.name env
      (ContractDecl.directUserValueTypes decl))
    (ContractDecl.directUserValueTypes decl)

def UserTypeEnv.extendContractQualifiedDecls (env : UserTypeEnv)
    (decl : ContractDecl) : UserTypeEnv :=
  UserTypeEnv.extendQualifiedDecls decl.name env
    (ContractDecl.directUserValueTypes decl)

def ContractDecl.userTypeEnvFromContracts (contracts : List ContractDecl) :
    UserTypeEnv :=
  contracts.foldl
    (fun env decl =>
      UserTypeEnv.extendContractDecls env decl)
    []

def ContractDecl.userTypeEnvFromContractsInScope (env : UserTypeEnv)
    (contracts : List ContractDecl) : UserTypeEnv :=
  contracts.reverse.foldl
    (fun env decl =>
      UserTypeEnv.extendDecls env
        (ContractDecl.directUserValueTypes decl))
    env

def ContractDecl.userTypeEnvWithQualifiedContracts (env : UserTypeEnv)
    (contracts : List ContractDecl) : UserTypeEnv :=
  contracts.foldl
    (fun env decl => UserTypeEnv.extendContractQualifiedDecls env decl)
    env

def EnumEnv.extendDecls (env : EnumEnv) :
    List EnumDecl -> EnumEnv
  | [] => env
  | decl :: rest =>
      EnumEnv.extendDecls (EnumEnv.extendDecl env decl) rest

def EnumEnv.extendQualifiedDecls (scope : Name)
    (env : EnumEnv) : List EnumDecl -> EnumEnv
  | [] => env
  | decl :: rest =>
      EnumEnv.extendQualifiedDecls scope
        (EnumEnv.extendQualifiedDecl env scope decl) rest

def EnumEnv.extendContractDecls (env : EnumEnv)
    (decl : ContractDecl) : EnumEnv :=
  EnumEnv.extendDecls
    (EnumEnv.extendQualifiedDecls decl.name env
      (ContractDecl.directEnums decl))
    -- BUG#6: the unqualified aliases keep the declaring-scope stamp so an
    -- enum referenced as `Mode` still resolves to canonical `Lib.Mode`.
    ((ContractDecl.directEnums decl).map (EnumDecl.stampScope decl.name))

def EnumEnv.extendContractQualifiedDecls (env : EnumEnv)
    (decl : ContractDecl) : EnumEnv :=
  EnumEnv.extendQualifiedDecls decl.name env
    (ContractDecl.directEnums decl)

def ContractDecl.enumEnvFromContracts (contracts : List ContractDecl) :
    EnumEnv :=
  contracts.foldl
    (fun env decl =>
      EnumEnv.extendContractDecls env decl)
    []

def ContractDecl.enumEnvFromContractsInScope (env : EnumEnv)
    (contracts : List ContractDecl) : EnumEnv :=
  contracts.reverse.foldl
    (fun env decl =>
      EnumEnv.extendDecls env
        ((ContractDecl.directEnums decl).map (EnumDecl.stampScope decl.name)))
    env

def ContractDecl.enumEnvWithQualifiedContracts (env : EnumEnv)
    (contracts : List ContractDecl) : EnumEnv :=
  contracts.foldl
    (fun env decl => EnumEnv.extendContractQualifiedDecls env decl)
    env

def StructEnv.extendDecls (env : StructEnv) :
    List StructDecl -> StructEnv
  | [] => env
  | decl :: rest =>
      StructEnv.extendDecls (StructEnv.extendDecl env decl) rest

def StructEnv.extendQualifiedDecls (scope : Name)
    (env : StructEnv) : List StructDecl -> StructEnv
  | [] => env
  | decl :: rest =>
      StructEnv.extendQualifiedDecls scope
        (StructEnv.extendQualifiedDecl env scope decl) rest

def StructEnv.extendContractDecls (env : StructEnv)
    (decl : ContractDecl) : StructEnv :=
  StructEnv.extendDecls
    (StructEnv.extendQualifiedDecls decl.name env
      (ContractDecl.directStructs decl))
    -- BUG#6: unqualified aliases keep the declaring-scope stamp (see enums).
    ((ContractDecl.directStructs decl).map (StructDecl.stampScope decl.name))

def StructEnv.extendContractQualifiedDecls (env : StructEnv)
    (decl : ContractDecl) : StructEnv :=
  StructEnv.extendQualifiedDecls decl.name env
    (ContractDecl.directStructs decl)

def ContractDecl.structEnvFromContracts (contracts : List ContractDecl) :
    StructEnv :=
  contracts.foldl
    (fun env decl =>
      StructEnv.extendContractDecls env decl)
    []

def ContractDecl.structEnvFromContractsInScope (env : StructEnv)
    (contracts : List ContractDecl) : StructEnv :=
  contracts.reverse.foldl
    (fun env decl =>
      StructEnv.extendDecls env
        ((ContractDecl.directStructs decl).map
          (StructDecl.stampScope decl.name)))
    env

def ContractDecl.structEnvWithQualifiedContracts (env : StructEnv)
    (contracts : List ContractDecl) : StructEnv :=
  contracts.foldl
    (fun env decl => StructEnv.extendContractQualifiedDecls env decl)
    env

def ModifierInvocation.targetsContract? (contracts : List ContractDecl)
    (invocation : ModifierInvocation) : Bool :=
  match pathLast? invocation.target with
  | some name =>
      match ContractDecl.findByName? contracts name with
      | some _ => true
      | none => false
  | none => false

def ModifierInvocations.dropBaseConstructorInvocations
    (contracts : List ContractDecl) :
    List ModifierInvocation -> List ModifierInvocation
  | [] => []
  | invocation :: rest =>
      let tail :=
        ModifierInvocations.dropBaseConstructorInvocations contracts rest
      if ModifierInvocation.targetsContract? contracts invocation then
        tail
      else
        invocation :: tail

/-- Qualified-constant `ConstantEnv` entries for reads through a type name.
    For every contract/library `decl`, every constant reachable through it (its
    own + inherited, in C3 order) is registered under the joined key
    `decl.name . const` — so `Base.K`, `L.LK`, and even `Derived.K` (a constant
    inherited into `Derived`) all resolve to the constant's initializer. -/
def ContractDecl.qualifiedConstantEntries (contracts : List ContractDecl)
    (decl : ContractDecl) : ConstantEnv :=
  let order :=
    match ContractDecl.dispatchOrder? contracts decl with
    | some order => order
    | none => [decl]
  concatMapList
    (fun c =>
      (ContractDecl.directStateVars c).filterMap
        (fun sv =>
          match StateVarDecl.constantEntry? sv with
          | some (_, ty, e) =>
              some
                (qualifiedConstantKey (pathOfName decl.name) sv.name, ty, e)
          | none => none))
    order

def ContractDecls.qualifiedConstantEntries (contracts : List ContractDecl) :
    ConstantEnv :=
  concatMapList (ContractDecl.qualifiedConstantEntries contracts) contracts

/-- Constants visible (unqualified) in `decl`'s OWN lexical scope: `decl`'s own
    contract-level constants plus those inherited from its base contracts, in
    C3 order (most-derived-first, so `decl`'s own constant shadows an inherited
    same-name one). File-level constants are NOT included here; the caller
    appends them as a lower-priority tail. This keeps a DERIVED contract's
    constant out of a BASE contract's function body — solc resolves an inherited
    base function's unqualified identifier in the base's scope, where only the
    base's own/inherited constants and the file-level constant are visible, so a
    same-name constant declared only in the derived contract must NOT capture it
    (and, symmetrically, the base's constant must not leak into a sibling). -/
def ContractDecl.scopedConstantEntries (contracts : List ContractDecl)
    (decl : ContractDecl) : ConstantEnv :=
  let order :=
    match ContractDecl.dispatchOrder? contracts decl with
    | some order => order
    | none => [decl]
  concatMapList
    (fun c =>
      (ContractDecl.directStateVars c).filterMap StateVarDecl.constantEntry?)
    order

/-- Names of NON-constant state variables visible (unqualified) in `decl`'s OWN
    lexical scope: `decl`'s own storage / transient / immutable state variables
    plus those inherited from its base contracts (C3). Such a variable shadows a
    same-name file-level (or qualified) `constant` inside `decl`'s function
    bodies, so that constant must NOT be inlined there — a bare read of the name
    is a storage / immutable load, not a constant fold. Mirrors the base-vs-
    derived scoping of `scopedConstantEntries`: a derived contract's storage var
    is out of an inherited base body's scope, so it cannot suppress the base's
    file-level constant. -/
def ContractDecl.scopedStateVarShadowNames (contracts : List ContractDecl)
    (decl : ContractDecl) : List Name :=
  let order :=
    match ContractDecl.dispatchOrder? contracts decl with
    | some order => order
    | none => [decl]
  concatMapList
    (fun c =>
      (ContractDecl.directStateVars c).filterMap
        (fun sv =>
          match sv.mutability with
          | VarMutability.constant => none
          | _ => some sv.name))
    order

/-- `decl`'s unqualified constant scope for body inlining: its own/inherited
    constants (C3, most-derived-first) shadowing the shared file-level +
    qualified `sharedTail`, with any entry whose name is shadowed by a
    non-constant state variable in `decl`'s scope removed. -/
def ContractDecl.scopedConstantEnv (contracts : List ContractDecl)
    (sharedTail : ConstantEnv) (decl : ContractDecl) : ConstantEnv :=
  let shadowNames := ContractDecl.scopedStateVarShadowNames contracts decl
  (ContractDecl.scopedConstantEntries contracts decl ++ sharedTail).filter
    (fun entry => !shadowNames.contains entry.1)

def ContractDecls.contextualOrdinaryFunctions (hierarchy : List ContractDecl)
    (sharedTail : ConstantEnv) (baseNames : List Name)
    (decls : List ContractDecl) : List FunctionDecl :=
  concatMapList
    (fun decl =>
      ContractDecl.contextualOrdinaryFunctions
        (ContractDecl.scopedConstantEnv hierarchy sharedTail decl)
        baseNames (ContractDecl.scopedStateVarShadowNames hierarchy decl) decl)
    decls

def ContractDecls.contextualBaseHelpers (hierarchy : List ContractDecl)
    (sharedTail : ConstantEnv) (baseNames : List Name)
    (decls : List ContractDecl) : List FunctionDecl :=
  concatMapList
    (fun decl =>
      ContractDecl.contextualBaseHelpers
        (ContractDecl.scopedConstantEnv hierarchy sharedTail decl)
        baseNames (ContractDecl.scopedStateVarShadowNames hierarchy decl) decl)
    decls

def ContractDecls.contextualSuperHelpersFor? (hierarchy : List ContractDecl)
    (sharedTail : ConstantEnv) (baseNames : List Name)
    (dispatchOrder : List ContractDecl)
    (decl : ContractDecl) : Option (List FunctionDecl) := do
  let supers ← ContractDecls.afterName? dispatchOrder decl.name
  some
    ((ContractDecls.contextualOrdinaryFunctions hierarchy sharedTail baseNames
        supers)
      |>.filterMap (FunctionDecl.asSuperHelper? decl.name))

def ContractDecls.contextualSuperHelpers? (hierarchy : List ContractDecl)
    (sharedTail : ConstantEnv) (baseNames : List Name)
    (dispatchOrder : List ContractDecl) : Option (List FunctionDecl) := do
  let groups ←
    mapOption
      (ContractDecls.contextualSuperHelpersFor? hierarchy sharedTail baseNames
        dispatchOrder)
      dispatchOrder
  some (concatLists groups)

/-- State variables `decl` inherits from the (already-linearized) `order`
    (which starts with `decl` itself): every non-private state variable of
    every ancestor, most-base-first. Private base variables are NOT in a
    derived contract's scope (solc hides them; only their storage slots
    remain), so they are excluded — a derived redeclaration of the same name
    must win the bind. -/
def ContractDecl.inheritedStateVarsOfOrder
    (order : List ContractDecl) : List StateVarDecl :=
  concatMapList
    (fun base =>
      (ContractDecl.directStateVars base).filter
        StateVarDecl.visibleFromDerived)
    (List.reverse (List.drop 1 order))

/-- State variables `decl` inherits from its linearized base contracts. -/
def ContractDecl.inheritedStateVars (contracts : List ContractDecl)
    (decl : ContractDecl) : List StateVarDecl :=
  match ContractDecl.dispatchOrder? contracts decl with
  | some order => ContractDecl.inheritedStateVarsOfOrder order
  | none => []

/-- `ContractDecl.resolveStructs` with the contract's inherited state
    variables (drawn from `contracts`, the full hierarchy universe) seeded
    into the member-rewrite type environment (#197). -/
def ContractDecl.resolveStructsInHierarchy (env : StructEnv)
    (contracts : List ContractDecl) (decl : ContractDecl) : ContractDecl :=
  ContractDecl.resolveStructsWithInheritedVars env
    (ContractDecl.inheritedStateVars contracts decl) decl

def FunctionDecl.names (functions : List FunctionDecl) : List Name :=
  functions.filterMap (fun function => function.name)

def ContractDecl.externalCallKindEntries? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option (List ExternalCallKindEntry) :=
  -- BUG#6: the same struct env `directCoreFunctions?` renders the callee-side
  -- library dispatch selectors with — caller payload and callee dispatch must
  -- hash the SAME library-qualified signature.
  let structEnv := ContractDecl.structEnvFromContracts contracts
  let entriesFrom (decls : List ContractDecl) :=
    concatMapList
      (fun d =>
        ContractDecl.directExternalCallKindEntriesAs decl.name d structEnv)
      decls
  match ContractDecl.dispatchOrder? contracts decl with
  | some dispatchOrder => some (entriesFrom dispatchOrder)
  | none =>
      some
        (ContractDecl.directExternalCallKindEntriesAs decl.name decl structEnv)

def ExternalCallKindEnv.fromContracts? (contracts : List ContractDecl) :
    Option ExternalCallKindEnv := do
  let groups ←
    mapOption (ContractDecl.externalCallKindEntries? contracts) contracts
  let constructors ←
    mapOption ContractDecl.constructorCallKindEntry? contracts
  some (concatLists groups ++ constructors)

structure StoragePackingCursor where
  slot : Nat
  offset : Nat := 0
  deriving Repr

def StoragePackingCursor.finishSlot (cursor : StoragePackingCursor) : Nat :=
  if cursor.offset == 0 then cursor.slot else cursor.slot + 1

def StoragePackingCursor.align (cursor : StoragePackingCursor) :
    StoragePackingCursor :=
  if cursor.offset == 0 then cursor
  else { slot := cursor.slot + 1, offset := 0 }

def ContractDecl.storageFieldAndNext (transient : Bool)
    (cursor : StoragePackingCursor) (stateVar : StateVarDecl) :
    CoreStorageField × StoragePackingCursor :=
  let layout? := Ty.toCoreStorageLayout? stateVar.ty
  let ty? := Ty.toCoreStorageWord? stateVar.ty
  match layout?, Ty.storagePackedBytes? stateVar.ty with
  | some (SolidCore.Solidity.Source.StorageLayout.scalar _), some bytes =>
      let fits :=
        cursor.offset + bytes <= SolidCore.Solidity.Source.wordBytes
      let slot := if fits then cursor.slot else cursor.slot + 1
      let offset := if fits then cursor.offset else 0
      let nextOffset := offset + bytes
      let next :=
        if nextOffset == SolidCore.Solidity.Source.wordBytes then
          { slot := slot + 1, offset := 0 }
        else
          { slot := slot, offset := nextOffset }
      ( { name := stateVar.name
          slot := slot
          ty? := ty?
          layout? := layout?
          transient := transient
          packedOffset := offset
          packedBytes := bytes
          packedSigned := Ty.storagePackedSigned stateVar.ty }
      , next )
  | _, _ =>
      let aligned := cursor.align
      let span :=
        match layout? with
        | some layout =>
            max 1 (SolidCore.Solidity.Source.StorageLayout.slotSpan layout)
        | none => 1
      ( { name := stateVar.name
          slot := aligned.slot
          ty? := ty?
          layout? := layout?
          transient := transient }
      , { slot := aligned.slot + span, offset := 0 } )

def ContractDecl.storageFieldsPackedFrom (transient : Bool)
    (cursor : StoragePackingCursor) :
    List StateVarDecl -> List CoreStorageField × StoragePackingCursor
  | [] => ([], cursor)
  | stateVar :: rest =>
      let (field, next) :=
        ContractDecl.storageFieldAndNext transient cursor stateVar
      let (tail, finalCursor) :=
        ContractDecl.storageFieldsPackedFrom transient next rest
      (field :: tail, finalCursor)

def ContractDecl.storageFieldsFrom (transient : Bool) (slot : Nat) :
    List StateVarDecl -> List CoreStorageField
  | stateVars =>
      (ContractDecl.storageFieldsPackedFrom transient
        { slot := slot, offset := 0 } stateVars).fst

def ContractDecl.storageFieldsSlotSpanFrom (slot : Nat)
    (stateVars : List StateVarDecl) : Nat :=
  let finalCursor :=
    (ContractDecl.storageFieldsPackedFrom false
      { slot := slot, offset := 0 } stateVars).snd
  finalCursor.finishSlot - slot

def ContractDecl.storageFieldsSlotSpan :
    List StateVarDecl -> Nat
  | stateVars => ContractDecl.storageFieldsSlotSpanFrom 0 stateVars

def ContractDecl.toCoreStorageFieldsFromSlot (transient : Bool) (slot : Word)
    (stateVars : List StateVarDecl) : List CoreStorageField :=
  ContractDecl.storageFieldsFrom transient slot stateVars

def ContractDecl.toCoreStorageFieldsFrom (transient : Bool)
    (stateVars : List StateVarDecl) : List CoreStorageField :=
  ContractDecl.toCoreStorageFieldsFromSlot transient 0 stateVars

def Expr.storageLayoutBaseErc7201IdAllowed : Expr -> Bool
  | Expr.literal (Literal.string _) => true
  | Expr.literal (Literal.unicodeString _) => true
  | _ => false

def Expr.storageLayoutBaseEvalAllowed : Expr -> Bool
  | Expr.literal (Literal.number _) => true
  | Expr.literal (Literal.unitNumber _ _) => true
  | Expr.ident _ => true
  | Expr.call (Expr.ident "erc7201") [Arg.positional id] =>
      Expr.storageLayoutBaseErc7201IdAllowed id
  | Expr.unary UnaryOp.neg inner =>
      Expr.storageLayoutBaseEvalAllowed inner
  | Expr.binary op lhs rhs =>
      BinaryOp.storageLayoutBaseEvalAllowed op &&
        Expr.storageLayoutBaseEvalAllowed lhs &&
          Expr.storageLayoutBaseEvalAllowed rhs
  | _ => false

def Expr.evalLayoutBaseCore? (expr : Expr) : Option Word := do
  if Expr.storageLayoutBaseEvalAllowed expr then
    let core ← Expr.toCore? [] expr
    match SolidCore.Solidity.Source.Expr.evalWithRuntimeByContext
        core
        SolidCore.Solidity.Source.Context.empty
        (SolidCore.Solidity.Source.Runtime.ofState
          SolidCore.Solidity.Source.State.empty) with
    | Except.ok (SolidCore.Solidity.Source.Value.word value, _) => some value
    | _ => none
  else
    none

def Expr.layoutBaseSlotValue? : Expr -> Option Word
  | expr =>
      match Expr.numberLiteralNat? expr with
      | some value => some value
      | none => Expr.evalLayoutBaseCore? expr

def ContractDecl.layoutBaseSlot? (constants : ConstantEnv)
    (decl : ContractDecl) : Option Word :=
  match decl.layoutBase with
  | none => some 0
  | some expr => do
      let expr := Expr.inlineConstants constants expr
      let value ← Expr.layoutBaseSlotValue? expr
      if value < SolidCore.Solidity.Shared.wordModulus then
        some value
      else
        none

def storageLayoutBaseFits (baseSlot : Word)
    (stateVars : List StateVarDecl) : Bool :=
  baseSlot + ContractDecl.storageFieldsSlotSpan stateVars <=
    SolidCore.Solidity.Shared.wordModulus

def ContractDecl.hasLayoutBase (decl : ContractDecl) : Bool :=
  decl.layoutBase.isSome

def ContractDecl.layoutBaseAllowed (decl : ContractDecl) : Bool :=
  match decl.layoutBase with
  | none => true
  | some _ =>
      decl.kind == ContractKind.contract && !decl.abstract

def ContractDecls.anyLayoutBase : List ContractDecl -> Bool
  | [] => false
  | decl :: rest =>
      ContractDecl.hasLayoutBase decl ||
        ContractDecls.anyLayoutBase rest

def ContractDecl.toCoreStorageFields (decl : ContractDecl) :
    List CoreStorageField :=
  match ContractDecl.layoutBaseSlot? [] decl with
  | some layoutBaseSlot =>
      ContractDecl.toCoreStorageFieldsFromSlot false layoutBaseSlot
        (ContractDecl.directStorageStateVars decl) ++
        ContractDecl.toCoreStorageFieldsFromSlot true 0
          (ContractDecl.directTransientStateVars decl)
  | none => []

def StateVarDecl.toCoreImmutableField?
    (decl : StateVarDecl) : Option (Option CoreImmutableField) :=
  match decl.mutability with
  | VarMutability.immutable => do
      let ty ← Ty.toCoreStorageWord? decl.ty
      some (some { name := decl.name, ty := ty })
  | _ => some none

def ContractDecl.toCoreImmutableFieldsFrom
    (stateVars : List StateVarDecl) : Option (List CoreImmutableField) :=
  filterMapOption StateVarDecl.toCoreImmutableField? stateVars

def ContractDecl.toCoreImmutableFields
    (decl : ContractDecl) : Option (List CoreImmutableField) :=
  ContractDecl.toCoreImmutableFieldsFrom
    (ContractDecl.directStateVars decl)

def EventParam.toCoreField? (param : EventParam) :
    Option SolidCore.Solidity.Source.EventField := do
  let ty ← Ty.toCore? param.ty
  some { ty := ty, indexed := param.indexed }

def EventDecl.toCore (decl : EventDecl) : Option CoreEventDecl := do
  let fields ← mapOption EventParam.toCoreField? decl.params
  let signature ← EventDecl.abiSignature? decl
  some
    { name := decl.name
      indexedCount := decl.params.filter (fun param => param.indexed) |>.length
      topic? :=
        if decl.anonymous then
          none
        else
          some
            (SolidCore.Solidity.Source.Keccak.digestWord signature)
      fields := fields }

def ErrorDecl.toCore (decl : ErrorDecl) : Option CoreErrorDecl := do
  let fields ← Parameters.toCoreBindings? "_err" decl.params
  let types ← Parameters.abiCanonicalTypes? decl.params
  let signature := decl.name ++ "(" ++ joinStringsWith "," types ++ ")"
  some
    { name := decl.name
      selector :=
        SolidCore.Solidity.Source.ABI.selectorFromSignature
          signature
      fields := fields.map (fun field => field.ty) }

/-- QUALIFIED-COLLISION (#136/#137): runtime event-table entries for a
    type-qualified emit `emit X.Ev(...)`. Mirrors `qualifiedConstantEntries`:
    for every contract/library `decl`, every event reachable through it (its own
    + inherited, in C3 order) is registered under the joined key
    `decl.name . Ev` — so `L.Ev` (library), `Base.Ev`, `C.Ev`, and inherited
    `Derived.Ev` all resolve to the DECLARING scope's event. The topic is
    computed from the event's REAL signature (via `EventDecl.toCore`) and only
    the lookup `name` is overwritten with the joined key, so a name collision
    with the contract's own bare-name `Ev` can never mis-target: the lowering
    keys the qualified emit by `X.Ev`, the bare emit by `Ev`. A `.`-joined key
    never collides with a real Solidity identifier. -/
def ContractDecl.qualifiedCoreEventEntries (contracts : List ContractDecl)
    (decl : ContractDecl) : List CoreEventDecl :=
  let order :=
    match ContractDecl.dispatchOrder? contracts decl with
    | some order => order
    | none => [decl]
  concatMapList
    (fun c =>
      (ContractDecl.directEvents c).filterMap
        (fun e =>
          (EventDecl.toCore e).map
            (fun ce =>
              { ce with name := qualifiedConstantKey (pathOfName decl.name) e.name })))
    order

def ContractDecls.qualifiedCoreEventEntries (contracts : List ContractDecl) :
    List CoreEventDecl :=
  concatMapList (ContractDecl.qualifiedCoreEventEntries contracts) contracts

/-- QUALIFIED-COLLISION (#136): runtime error-table entries for a type-qualified
    revert `revert X.E(...)` / `require(c, X.E(...))`. Analogue of
    `qualifiedCoreEventEntries`; the selector is computed from the error's REAL
    signature and only the lookup `name` is overwritten with the joined key
    `decl.name . E`, so a library error `L.E(uint8)` reverting through `L.E`
    encodes L's selector even when the contract declares its own colliding
    `E(uint256)`. -/
def ContractDecl.qualifiedCoreErrorEntries (contracts : List ContractDecl)
    (decl : ContractDecl) : List CoreErrorDecl :=
  let order :=
    match ContractDecl.dispatchOrder? contracts decl with
    | some order => order
    | none => [decl]
  concatMapList
    (fun c =>
      (ContractDecl.directErrors c).filterMap
        (fun e =>
          (ErrorDecl.toCore e).map
            (fun ce =>
              { ce with name := qualifiedConstantKey (pathOfName decl.name) e.name })))
    order

def ContractDecls.qualifiedCoreErrorEntries (contracts : List ContractDecl) :
    List CoreErrorDecl :=
  concatMapList (ContractDecl.qualifiedCoreErrorEntries contracts) contracts

/-- Names appearing with ≥2 DISTINCT canonical signatures — the ambiguous
    (colliding) names whose bare-name runtime lookup would mis-target. -/
def collidingNamesOf (pairs : List (Name × String)) : List Name :=
  pairs.filterMap
    (fun p =>
      if pairs.any (fun q => q.fst == p.fst && q.snd != p.snd) then some p.fst
      else none)

def EventDecls.collidingNames (decls : List EventDecl) : List Name :=
  collidingNamesOf
    (decls.filterMap
      (fun d => (EventDecl.abiSignature? d).map (fun s => (d.name, s))))

def ErrorDecl.canonicalSignature? (decl : ErrorDecl) : Option String := do
  let types ← Parameters.abiCanonicalTypes? decl.params
  some (decl.name ++ "(" ++ joinStringsWith "," types ++ ")")

def ErrorDecls.collidingNames (decls : List ErrorDecl) : List Name :=
  collidingNamesOf
    (decls.filterMap
      (fun d => (ErrorDecl.canonicalSignature? d).map (fun s => (d.name, s))))

def StateVarDecl.publicGetterParamCore? (index : Nat) (ty : Ty) :
    Option (CoreBindingDecl × CoreExpr) := do
  let coreTy ← Ty.toCore? ty
  let name := "_key" ++ toString index
  some ({ name, ty := coreTy }, SolidCore.Solidity.Source.Expr.var name)

def StateVarDecl.publicGetterParamsCore?
    (paramTys : List Ty) : Option (List CoreBindingDecl × List CoreExpr) := do
  let pairs ← mapOptionIdx StateVarDecl.publicGetterParamCore? 0 paramTys
  some (pairs.map Prod.fst, pairs.map Prod.snd)

def StateVarDecl.publicGetterBodyExpr
    (name : Name) (returnTy : Ty) (indexes : List CoreExpr)
    (fieldPath : List Nat) : CoreExpr :=
  let path :=
    indexes ++
      fieldPath.map (fun index =>
        SolidCore.Solidity.Source.Expr.word index)
  match path with
  | [] =>
      match returnTy with
      | Ty.bytes | Ty.string =>
          SolidCore.Solidity.Source.Expr.storageBytes name
      | _ => SolidCore.Solidity.Source.Expr.storage name
  | _ :: _ =>
      SolidCore.Solidity.Source.Expr.storagePath name path

def StateVarDecl.publicGetterReturnCore? (index : Nat)
    (entry : List Nat × Ty) : Option CoreBindingDecl := do
  let ty ← Ty.toCore? entry.snd
  some { name := "_value" ++ toString index, ty }

def StateVarDecl.publicGetterReturnsCore?
    (entries : List (List Nat × Ty)) : Option (List CoreBindingDecl) :=
  mapOptionIdx StateVarDecl.publicGetterReturnCore? 0 entries

def StateVarDecl.publicGetterBodyExprs (name : Name)
    (indexes : List CoreExpr) (entries : List (List Nat × Ty)) :
    List CoreExpr :=
  entries.map (fun entry =>
    StateVarDecl.publicGetterBodyExpr name entry.snd indexes entry.fst)

def StateVarDecl.toCoreRecursiveGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility with
  | some Visibility.public_ => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let shape ← Ty.publicGetterShape? 64 decl.ty
      let (paramTys, returnsWithPaths) := shape
      let (params, indexes) ←
        StateVarDecl.publicGetterParamsCore? paramTys
      let paramAbiCleanups ← Tys.toCoreAbiCleanups? paramTys
      let returns ←
        StateVarDecl.publicGetterReturnsCore? returnsWithPaths
      let signature ←
        StateVarDecl.publicGetterSignature? decl
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  signature)
            params := params
            paramAbiCleanups := paramAbiCleanups
            returns := returns
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                (StateVarDecl.publicGetterBodyExprs
                  storageName indexes returnsWithPaths) })
  | _ => some none

def StateVarDecl.toCoreMappingGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.mapping keyTy valueTy => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let keyCoreTy ← Ty.toCoreMappingKey? keyTy
      let valueCoreTy ← Ty.toCoreStorageWord? valueTy
      let keyCanonical ← Ty.abiCanonical? keyTy
      let signature := decl.name ++ "(" ++ keyCanonical ++ ")"
      let keyName := "_key0"
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  signature)
            params := [{ name := keyName, ty := keyCoreTy }]
            returns := [{ name := "_value", ty := valueCoreTy }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageIndex
                  storageName
                  (SolidCore.Solidity.Source.Expr.var keyName)] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreArrayGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.array elementTy _ => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let elementCoreTy ← Ty.toCoreStorageWord? elementTy
      let indexName := "_index0"
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "(uint256)"))
            params :=
              [{ name := indexName
                 ty := SolidCore.Solidity.Source.Ty.uint256 }]
            returns := [{ name := "_value", ty := elementCoreTy }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageIndex
                  storageName
                  (SolidCore.Solidity.Source.Expr.var indexName)] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreByteStringGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.bytes =>
      let storageName := (stateNameRuntimeKey? decl.name storageNames).getD decl.name
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns :=
              [{ name := "_value"
                 ty := SolidCore.Solidity.Source.Ty.bytesCalldata }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageBytes storageName] })
  | some Visibility.public_, Ty.string =>
      let storageName := (stateNameRuntimeKey? decl.name storageNames).getD decl.name
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns :=
              [{ name := "_value"
                 ty := SolidCore.Solidity.Source.Ty.bytesCalldata }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storageBytes storageName] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreStructGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.ty with
  | some Visibility.public_, Ty.tuple _ => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let ty ← Ty.toCore? decl.ty
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.storage storageName] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreConstantGetterIfPublic?
    (storageNames : List Name) (constants : ConstantEnv)
    (decl : StateVarDecl) : Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability, decl.init with
  | some Visibility.public_, VarMutability.constant, some init => do
      let ty ← Ty.toCore? decl.ty
      let initCore ←
        Expr.toCore? storageNames (Expr.inlineConstants constants init)
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues [initCore] })
  | some Visibility.public_, VarMutability.constant, none => none
  | some Visibility.public_, VarMutability.immutable, _ => none
  | _, _, _ => some none

def StateVarDecl.toCoreImmutableGetterIfPublic?
    (storageNames : List Name) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability with
  | some Visibility.public_, VarMutability.immutable => do
      let immutableName ← stateNameImmutableKey? decl.name storageNames
      let ty ← Ty.toCoreStorageWord? decl.ty
      some
        (some
          { name := decl.name
            selector? :=
              some
                (SolidCore.Solidity.Source.ABI.selectorFromSignature
                  (decl.name ++ "()"))
            params := []
            returns := [{ name := "_value", ty := ty }]
            body :=
              SolidCore.Solidity.Source.Stmt.returnValues
                [SolidCore.Solidity.Source.Expr.immutable immutableName] })
  | some Visibility.public_, _ => some none
  | _, _ => some none

def StateVarDecl.toCoreGetterIfPublic? (storageNames : List Name)
    (constants : ConstantEnv) (decl : StateVarDecl) :
    Option (Option CoreFunctionDef) :=
  match decl.visibility, decl.mutability with
  | some Visibility.public_, VarMutability.constant =>
      StateVarDecl.toCoreConstantGetterIfPublic?
        storageNames constants decl
  | some Visibility.public_, VarMutability.immutable =>
      StateVarDecl.toCoreImmutableGetterIfPublic? storageNames decl
  | some Visibility.public_, VarMutability.mutable
  | some Visibility.public_, VarMutability.transient =>
      StateVarDecl.toCoreRecursiveGetterIfPublic? storageNames decl
  | _, _ => some none

def StateVarDecl.toCoreInit? (storageNames : List Name)
    (constants : ConstantEnv)
    (decl : StateVarDecl) : Option CoreStmt :=
  match decl.mutability, decl.init with
  | VarMutability.mutable, some expr => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.storage storageName)
        initCore)
  | VarMutability.transient, some expr => do
      let storageName ← stateNameRuntimeKey? decl.name storageNames
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.storage storageName)
        initCore)
  | VarMutability.immutable, some expr => do
      let immutableName ← stateNameImmutableKey? decl.name storageNames
      let expr := Expr.inlineConstants constants expr
      let initCore ← Expr.toCore? storageNames expr
      some (SolidCore.Solidity.Source.Stmt.assign
        (SolidCore.Solidity.Source.LValue.immutable immutableName)
        initCore)
  | _, _ => some SolidCore.Solidity.Source.Stmt.skip

/-- Lower a state-variable initializer with the SAME internal-call-capable
    machinery a constructor-body assignment gets (CTOR-RESIDUE gap (b)).

    solc runs inline state-variable initializers as part of the constructor with
    full expression support, so an initializer that calls an internal function
    (`T y = setY();`) or otherwise needs internal-call hoisting must lower.
    `StateVarDecl.toCoreInit?` only used the plain `Expr.toCore?` path and thus
    over-rejected such initializers.

    Behaviour-preserving: the plain path is tried FIRST, so every initializer
    that already lowered keeps its exact previous core. Only initializers the
    plain path rejects reach the internal-call route, where `<name> = <expr>` is
    lowered through `Stmt.toCoreWithInternalCalls?` — the same assignment
    lowering constructor bodies use, which resolves `<name>` to the identical
    storage/immutable LValue and applies the same coercion. Initializers are
    contract-scoped (no constructor parameters in scope), so `storageRefEnv` is
    empty and `env` carries only `this` plus the hierarchy's members/state. -/
def StateVarDecl.toCoreInitWithInternalCalls?
    (internalFuel : Nat) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (constants : ConstantEnv)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (decl : StateVarDecl) : Option CoreStmt :=
  let envAware : Option CoreStmt := do
    let expr0 ← decl.init
    let expr := Expr.inlineConstants constants expr0
    if Expr.abiArgNeedsEnvCleanup? expr then some () else none
    let sourceTy ← Expr.abiTyWithEnv? env expr
    let initCore ← Expr.toCoreAsWithEnv? storageNames env sourceTy expr
    match decl.mutability with
    | VarMutability.mutable
    | VarMutability.transient => do
        let storageName ← stateNameRuntimeKey? decl.name storageNames
        some (SolidCore.Solidity.Source.Stmt.assign
          (SolidCore.Solidity.Source.LValue.storage storageName) initCore)
    | VarMutability.immutable => do
        let immutableName ← stateNameImmutableKey? decl.name storageNames
        some (SolidCore.Solidity.Source.Stmt.assign
          (SolidCore.Solidity.Source.LValue.immutable immutableName) initCore)
    | _ => none
  match envAware with
  | some coreStmt => some coreStmt
  | none =>
  match StateVarDecl.toCoreInit? storageNames constants decl with
  | some coreStmt => some coreStmt
  | none =>
      match decl.mutability, decl.init with
      | VarMutability.mutable, some expr
      | VarMutability.transient, some expr
      | VarMutability.immutable, some expr =>
          let expr := Expr.inlineConstants constants expr
          let sourceStmt :=
            Stmt.expr
              (Expr.assign (Expr.ident decl.name) AssignOp.assign expr)
          let sourceStmt := Stmt.annotateAbi env sourceStmt
          Stmt.toCoreWithInternalCalls?
            internalFuel [] env externalCallKindEnv storageNames modifiers
            functions freeFunctions [] sourceStmt
      | _, _ => none

mutual

/-- Collect the callee keys of every `Stmt.internalCall` node in a core
    statement tree (function-boundary refactor: used to elaborate super/base
    helper table entries on demand instead of eagerly — the helper candidate
    sets are O(#contracts x #functions) while actual call sites are few). -/
def CoreStmt.collectInternalCallKeys : CoreStmt -> List Name
  | SolidCore.Solidity.Source.Stmt.internalCall _ callee _ => [callee]
  | SolidCore.Solidity.Source.Stmt.block stmts =>
      CoreStmts.collectInternalCallKeys stmts
  | SolidCore.Solidity.Source.Stmt.captureReturn _ body =>
      CoreStmt.collectInternalCallKeys body
  | SolidCore.Solidity.Source.Stmt.ifElse _ thenBranch elseBranch =>
      CoreStmt.collectInternalCallKeys thenBranch ++
        CoreStmt.collectInternalCallKeys elseBranch
  | SolidCore.Solidity.Source.Stmt.switch _ cases defaultBranch =>
      CoreSwitchCases.collectInternalCallKeys cases ++
        (match defaultBranch with
          | some branch => CoreStmt.collectInternalCallKeys branch
          | none => [])
  | SolidCore.Solidity.Source.Stmt.whileLoop _ body =>
      CoreStmt.collectInternalCallKeys body
  | SolidCore.Solidity.Source.Stmt.doWhile body _ =>
      CoreStmt.collectInternalCallKeys body
  | SolidCore.Solidity.Source.Stmt.forLoop init _ post body =>
      CoreStmt.collectInternalCallKeys init ++
        CoreStmt.collectInternalCallKeys post ++
        CoreStmt.collectInternalCallKeys body
  | SolidCore.Solidity.Source.Stmt.tryExternalCall
      _ _ _ _ _ _ _ _ _ body clauses =>
      CoreStmt.collectInternalCallKeys body ++
        CoreTryCatchClauses.collectInternalCallKeys clauses
  | SolidCore.Solidity.Source.Stmt.tryContractCreate _ _ _ _ _ _ body clauses =>
      CoreStmt.collectInternalCallKeys body ++
        CoreTryCatchClauses.collectInternalCallKeys clauses
  | SolidCore.Solidity.Source.Stmt.checked body =>
      CoreStmt.collectInternalCallKeys body
  | SolidCore.Solidity.Source.Stmt.unchecked body =>
      CoreStmt.collectInternalCallKeys body
  | _ => []

def CoreStmts.collectInternalCallKeys : List CoreStmt -> List Name
  | [] => []
  | stmt :: rest =>
      CoreStmt.collectInternalCallKeys stmt ++
        CoreStmts.collectInternalCallKeys rest

def CoreSwitchCases.collectInternalCallKeys :
    List (SolidCore.Solidity.Source.Word × CoreStmt) -> List Name
  | [] => []
  | (_, stmt) :: rest =>
      CoreStmt.collectInternalCallKeys stmt ++
        CoreSwitchCases.collectInternalCallKeys rest

def CoreTryCatchClauses.collectInternalCallKeys :
    List SolidCore.Solidity.Source.TryCatchClause -> List Name
  | [] => []
  | SolidCore.Solidity.Source.TryCatchClause.clause _ _ body :: rest =>
      CoreStmt.collectInternalCallKeys body ++
        CoreTryCatchClauses.collectInternalCallKeys rest

end

/-- Demand-driven elaboration of helper table entries (function-boundary
    refactor R1). `candidates` are value-boundary helper decls (super/base
    helpers); an entry is elaborated only when its `internalTableKey?` is
    demanded by an already-emitted body, iterating to a fixpoint (helper bodies
    may demand further helpers). Fuel is `candidates.length + 1`: each
    productive round elaborates at least one candidate, so the fuel suffices. -/
def FunctionDecls.demandedHelperEntries
    (elabHelper : FunctionDecl -> Option CoreFunctionDef) :
    Nat -> List FunctionDecl -> List Name -> List CoreFunctionDef ->
    Option (List CoreFunctionDef)
  | 0, _, _, acc => some acc
  | fuel + 1, candidates, demanded, acc =>
      let hits := candidates.filter (fun fn =>
        match FunctionDecl.internalTableKey? fn with
        | some key => demanded.contains key
        | none => false)
      match hits with
      | [] => some acc
      | _ => do
          let rest := candidates.filter (fun fn =>
            match FunctionDecl.internalTableKey? fn with
            | some key => !demanded.contains key
            | none => true)
          let newEntries ←
            mapOption
              (fun fn => do
                let fd ← elabHelper fn
                let key ← FunctionDecl.internalTableKey? fn
                some { fd with name := key, selector? := none })
              hits
          let newKeys :=
            concatMapList
              (fun (fd : CoreFunctionDef) =>
                CoreStmt.collectInternalCallKeys fd.body)
              newEntries
          FunctionDecls.demandedHelperEntries elabHelper fuel rest
            (demanded ++ newKeys) (acc ++ newEntries)

/-- Deduplicate internal-linkage table entries (selector-less) by name, keeping
    the first occurrence (most-derived, C3 order — base/derived contracts each
    emit an entry for an inherited value-boundary function under the same
    `internalTableKey?`). Selector-bearing entrypoints are never dropped (public
    overloads share a plain name but carry distinct selectors). -/
def CoreFunctionDefs.dedupInternalByName
    (fns : List CoreFunctionDef) : List CoreFunctionDef :=
  (fns.foldl
    (fun (acc : List CoreFunctionDef × List Name) fn =>
      let (kept, seen) := acc
      if fn.selector?.isNone && seen.contains fn.name then
        (kept, seen)
      else
        (kept ++ [fn],
          if fn.selector?.isNone then fn.name :: seen else seen))
    ([], [])).1

def ContractDecl.directCoreFunctions? (storageNames : List Name)
    (constants : ConstantEnv)
    (extraEnv : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (contracts : List ContractDecl)
    (dispatchOrder : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (modifiers : List SourceModifierDecl) (functions : List FunctionDecl)
    (freeFunctions : List FunctionDecl)
    (eventArgEnv errorArgEnv : NamedArgParamEnv)
    (internalFnIds : List (Name × Nat))
    (eventIndexedEnv : EventIndexedEnv)
    (overloadEvents : List EventDecl)
    (decl : ContractDecl) :
    Option (List CoreFunctionDef) := do
  let getters ←
    filterMapOption (StateVarDecl.toCoreGetterIfPublic? storageNames constants)
      (ContractDecl.directStateVars decl)
  let usingDecls := ContractDecl.directUsingDecls decl ++ sourceUsingDecls
  -- Function-boundary refactor stage 2 (+ R1 perf fix): elaborate each direct
  -- function of this contract ONCE via `toCore?`, and reuse the resulting
  -- `FunctionDef` for both roles it may play — the plain-name selector-bearing
  -- entrypoint (dispatch) and the `internalTableKey?`-named selector-less table
  -- entry that contract-internal `Stmt.internalCall`s resolve against. The body
  -- is identical in both roles; only `name`/`selector?` differ. (An earlier cut
  -- ran `toCore?` twice per public value-boundary function, roughly doubling
  -- whole-contract elaboration cost on entrypoint-heavy lanes.)
  let functionPairs ←
    mapOption
      (fun fn => do
        let supers ← ContractDecls.afterName? dispatchOrder decl.name
        let fd ←
          FunctionDecl.toCore?
            storageNames constants extraEnv contracts usingDecls modifiers
            functions freeFunctions fn
            (concatMapList ContractDecl.directOrdinaryFunctions supers)
            (some decl.name) (dispatchOrder.map ContractDecl.name)
            externalCallKindEnv eventArgEnv errorArgEnv internalFnIds
            (structEnv := ContractDecl.structEnvFromContracts contracts)
            (eventIndexedEnv := eventIndexedEnv)
            (overloadEvents := overloadEvents)
        -- BUG#6: a LIBRARY's dispatch entrypoints answer to the
        -- library-qualified selector (what solc's delegatecall dispatch
        -- hashes), keeping callee dispatch symmetric with the caller-side
        -- payload. Contract entrypoints keep the external-ABI selector.
        let fd :=
          if decl.kind == ContractKind.library then
            { fd with
              selector? :=
                FunctionDecl.libraryAbiSelector?
                  (ContractDecl.structEnvFromContracts contracts) fn }
          else
            fd
        some (fn, fd))
      ((ContractDecl.directOrdinaryFunctions decl).filter
        (fun fn =>
          (FunctionDecl.isCoreEntrypoint fn ||
            FunctionDecl.isBoundaryCallee fn) && fn.body.isSome))
  let entrypointFunctions :=
    (functionPairs.filter
      (fun pair => FunctionDecl.isCoreEntrypoint pair.fst)).map Prod.snd
  let internalEntries :=
    functionPairs.filterMap
      (fun pair =>
        if FunctionDecl.isBoundaryCallee pair.fst then
          (FunctionDecl.internalTableKey? pair.fst).map
            (fun key => { pair.snd with name := key, selector? := none })
        else
          none)
  some (getters ++ entrypointFunctions ++ internalEntries)

def Parameters.baseConstructorArgCoreDecls?
    (internalFuel : Nat) (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl) (env : TypeEnv)
    (externalCallKindEnv : ExternalCallKindEnv)
    (storageNames : List Name) (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl) :
    Nat -> List Parameter -> List Expr -> Option (List CoreStmt)
  | _, [], [] => some []
  | index, param :: params, arg :: args => do
      let evalName := "#solidcore_base_arg_eval_" ++ toString index
      let coreTy ← Ty.toCore? param.ty
      let evalDecl :=
        if param.location == some DataLocation.memory then
          SolidCore.Solidity.Source.Stmt.memoryVarDecl coreTy evalName none
        else
          SolidCore.Solidity.Source.Stmt.varDecl coreTy evalName none
      let evalEnv := TypeEnv.extend? env (some evalName) (some param.ty)
      let sourceStmt :=
        Stmt.expr
          (Expr.assign (Expr.ident evalName) AssignOp.assign arg)
      let sourceStmt :=
        Stmt.expandUsing allContracts (functions ++ freeFunctions)
          sourceUsingDecls evalEnv sourceStmt
      let sourceStmt := Stmt.annotateAbi evalEnv sourceStmt
      let evalCore ←
        Stmt.toCoreWithInternalCalls?
          internalFuel [] evalEnv externalCallKindEnv storageNames modifiers
          functions freeFunctions [] sourceStmt
      let paramDecl ←
        Parameter.toStorageAwareCoreArgDecl?
          [] storageNames evalEnv "_arg" index param (Expr.ident evalName)
      let rest ←
        Parameters.baseConstructorArgCoreDecls?
          internalFuel allContracts sourceUsingDecls env externalCallKindEnv
          storageNames modifiers functions freeFunctions (index + 1)
          params args
      some (evalDecl :: evalCore :: paramDecl :: rest)
  | _, _, _ => none

def ContractDecl.constructorBodyForDeployment?
    (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (baseArgUsingDecls : List UsingDecl)
    (storageNames : List Name) (constants : ConstantEnv)
    (stateEnv : TypeEnv) (externalCallKindEnv : ExternalCallKindEnv)
    (modifiers : List SourceModifierDecl)
    (functions freeFunctions : List FunctionDecl)
    (eventArgEnv errorArgEnv : NamedArgParamEnv)
    (internalFnIds : List (Name × Nat))
    (eventIndexedEnv : EventIndexedEnv)
    (overloadEvents : List EventDecl)
    (targetName : Name) (supplyingParams : List Parameter)
    (baseArgs : List Expr) (decl : ContractDecl) :
    Option (List CoreBindingDecl × List CoreStmt × List CoreStmt × List CoreStmt) := do
  -- Returns the per-contract pieces the deployment constructor is assembled
  -- from, kept SEPARATE so the caller can reproduce solc's legacy ordering:
  --   (constructorParams, initStmts, ownArgCore, bodyStmts)
  -- * `initStmts`   — this contract's inline state-variable initializers; the
  --   caller hoists ALL of them (base->derived) ahead of every constructor
  --   body (legacy `ContractCompiler::appendInitAndConstructorCode`).
  -- * `ownArgCore`  — statements binding THIS contract's constructor params to
  --   the arguments its immediate-derived contract supplied; the caller emits
  --   them inside the deriving contract's frame during the derived->base
  --   descent (legacy `appendBaseConstructor`: eval args, then recurse).
  -- * `bodyStmts`   — this contract's constructor body (+ param cleanups for
  --   the most-derived contract). Bodies run base->derived.
  let initEnv := TypeEnv.extendThis stateEnv (some targetName)
  let initStmts ←
    mapOption
      (StateVarDecl.toCoreInitWithInternalCalls?
        defaultInternalCallInlineFuel initEnv externalCallKindEnv storageNames
        constants modifiers functions freeFunctions)
      (ContractDecl.directStateVars decl)
  let baseArgs := baseArgs.map (Expr.inlineConstants constants)
  -- Base-constructor arguments are evaluated in the SUPPLYING (immediate-derived)
  -- contract's frame: its constructor parameters are in scope (a middle contract
  -- can pass its own base's args via `C(...) B(c * 2)`), while `this` stays the
  -- most-derived contract being deployed. `supplyingParams` are that supplying
  -- contract's constructor params (empty for the most-derived contract, which
  -- receives no incoming base args). In the two-contract case the supplying
  -- contract IS the target, so this is identical to the prior target-frame env.
  let baseArgEnv := Parameters.extendTypeEnv "_arg" initEnv supplyingParams
  match ContractDecl.directConstructors decl with
  | [] => some ([], initStmts, [], [])
  | [ctor] => do
      let ctor := FunctionDecl.inlineConstants constants ctor
      let (params, baseArgCore) ←
        if decl.name == targetName then
          let params ← Parameters.toCoreBindings? "_arg" ctor.params
          some (params, [])
        else
          let argDecls ←
            Parameters.baseConstructorArgCoreDecls?
              defaultInternalCallInlineFuel allContracts baseArgUsingDecls
              baseArgEnv externalCallKindEnv storageNames modifiers functions
              freeFunctions 0 ctor.params baseArgs
          some ([], argDecls)
      let body :=
        match ctor.body with
        | some stmt => stmt
        | none => Stmt.empty
      let body := Stmt.inlineConstants constants body
      let usingDecls := ContractDecl.directUsingDecls decl ++ sourceUsingDecls
      let env := FunctionDecl.typeEnv stateEnv ctor
      let usingFunctionScope := functions ++ freeFunctions
      let body :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          body
        else
          Stmt.expandUsing allContracts usingFunctionScope usingDecls env body
      let modifiers :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          modifiers
        else
          modifiers.map
            (ModifierDecl.expandUsing
              allContracts usingFunctionScope usingDecls env)
      let body := Stmt.resolveNamedEventErrorArgs eventArgEnv errorArgEnv body
      -- Rewrite function-pointer VALUE uses in the constructor body (and the
      -- modifier bodies inlined into it) to their dispatch-ID literals, exactly
      -- as ordinary function bodies get (boundary-completion arc, ctor/modifier
      -- residue). `internalFnIds` is the SAME numbering the runtime dispatch
      -- table is stamped with, so the ID the constructor writes into storage
      -- dispatches to the intended function post-deployment.
      let body :=
        Stmt.rewriteInternalFnValueIdents internalFnIds
          (FunctionDecl.fnValueScopeBoundNames ctor) body
      let modifiers :=
        modifiers.map
          (fun modifier =>
            { modifier with
              body :=
                (modifier.body.map
                  (Stmt.resolveNamedEventErrorArgs eventArgEnv errorArgEnv)).map
                  (Stmt.rewriteInternalFnValueIdents internalFnIds
                    (Parameters.boundNames modifier.params)) })
      -- EVENT-OVERLOAD (soundness): rewrite overloaded bare-name emits in the
      -- constructor body (and its modifier bodies) to their signature keys,
      -- exactly as ordinary function bodies get.
      let body := Stmt.resolveOverloadedEventEmits overloadEvents env body
      let modifiers :=
        modifiers.map
          (fun modifier =>
            { modifier with
              body := modifier.body.map
                (Stmt.resolveOverloadedEventEmits overloadEvents
                  (Parameters.extendTypeEnv "_mod" env modifier.params)) })
      let body := Stmt.annotateAbi env body
      let storageRefEnv := Parameters.extendStorageRefEnv "_arg" [] ctor.params
      let ctorModifiers :=
        ModifierInvocations.dropBaseConstructorInvocations
          allContracts ctor.modifiers
      let ctorModifiers :=
        if usingDecls.isEmpty && !ContractDecls.hasLibrary allContracts then
          ctorModifiers
        else
          ctorModifiers.map
            (ModifierInvocation.expandUsing
              allContracts freeFunctions usingDecls env)
      -- A constructor parameter likewise shadows a same-named state variable in
      -- the constructor body (same nearest-declaration resolution).
      let ctorBodyStorageNames :=
        stateNamesExcludingBound (Parameters.boundNames ctor.params) storageNames
      let bodyCore ←
        functionExpandModifiersToCoreWithInternalCallsFull?
          defaultInternalCallInlineFuel storageRefEnv env externalCallKindEnv
          storageNames ctorBodyStorageNames [] modifiers functions freeFunctions
          [] ctorModifiers body
          (structEnv := ContractDecl.structEnvFromContracts allContracts)
          (eventIndexedEnv := eventIndexedEnv)
      let paramCleanups ← Parameters.toCoreCleanupStmts? "_arg" ctor.params
      if decl.name == targetName then
        -- Most-derived contract: params are ABI-decoded (bound via `params`);
        -- `paramCleanups` sanitize them ahead of the body. No incoming
        -- base-constructor args (nothing derives this contract).
        some (params, initStmts, [], paramCleanups ++ [bodyCore])
      else
        -- Base contract: its params are bound by `baseArgCore` (the args the
        -- deriving contract supplied), which the caller emits in the deriving
        -- contract's frame during the derived->base descent.
        some (params, initStmts, baseArgCore, [bodyCore])
  | _ => none

def ContractDecl.toCoreFromOrders? (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl) (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (storageOrder dispatchOrder : List ContractDecl) :
    Option CoreContract := do
  let allContracts :=
    appendUniqueContracts allContracts
      (appendUniqueContracts storageOrder dispatchOrder)
  let userEnv :=
    let freeEnv := UserTypeEnv.extendDecls [] sourceUserValueTypes
    ContractDecl.userTypeEnvFromContractsInScope
      (ContractDecl.userTypeEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let enumEnv :=
    let freeEnv := EnumEnv.extendDecls [] sourceEnums
    ContractDecl.enumEnvFromContractsInScope
      (ContractDecl.enumEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let allContracts :=
    allContracts.map (ContractDecl.resolveEnums enumEnv)
  let sourceUsingDecls :=
    sourceUsingDecls.map (UsingDecl.resolveEnums enumEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveEnums enumEnv)
  let sourceEvents :=
    sourceEvents.map (EventDecl.resolveEnums enumEnv)
  let sourceErrors :=
    sourceErrors.map (ErrorDecl.resolveEnums enumEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveEnums enumEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveEnums enumEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveEnums enumEnv)
  let structEnv :=
    let freeEnv := StructEnv.extendDecls [] sourceStructs
    ContractDecl.structEnvFromContractsInScope
      (ContractDecl.structEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let usingContracts := allContracts
  let usingFreeFunctions :=
    sourceFunctions ++
      concatMapList ContractDecl.directOrdinaryFunctions usingContracts
  let usingSourceDecls := sourceUsingDecls
  let allContracts :=
    allContracts.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let sourceConstants :=
    sourceConstants.map
      (StateVarDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls [])
  let storageOrder :=
    storageOrder.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let sourceUsingDecls := []
  let structHierarchy := allContracts
  let allContracts :=
    allContracts.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveStructs structEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveStructs structEnv)
  let sourceEvents := sourceEvents.map (EventDecl.resolveStructs structEnv)
  let sourceErrors := sourceErrors.map (ErrorDecl.resolveStructs structEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveStructs structEnv)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let postStructUsingContracts := allContracts
  let postStructUsingFreeFunctions :=
    sourceFunctions ++
      concatMapList ContractDecl.directOrdinaryFunctions postStructUsingContracts
  let allContracts :=
    allContracts.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let allContracts := allContracts.map (ContractDecl.resolveUserTypes userEnv)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveUserTypes userEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveUserTypes userEnv)
  let sourceEvents := sourceEvents.map (EventDecl.resolveUserTypes userEnv)
  let sourceErrors := sourceErrors.map (ErrorDecl.resolveUserTypes userEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveUserTypes userEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveUserTypes userEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveUserTypes userEnv)
  let interfaceIdEnv ← ContractDecls.interfaceIdEnv allContracts
  let allContracts := allContracts.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveInterfaceIds interfaceIdEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  -- QUALIFIED-COLLISION (#136/#137): rewrite AMBIGUOUS type-qualified emit/
  -- revert/require callees to `.`-joined `qualifiedConstantKey` names so a
  -- library member whose bare name collides with a differently-signed contract
  -- member resolves to the correct selector/topic0 (the runtime table carries
  -- matching qualified entries). Non-ambiguous qualified callees stay bare, so
  -- base-/self-qualified emits/reverts (which solc forbids from shadowing an
  -- inherited name, hence never ambiguous) are byte-identical.
  let collidingEvents :=
    EventDecls.collidingNames
      (concatMapList ContractDecl.directEvents dispatchOrder ++ sourceEvents ++
        concatMapList ContractDecl.directEvents
          (allContracts.filter
            (fun d => ContractDecl.isLibrary d || ContractDecl.isInterface d)))
  let collidingErrors :=
    ErrorDecls.collidingNames
      (concatMapList ContractDecl.directErrors dispatchOrder ++ sourceErrors ++
        concatMapList ContractDecl.directErrors
          (allContracts.filter ContractDecl.isLibrary))
  let allContracts :=
    allContracts.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let sourceFunctions :=
    sourceFunctions.map
      (FunctionDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  if !namesUnique (sourceConstants.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.allConstants sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits stateVars then
    none
  else
    some ()
  let allContractFunctions :=
    concatMapList ContractDecl.directOrdinaryFunctions allContracts
  let allContractErrors := concatMapList ContractDecl.directErrors allContracts
  let allContractStateVars :=
    concatMapList ContractDecl.directStateVars allContracts
  let qualifiedSelectorEnv :=
    concatMapList
      (fun decl =>
        -- BUG#6: `L.f.selector` on a LIBRARY function is the
        -- library-qualified selector (`isOff(Lib.Mode)`), not the
        -- external-ABI one. Contract entries are unchanged.
        if decl.kind == ContractKind.library then
          FunctionDecls.libraryQualifiedSelectorEntries structEnv decl.name
            (ContractDecl.directOrdinaryFunctions decl)
        else
          FunctionDecls.qualifiedSelectorEntries decl.name
            (ContractDecl.directOrdinaryFunctions decl))
      allContracts
  -- ERROR-SELECTOR-COLLISION (#139): qualified `Contract.Bad` keys over ALL
  -- contracts/libraries, so a type-qualified `L.Bad.selector` / `Base.Bad.selector`
  -- resolves to the declaring scope's selector even under a same-name collision
  -- (mirrors the qualified FUNCTION/EVENT selector entries).
  let qualifiedErrorSelectorEnv :=
    concatMapList
      (fun decl =>
        ErrorDecls.qualifiedSelectorEntries decl.name
          (ContractDecl.directErrors decl))
      allContracts
  -- The bare `Bad.selector` scope is PER-CONTRACT: solc resolves it against the
  -- errors visible to the enclosing contract (own + inherited + unshadowed
  -- file-level), exactly as the type-checker does via `ErrorSigs.resolveByName
  -- env.errors`. `dispatchOrder` is the target contract's linearization, so its
  -- direct errors ARE the target's own+inherited errors; within a single
  -- linearization solc forbids redeclaring an inherited error name, so these
  -- never self-collide. A same-name error in a SIBLING contract no longer
  -- poisons the bare name for the target.
  let targetContractErrors := concatMapList ContractDecl.directErrors dispatchOrder
  let targetVisibleSourceErrors :=
    ErrorDecls.withoutNamesOf targetContractErrors sourceErrors
  let selectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (sourceErrors ++ allContractErrors) ++
    StateVarDecls.selectorEntries allContractStateVars
  -- Bare-selector env for the TARGET contract's own code (dispatch/storage
  -- orders): only the target's visible errors, plus qualified keys and the
  -- function selectors.
  let targetUnqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (targetContractErrors ++ targetVisibleSourceErrors)
  -- Bare-selector env for FREE functions/constants: file-level errors only
  -- (free functions cannot see any contract's errors).
  let freeUnqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries sourceErrors
  -- Global fallback env for LIBRARY/other contracts pulled from `allContracts`
  -- (e.g. inlined library helpers): keep the historical whole-program error
  -- table so a library helper's own error `.selector` still resolves.
  let unqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (sourceErrors ++ allContractErrors)
  let eventSelectorEnv :=
    let contractEvents := concatMapList ContractDecl.directEvents dispatchOrder
    let visibleSourceEvents :=
      EventDecls.withoutNamesOf contractEvents sourceEvents
    -- QUALIFIED EVENT SELECTOR (#137 `.selector`): qualified `Contract.Ev` keys
    -- over ALL contracts/libraries (so `Base.Ev.selector` / `L.Ping.selector`
    -- resolve to the declaring scope's topic0 under a collision), plus the bare
    -- own/inherited entries for `Ev.selector`.
    concatMapList
      (fun decl =>
        EventDecls.qualifiedSelectorEntries decl.name
          (ContractDecl.directEvents decl))
      allContracts ++
    EventDecls.selectorEntries (contractEvents ++ visibleSourceEvents)
  let functionAddressEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let allContracts :=
    allContracts.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveFunctionAddresses functionAddressEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let allContracts :=
    allContracts.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv unqualifiedSelectorEnv)
  let sourceFunctions :=
    sourceFunctions.map
      (FunctionDecl.resolveSelectorsWithUnqualified
        selectorEnv freeUnqualifiedSelectorEnv)
  let sourceConstants :=
    sourceConstants.map
      (StateVarDecl.resolveSelectorsWithUnqualified
        selectorEnv freeUnqualifiedSelectorEnv)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv targetUnqualifiedSelectorEnv)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv targetUnqualifiedSelectorEnv)
  let allContracts :=
    allContracts.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveEventSelectors eventSelectorEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveEventSelectors eventSelectorEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let scopedStateVars := ContractDecls.scopedStateVars storageOrder
  let duplicateStateNames :=
    duplicateNames
      ((scopedStateVars.filter
        (fun scopedVar => !StateVarDecl.isConstant scopedVar.decl)).map
          (fun scopedVar => scopedVar.decl.name))
  let storageOrder :=
    ContractDecls.rewriteStateAliases
      duplicateStateNames scopedStateVars storageOrder
  let dispatchOrder :=
    ContractDecls.rewriteStateAliases
      duplicateStateNames scopedStateVars dispatchOrder
  let stateVars :=
    ScopedStateVarDecls.coreDecls duplicateStateNames scopedStateVars
  let sourceConstantEnv := StateVars.constantEnv sourceConstants
  let constants :=
    StateVars.constantEnv stateVars ++ sourceConstantEnv ++
      ContractDecls.qualifiedConstantEntries allContracts
  let storageStateVars := stateVars.filter StateVarDecl.isStorageBacked
  let transientStateVars := stateVars.filter StateVarDecl.isTransient
  let immutableStateVars := stateVars.filter StateVarDecl.isImmutable
  let storageAliases :=
    ScopedStateVarDecls.runtimeNameAliasEntries
      duplicateStateNames scopedStateVars
  let storageNames :=
    storageAliases ++
      stateNamesFrom (storageStateVars ++ transientStateVars) immutableStateVars
  let targetDecl ← dispatchOrder.head?
  if !ContractDecl.layoutBaseAllowed targetDecl then
    none
  else
    some ()
  if ContractDecls.anyLayoutBase (List.drop 1 dispatchOrder) then
    none
  else
    some ()
  let layoutBaseSlot ← ContractDecl.layoutBaseSlot? constants targetDecl
  if !storageLayoutBaseFits layoutBaseSlot storageStateVars then
    none
  else
    some ()
  let externalCallKindEnv ← ExternalCallKindEnv.fromContracts? allContracts
  let externalCallKindTypeEnv ← ExternalCallKindEnv.toTypeEnv? externalCallKindEnv
  let stateEnv := StateVars.extendTypeEnv externalCallKindTypeEnv stateVars
  -- Per-contract constant scope: each contract's own/inherited constants (C3,
  -- most-derived-first) shadow the shared file-level + qualified tail, but a
  -- derived contract's constant never leaks into a base contract's function
  -- body. The `dispatchOrder` (the target's C3 linearization) is closed under
  -- bases, so it is a sufficient universe to re-derive each contract's own
  -- linearization for scoping.
  let sharedConstantTail :=
    sourceConstantEnv ++ ContractDecls.qualifiedConstantEntries allContracts
  let modifiers :=
    concatMapList
      (fun decl =>
        (ContractDecl.directModifiersStamped decl).map
          (ModifierDecl.inlineConstants
            (ContractDecl.scopedConstantEnv dispatchOrder
              sharedConstantTail decl)))
      dispatchOrder ++ ContractDecls.libraryModifiers allContracts
  let baseNames := dispatchOrder.map ContractDecl.name
  let ordinaryFunctions :=
    ContractDecls.contextualOrdinaryFunctions dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let libraryHelpers :=
    ContractDecl.libraryHelperFunctions sourceConstantEnv allContracts
  let baseHelpers :=
    ContractDecls.contextualBaseHelpers dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let superHelpers ←
    ContractDecls.contextualSuperHelpers? dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.inlineConstants sourceConstantEnv)
  let availableFunctions :=
    ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers
  -- Stage C: per-contract internal-dispatch numbering — functions used as
  -- VALUES get IDs 1..n (first-use order across the ordinary function bodies
  -- in declaration order), mirroring solc via-IR
  -- (docs/refs-completion-solc-research.md §2).
  -- A name that is ALSO a state variable is excluded: a public state variable
  -- may OVERRIDE an inherited virtual function (`uint256 public override
  -- value;`), and a bare identifier then reads the VARIABLE — rewriting it to
  -- a dispatch ID corrupts the read (caught by the frontend-frontier lane).
  let fnIdCandidates :=
    ((availableFunctions ++ sourceFunctions).filterMap FunctionDecl.name).filter
      (fun n => !storageNames.contains n)
  -- Include modifier- and constructor-body value uses so a function used as a
  -- value ONLY inside a modifier or constructor still gets a dispatch ID and a
  -- table stamp (boundary-completion arc, ctor/modifier residue). The
  -- constructor elaboration path numbers with identical arguments.
  let constructorDecls : List FunctionDecl :=
    concatMapList ContractDecl.directConstructors dispatchOrder
  let internalFnIds :=
    FunctionDecls.internalFnValueNumberingFull fnIdCandidates ordinaryFunctions
      modifiers constructorDecls
  let contractEvents := concatMapList ContractDecl.directEvents dispatchOrder
  let visibleSourceEvents := EventDecls.withoutNamesOf contractEvents sourceEvents
  let contractErrors := concatMapList ContractDecl.directErrors dispatchOrder
  let visibleSourceErrors := ErrorDecls.withoutNamesOf contractErrors sourceErrors
  let eventArgEnv :=
    EventDecls.namedArgEnv (contractEvents ++ visibleSourceEvents)
  let eventIndexedEnv :=
    EventDecls.indexedEnv (contractEvents ++ visibleSourceEvents)
  let errorArgEnv :=
    ErrorDecls.namedArgEnv (contractErrors ++ visibleSourceErrors)
  -- Each contract's entrypoint/getter bodies are re-elaborated from the raw
  -- declaration via `toCore?`, which re-inlines against the constant env passed
  -- here. Use that contract's OWN scoped constant env (own/inherited constants
  -- over the file-level + qualified tail, with names shadowed by a non-constant
  -- state variable removed) rather than the flat whole-program `constants`, so a
  -- storage/immutable variable that shadows a same-name file-level constant is
  -- read from storage instead of being constant-folded (and a derived
  -- contract's constant does not leak into a base entrypoint body).
  let functionGroups ←
    mapOption
      (fun decl =>
        ContractDecl.directCoreFunctions?
          storageNames
          (ContractDecl.scopedConstantEnv dispatchOrder sharedConstantTail decl)
          stateEnv externalCallKindEnv allContracts
          dispatchOrder sourceUsingDecls modifiers availableFunctions
          sourceFunctions eventArgEnv errorArgEnv internalFnIds eventIndexedEnv
          (contractEvents ++ visibleSourceEvents) decl)
      dispatchOrder
  -- Function-boundary refactor stage 3: value-boundary synthetic helpers
  -- (library `__library_*`, super/base helpers) get selector-less table entries
  -- under the same `internalTableKey?` the call-site emits. Elaborated once via
  -- `toCore?` with the full contract context (they may read storage), mirroring
  -- the splice-era treatment: bodies are already contextualized/super-free
  -- (`contextualSuperHelpers?`/`libraryHelperFunctions`), so no contract-name
  -- rewrites are re-run.
  -- R1 perf: LIBRARY helpers are eager (small set; constructors may call them
  -- via `using`), but SUPER/BASE helpers are elaborated ON DEMAND — the
  -- candidate sets are O(#contracts x #functions) (`asBaseHelper?` maps every
  -- function of every contract) while actual call sites are few, and eagerly
  -- elaborating them all made whole-contract elaboration ~5x slower (measured
  -- on the openzeppelin-erc20 lane: 7.3s -> 36s per eval). Demand is seeded
  -- from every eagerly-emitted body and iterated to a fixpoint.
  let elabHelper := fun (fn : FunctionDecl) =>
    FunctionDecl.toCore?
      storageNames constants stateEnv allContracts sourceUsingDecls
      modifiers availableFunctions sourceFunctions fn
      (superFunctions := []) (contractName? := none)
      (baseNames := []) (externalCallKindEnv := externalCallKindEnv)
      (eventArgEnv := eventArgEnv) (errorArgEnv := errorArgEnv)
      (internalFnIds := internalFnIds) (structEnv := structEnv)
      (eventIndexedEnv := eventIndexedEnv)
      (overloadEvents := contractEvents ++ visibleSourceEvents)
  let libraryInternalEntries ←
    filterMapOption
      (fun fn =>
        if FunctionDecl.isBoundaryCallee fn && fn.body.isSome then do
          let fd ← elabHelper fn
          let key ← FunctionDecl.internalTableKey? fn
          some (some { fd with name := key, selector? := none })
        else
          some none)
      libraryHelpers
  -- Function-boundary refactor stage 2: value-boundary FREE functions also get
  -- selector-less table entries (they are resolved via the freeFunctions branch
  -- of `internalCallParts?` and node-emitted under the same `internalTableKey?`).
  -- Appended AFTER the contract groups so a same-signature contract function's
  -- entry wins the key on lookup/dedup, matching the call-site resolver's
  -- contract-functions-first precedence.
  let freeInternalEntries ←
    filterMapOption
      (fun fn =>
        if FunctionDecl.isBoundaryCallee fn && fn.body.isSome then do
          let fd ←
            FunctionDecl.toCore?
              [] constants externalCallKindTypeEnv allContracts
              sourceUsingDecls [] [] sourceFunctions fn
              (superFunctions := []) (contractName? := none)
              (baseNames := []) (externalCallKindEnv := externalCallKindEnv)
              (eventArgEnv := eventArgEnv) (errorArgEnv := errorArgEnv)
              (internalFnIds := internalFnIds) (structEnv := structEnv)
              (eventIndexedEnv := eventIndexedEnv)
          let key ← FunctionDecl.internalTableKey? fn
          some (some { fd with name := key, selector? := none })
        else
          some none)
      sourceFunctions
  let eagerEntries :=
    concatLists functionGroups ++ libraryInternalEntries ++ freeInternalEntries
  let helperCandidates :=
    (superHelpers ++ baseHelpers).filter
      (fun fn => FunctionDecl.isBoundaryCallee fn && fn.body.isSome)
  let seedKeys :=
    concatMapList
      (fun (fd : CoreFunctionDef) => CoreStmt.collectInternalCallKeys fd.body)
      eagerEntries
  let demandedEntries ←
    FunctionDecls.demandedHelperEntries elabHelper
      (helperCandidates.length + 1) helperCandidates seedKeys []
  let functions :=
    CoreFunctionDefs.dedupInternalByName (eagerEntries ++ demandedEntries)
  -- Stage C: stamp dispatch IDs onto the selector-less table entries of the
  -- numbered (used-as-value) functions; `Contract.table` projects them onto
  -- `InternalFunction.id?` for run-time pointer dispatch.
  let fnKeyIds : List (Name × Nat) :=
    internalFnIds.filterMap
      (fun (pair : Name × Nat) => do
        let fnDecl ←
          (availableFunctions ++ sourceFunctions).find?
            (fun fn => fn.name == some pair.fst)
        let key ← FunctionDecl.internalTableKey? fnDecl
        some (key, pair.snd))
  let functions :=
    functions.map
      (fun fd =>
        match fnKeyIds.lookup fd.name with
        | some id =>
            if fd.selector?.isNone then
              { fd with dispatchId? := some (id : Word) }
            else
              fd
        | none => fd)
  let immutableFields ←
    ContractDecl.toCoreImmutableFieldsFrom stateVars
  -- EMIT-QUAL cross-scope case (#137 / interface follow-up): a `emit X.Ev(...)`
  -- names an event declared in a LIBRARY or INTERFACE (e.g. an interface event
  -- emitted from a library, `emit I.E()`), not in the contract's own/inherited
  -- event scope. Add those events (by name, without shadowing a same-named
  -- contract event) to the runtime event table so a NON-colliding qualified emit
  -- resolves its topic0 by the bare name — mirroring `extraLibraryErrors`. The
  -- typecheck (`contractEventSig?`) already accepts an interface-qualified emit;
  -- without the interface's event in the table the bare-name lookup dead-ended in
  -- `Panic(0)` where solc+EVM emit the event.
  let libraryEvents :=
    concatMapList ContractDecl.directEvents
      (allContracts.filter
        (fun d => ContractDecl.isLibrary d || ContractDecl.isInterface d))
  let extraLibraryEvents :=
    EventDecls.withoutNamesOf (contractEvents ++ visibleSourceEvents)
      libraryEvents
  let eventDecls ←
    mapOption EventDecl.toCore
      (contractEvents ++ visibleSourceEvents ++ extraLibraryEvents)
  -- EVENT-OVERLOAD (soundness): same-scope event overloads are legal in solc
  -- (error 5883 only rejects EQUAL parameter types). The bare-name table keys
  -- above bind every `emit E(...)` to the FIRST decl named `E`; the lowering
  -- (`Stmt.resolveOverloadedEventEmits`) rewrites overloaded emits to their
  -- canonical-ABI-signature keys (e.g. `"E(uint256)"`), so register a
  -- signature-keyed entry for every event whose name is overloaded in the
  -- bare-name scope. Purely ADDITIVE: a parenthesized signature can never
  -- collide with an identifier or a `.`-joined qualified key, so non-overload
  -- lookups are byte-identical.
  let overloadScope := contractEvents ++ visibleSourceEvents
  let overloadSigEventDecls :=
    overloadScope.filterMap
      (fun e =>
        if (overloadScope.filter (fun o => o.name == e.name)).length >= 2 then
          match EventDecl.toCore e, EventDecl.abiSignature? e with
          | some ce, some signature => some { ce with name := signature }
          | _, _ => none
        else
          none)
  let eventDecls := eventDecls ++ overloadSigEventDecls
  -- QUALIFIED-COLLISION (#137): an AMBIGUOUS `emit X.Ev(...)` (a library event
  -- whose bare name collides with a differently-signed contract event) is
  -- lowered to the `.`-joined key `X.Ev`; register those keyed entries so it
  -- resolves to L's topic even under the collision.
  let eventDecls :=
    eventDecls ++ ContractDecls.qualifiedCoreEventEntries allContracts
  -- REVERT-QUAL library case (#102/5): a `revert L.Err(...)` names an error
  -- declared in a LIBRARY, which is not in the contract's own/inherited error
  -- scope. Add library errors (by name, without shadowing a same-named contract
  -- error) to the runtime error table so `findErrorDecl?` can encode the
  -- selector + args. solc computes the same canonical selector regardless of the
  -- declaring scope.
  let libraryErrors :=
    concatMapList ContractDecl.directErrors
      (allContracts.filter ContractDecl.isLibrary)
  let extraLibraryErrors :=
    ErrorDecls.withoutNamesOf (contractErrors ++ visibleSourceErrors)
      libraryErrors
  let errorDecls ←
    mapOption
      ErrorDecl.toCore
      (contractErrors ++ visibleSourceErrors ++ extraLibraryErrors)
  -- QUALIFIED-COLLISION (#136): type-qualified reverts `revert X.E(...)` lower to
  -- a `.`-joined lookup key `X.E`; register those keyed entries so a
  -- library-qualified error encodes L's selector even under a name collision
  -- with the contract's own `E`.
  let errorDecls :=
    errorDecls ++ ContractDecls.qualifiedCoreErrorEntries allContracts
  some
    { storageFields :=
        ContractDecl.toCoreStorageFieldsFromSlot false layoutBaseSlot
          storageStateVars ++
          ContractDecl.toCoreStorageFieldsFromSlot true 0 transientStateVars
      immutableFields := immutableFields
      eventDecls := eventDecls
      errorDecls := errorDecls
      functions := functions }

/-- Assemble the constructor-body statements from the per-contract pieces in
    DESCENT order (most-derived first), reproducing solc's legacy control flow
    (`ContractCompiler::appendBaseConstructor` + the constructor `visit`): at
    each level evaluate the immediate base's supplied arguments in the current
    (deriving) contract's frame, recurse into the base, then run the current
    contract's constructor body. Net effect for a chain `D is B is A`:
    base-ctor arguments are evaluated derived->base during descent, and the
    constructor bodies run base->derived. Each contract's `ownArgCore` (its own
    incoming argument bindings) is emitted inside its deriving contract's block,
    so the argument expressions see the deriving contract's frame and the bound
    parameters stay in scope for the base body. -/
def buildNestedConstructorBody
    (pieces :
      List (List CoreBindingDecl × List CoreStmt × List CoreStmt × List CoreStmt)) :
    List CoreStmt :=
  match pieces with
  | [] => []
  | [p] =>
      let (_, _, ownArgCore, bodyStmts) := p
      ownArgCore ++ bodyStmts
  | p :: rest =>
      let (_, _, ownArgCore, bodyStmts) := p
      ownArgCore ++
        [SolidCore.Solidity.Source.Stmt.block (buildNestedConstructorBody rest)] ++
        bodyStmts

def ContractDecl.constructorFunctionFromOrders?
    (allContracts : List ContractDecl)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (storageOrder dispatchOrder : List ContractDecl)
    (targetName : Name) : Option CoreFunctionDef := do
  let allContracts :=
    appendUniqueContracts allContracts
      (appendUniqueContracts storageOrder dispatchOrder)
  let userEnv :=
    let freeEnv := UserTypeEnv.extendDecls [] sourceUserValueTypes
    ContractDecl.userTypeEnvFromContractsInScope
      (ContractDecl.userTypeEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let enumEnv :=
    let freeEnv := EnumEnv.extendDecls [] sourceEnums
    ContractDecl.enumEnvFromContractsInScope
      (ContractDecl.enumEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let allContracts :=
    allContracts.map (ContractDecl.resolveEnums enumEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveEnums enumEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveEnums enumEnv)
  let sourceUsingDecls :=
    sourceUsingDecls.map (UsingDecl.resolveEnums enumEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveEnums enumEnv)
  let sourceEvents :=
    sourceEvents.map (EventDecl.resolveEnums enumEnv)
  let sourceErrors :=
    sourceErrors.map (ErrorDecl.resolveEnums enumEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveEnums enumEnv)
  let structEnv :=
    let freeEnv := StructEnv.extendDecls [] sourceStructs
    ContractDecl.structEnvFromContractsInScope
      (ContractDecl.structEnvWithQualifiedContracts freeEnv allContracts)
      allContracts
  let usingContracts := allContracts
  let usingFreeFunctions :=
    sourceFunctions ++
      concatMapList ContractDecl.directOrdinaryFunctions usingContracts
  let usingSourceDecls := sourceUsingDecls
  let allContracts :=
    allContracts.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let sourceConstants :=
    sourceConstants.map
      (StateVarDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls [])
  let storageOrder :=
    storageOrder.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.expandUsingSurface
        usingContracts usingFreeFunctions usingSourceDecls)
  let constructorUsingDecls := sourceUsingDecls
  let sourceUsingDecls := []
  let structHierarchy := allContracts
  let allContracts :=
    allContracts.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let constructorUsingDecls :=
    constructorUsingDecls.map (UsingDecl.resolveStructs structEnv)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveStructs structEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveStructs structEnv)
  let sourceEvents := sourceEvents.map (EventDecl.resolveStructs structEnv)
  let sourceErrors := sourceErrors.map (ErrorDecl.resolveStructs structEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveStructs structEnv)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.resolveStructsInHierarchy structEnv structHierarchy)
  let postStructUsingContracts := allContracts
  let postStructUsingFreeFunctions :=
    sourceFunctions ++
      concatMapList ContractDecl.directOrdinaryFunctions postStructUsingContracts
  let allContracts :=
    allContracts.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.expandDirectUsingSurface
        postStructUsingContracts postStructUsingFreeFunctions)
  let allContracts := allContracts.map (ContractDecl.resolveUserTypes userEnv)
  let constructorUsingDecls :=
    constructorUsingDecls.map (UsingDecl.resolveUserTypes userEnv)
  let sourceUsingDecls := sourceUsingDecls.map (UsingDecl.resolveUserTypes userEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveUserTypes userEnv)
  let sourceEvents := sourceEvents.map (EventDecl.resolveUserTypes userEnv)
  let sourceErrors := sourceErrors.map (ErrorDecl.resolveUserTypes userEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveUserTypes userEnv)
  let storageOrder := storageOrder.map (ContractDecl.resolveUserTypes userEnv)
  let dispatchOrder := dispatchOrder.map (ContractDecl.resolveUserTypes userEnv)
  let interfaceIdEnv ← ContractDecls.interfaceIdEnv allContracts
  let allContracts := allContracts.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceFunctions := sourceFunctions.map (FunctionDecl.resolveInterfaceIds interfaceIdEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveInterfaceIds interfaceIdEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveInterfaceIds interfaceIdEnv)
  -- QUALIFIED-COLLISION (#136/#137): rewrite AMBIGUOUS type-qualified emit/
  -- revert/require callees to `.`-joined `qualifiedConstantKey` names so a
  -- library member whose bare name collides with a differently-signed contract
  -- member resolves to the correct selector/topic0 (the runtime table carries
  -- matching qualified entries). Non-ambiguous qualified callees stay bare, so
  -- base-/self-qualified emits/reverts (which solc forbids from shadowing an
  -- inherited name, hence never ambiguous) are byte-identical.
  let collidingEvents :=
    EventDecls.collidingNames
      (concatMapList ContractDecl.directEvents dispatchOrder ++ sourceEvents ++
        concatMapList ContractDecl.directEvents
          (allContracts.filter
            (fun d => ContractDecl.isLibrary d || ContractDecl.isInterface d)))
  let collidingErrors :=
    ErrorDecls.collidingNames
      (concatMapList ContractDecl.directErrors dispatchOrder ++ sourceErrors ++
        concatMapList ContractDecl.directErrors
          (allContracts.filter ContractDecl.isLibrary))
  let allContracts :=
    allContracts.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let sourceFunctions :=
    sourceFunctions.map
      (FunctionDecl.qualifyCollidingEventErrors collidingEvents collidingErrors)
  let stateVars := concatMapList ContractDecl.directStateVars storageOrder
  if !namesUnique (sourceConstants.map StateVarDecl.name) then
    none
  else
    some ()
  if !StateVars.allConstants sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits sourceConstants then
    none
  else
    some ()
  if !StateVars.constantsHaveInits stateVars then
    none
  else
    some ()
  let allContractFunctions :=
    concatMapList ContractDecl.directOrdinaryFunctions allContracts
  let allContractErrors := concatMapList ContractDecl.directErrors allContracts
  let allContractStateVars :=
    concatMapList ContractDecl.directStateVars allContracts
  let qualifiedSelectorEnv :=
    concatMapList
      (fun decl =>
        -- BUG#6: `L.f.selector` on a LIBRARY function is the
        -- library-qualified selector (`isOff(Lib.Mode)`), not the
        -- external-ABI one. Contract entries are unchanged.
        if decl.kind == ContractKind.library then
          FunctionDecls.libraryQualifiedSelectorEntries structEnv decl.name
            (ContractDecl.directOrdinaryFunctions decl)
        else
          FunctionDecls.qualifiedSelectorEntries decl.name
            (ContractDecl.directOrdinaryFunctions decl))
      allContracts
  -- ERROR-SELECTOR-COLLISION (#139): qualified `Contract.Bad` keys over ALL
  -- contracts/libraries, so a type-qualified `L.Bad.selector` / `Base.Bad.selector`
  -- resolves to the declaring scope's selector even under a same-name collision
  -- (mirrors the qualified FUNCTION/EVENT selector entries).
  let qualifiedErrorSelectorEnv :=
    concatMapList
      (fun decl =>
        ErrorDecls.qualifiedSelectorEntries decl.name
          (ContractDecl.directErrors decl))
      allContracts
  -- The bare `Bad.selector` scope is PER-CONTRACT: solc resolves it against the
  -- errors visible to the enclosing contract (own + inherited + unshadowed
  -- file-level), exactly as the type-checker does via `ErrorSigs.resolveByName
  -- env.errors`. `dispatchOrder` is the target contract's linearization, so its
  -- direct errors ARE the target's own+inherited errors; within a single
  -- linearization solc forbids redeclaring an inherited error name, so these
  -- never self-collide. A same-name error in a SIBLING contract no longer
  -- poisons the bare name for the target.
  let targetContractErrors := concatMapList ContractDecl.directErrors dispatchOrder
  let targetVisibleSourceErrors :=
    ErrorDecls.withoutNamesOf targetContractErrors sourceErrors
  let selectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (sourceErrors ++ allContractErrors) ++
    StateVarDecls.selectorEntries allContractStateVars
  -- Bare-selector env for the TARGET contract's own code (dispatch/storage
  -- orders): only the target's visible errors, plus qualified keys and the
  -- function selectors.
  let targetUnqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (targetContractErrors ++ targetVisibleSourceErrors)
  -- Bare-selector env for FREE functions/constants: file-level errors only
  -- (free functions cannot see any contract's errors).
  let freeUnqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries sourceErrors
  -- Global fallback env for LIBRARY/other contracts pulled from `allContracts`
  -- (e.g. inlined library helpers): keep the historical whole-program error
  -- table so a library helper's own error `.selector` still resolves.
  let unqualifiedSelectorEnv :=
    qualifiedSelectorEnv ++ qualifiedErrorSelectorEnv ++
    FunctionDecls.selectorEntries
      (sourceFunctions ++ allContractFunctions) ++
    ErrorDecls.selectorEntries
      (sourceErrors ++ allContractErrors)
  let eventSelectorEnv :=
    let contractEvents := concatMapList ContractDecl.directEvents dispatchOrder
    let visibleSourceEvents :=
      EventDecls.withoutNamesOf contractEvents sourceEvents
    -- QUALIFIED EVENT SELECTOR (#137 `.selector`): qualified `Contract.Ev` keys
    -- over ALL contracts/libraries (so `Base.Ev.selector` / `L.Ping.selector`
    -- resolve to the declaring scope's topic0 under a collision), plus the bare
    -- own/inherited entries for `Ev.selector`.
    concatMapList
      (fun decl =>
        EventDecls.qualifiedSelectorEntries decl.name
          (ContractDecl.directEvents decl))
      allContracts ++
    EventDecls.selectorEntries (contractEvents ++ visibleSourceEvents)
  let functionAddressEnv :=
    FunctionDecls.selectorEntries
      (sourceFunctions ++ concatMapList ContractDecl.directOrdinaryFunctions dispatchOrder) ++
    StateVarDecls.selectorEntries stateVars
  let allContracts :=
    allContracts.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveFunctionAddresses functionAddressEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveFunctionAddresses functionAddressEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveFunctionAddresses functionAddressEnv)
  let allContracts :=
    allContracts.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv unqualifiedSelectorEnv)
  let sourceFunctions :=
    sourceFunctions.map
      (FunctionDecl.resolveSelectorsWithUnqualified
        selectorEnv freeUnqualifiedSelectorEnv)
  let sourceConstants :=
    sourceConstants.map
      (StateVarDecl.resolveSelectorsWithUnqualified
        selectorEnv freeUnqualifiedSelectorEnv)
  let storageOrder :=
    storageOrder.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv targetUnqualifiedSelectorEnv)
  let dispatchOrder :=
    dispatchOrder.map
      (ContractDecl.resolveSelectorsWithUnqualified
        selectorEnv targetUnqualifiedSelectorEnv)
  let allContracts :=
    allContracts.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.resolveEventSelectors eventSelectorEnv)
  let sourceConstants :=
    sourceConstants.map (StateVarDecl.resolveEventSelectors eventSelectorEnv)
  let storageOrder :=
    storageOrder.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let dispatchOrder :=
    dispatchOrder.map (ContractDecl.resolveEventSelectors eventSelectorEnv)
  let scopedStateVars := ContractDecls.scopedStateVars storageOrder
  let duplicateStateNames :=
    duplicateNames
      ((scopedStateVars.filter
        (fun scopedVar => !StateVarDecl.isConstant scopedVar.decl)).map
          (fun scopedVar => scopedVar.decl.name))
  let storageOrder :=
    ContractDecls.rewriteStateAliases
      duplicateStateNames scopedStateVars storageOrder
  let dispatchOrder :=
    ContractDecls.rewriteStateAliases
      duplicateStateNames scopedStateVars dispatchOrder
  let stateVars :=
    ScopedStateVarDecls.coreDecls duplicateStateNames scopedStateVars
  let sourceConstantEnv := StateVars.constantEnv sourceConstants
  let constants :=
    StateVars.constantEnv stateVars ++ sourceConstantEnv ++
      ContractDecls.qualifiedConstantEntries allContracts
  let storageStateVars := stateVars.filter StateVarDecl.isStorageBacked
  let transientStateVars := stateVars.filter StateVarDecl.isTransient
  let immutableStateVars := stateVars.filter StateVarDecl.isImmutable
  let storageAliases :=
    ScopedStateVarDecls.runtimeNameAliasEntries
      duplicateStateNames scopedStateVars
  let storageNames :=
    storageAliases ++
      stateNamesFrom (storageStateVars ++ transientStateVars) immutableStateVars
  let externalCallKindEnv ← ExternalCallKindEnv.fromContracts? allContracts
  let externalCallKindTypeEnv ← ExternalCallKindEnv.toTypeEnv? externalCallKindEnv
  let stateEnv := StateVars.extendTypeEnv externalCallKindTypeEnv stateVars
  -- Per-contract constant scope: each contract's own/inherited constants (C3,
  -- most-derived-first) shadow the shared file-level + qualified tail, but a
  -- derived contract's constant never leaks into a base contract's function
  -- body. The `dispatchOrder` (the target's C3 linearization) is closed under
  -- bases, so it is a sufficient universe to re-derive each contract's own
  -- linearization for scoping.
  let sharedConstantTail :=
    sourceConstantEnv ++ ContractDecls.qualifiedConstantEntries allContracts
  let modifiers :=
    concatMapList
      (fun decl =>
        (ContractDecl.directModifiersStamped decl).map
          (ModifierDecl.inlineConstants
            (ContractDecl.scopedConstantEnv dispatchOrder
              sharedConstantTail decl)))
      dispatchOrder
  let baseNames := dispatchOrder.map ContractDecl.name
  let ordinaryFunctions :=
    ContractDecls.contextualOrdinaryFunctions dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let libraryHelpers :=
    ContractDecl.libraryHelperFunctions sourceConstantEnv allContracts
  let baseHelpers :=
    ContractDecls.contextualBaseHelpers dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let superHelpers ←
    ContractDecls.contextualSuperHelpers? dispatchOrder sharedConstantTail
      baseNames dispatchOrder
  let sourceFunctions :=
    sourceFunctions.map (FunctionDecl.inlineConstants sourceConstantEnv)
  let availableFunctions :=
    ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers
  -- Internal-dispatch numbering, computed IDENTICALLY to `toCoreFromOrders?`
  -- (same candidate set, same ordinary/modifier/constructor scan) so the IDs
  -- the constructor writes into storage agree with the dispatch-table stamps
  -- (boundary-completion arc, ctor/modifier residue).
  let fnIdCandidates :=
    ((availableFunctions ++ sourceFunctions).filterMap FunctionDecl.name).filter
      (fun n => !storageNames.contains n)
  let constructorDecls : List FunctionDecl :=
    concatMapList ContractDecl.directConstructors dispatchOrder
  let internalFnIds :=
    FunctionDecls.internalFnValueNumberingFull fnIdCandidates ordinaryFunctions
      modifiers constructorDecls
  let contractEvents := concatMapList ContractDecl.directEvents dispatchOrder
  let visibleSourceEvents := EventDecls.withoutNamesOf contractEvents sourceEvents
  let contractErrors := concatMapList ContractDecl.directErrors dispatchOrder
  let visibleSourceErrors := ErrorDecls.withoutNamesOf contractErrors sourceErrors
  let eventArgEnv :=
    EventDecls.namedArgEnv (contractEvents ++ visibleSourceEvents)
  let eventIndexedEnv :=
    EventDecls.indexedEnv (contractEvents ++ visibleSourceEvents)
  let errorArgEnv :=
    ErrorDecls.namedArgEnv (contractErrors ++ visibleSourceErrors)
  let targetDecl ← ContractDecl.findByName? dispatchOrder targetName
  let payable ← ContractDecl.constructorPayable? targetDecl
  let constructorParams ←
    match ContractDecl.directConstructors targetDecl with
    | [] => some []
    | [ctor] => some ctor.params
    | _ => none
  -- Constructor reference-type parameters are always `memory` (solc forbids
  -- `calldata` for constructor params), so they are ABI-decoded into memory
  -- with eager per-element validation: mark `memory`-location params
  -- `memoryEager` exactly as for regular function parameters.
  let paramAbiCleanups ←
    mapOption
      (fun (param : Parameter) =>
        if param.location == some DataLocation.storage then
          some SolidCore.Solidity.Source.AbiCleanup.none
        else do
          let cleanup ←
            Ty.toCoreAbiCleanup? (Ty.resolveStructs structEnv param.ty)
          if param.location == some DataLocation.memory then
            some (SolidCore.Solidity.Source.AbiCleanup.memoryEager cleanup)
          else
            some cleanup)
      constructorParams
  let pieces ←
    mapOption
      (fun decl => do
        let baseArgsAndUsing ←
          if decl.name == targetName then
            some ([], constructorUsingDecls, ([] : List Parameter))
          else
            let (baseArgs, supplier) ←
              ContractDecl.baseConstructorArgsAndSupplier?
                storageOrder decl
            let baseArgUsingDecls :=
              ContractDecl.directUsingDecls supplier ++ constructorUsingDecls
            -- Args flow in the supplying contract's frame (the contract that
            -- actually declares this base's constructor arguments — either the
            -- direct inheritor via an inheritance specifier, or any derived
            -- contract via a constructor modifier), so its constructor params
            -- are the ones in scope while evaluating them.
            let supplyingParams :=
              match ContractDecl.directConstructors supplier with
              | [ctor] => ctor.params
              | _ => []
            some (baseArgs, baseArgUsingDecls, supplyingParams)
        let (baseArgs, baseArgUsingDecls, supplyingParams) := baseArgsAndUsing
        ContractDecl.constructorBodyForDeployment?
          allContracts sourceUsingDecls baseArgUsingDecls storageNames
          constants stateEnv externalCallKindEnv modifiers availableFunctions
          sourceFunctions eventArgEnv errorArgEnv internalFnIds eventIndexedEnv
          (contractEvents ++ visibleSourceEvents)
          targetName supplyingParams baseArgs decl)
      storageOrder
  -- `pieces` are in storage order (base->derived). Reproduce solc's LEGACY
  -- constructor lowering (`ContractCompiler::appendInitAndConstructorCode`):
  --   (1) run ALL state-variable initializers, whole hierarchy, base->derived,
  --       BEFORE any constructor body;
  --   (2) then the constructor bodies, base->derived, with each base's
  --       arguments evaluated in the supplying (more-derived) contract's frame
  --       during the derived->base descent (see `buildNestedConstructorBody`).
  let params := concatLists (pieces.map (fun p => p.1))
  let allInits := concatLists (pieces.map (fun p => p.2.1))
  let bodyStmts := buildNestedConstructorBody pieces.reverse
  let stmts := allInits ++ bodyStmts
  some
    { name := "__constructor"
      selector? := none
      payable := payable
      params := params
      paramAbiCleanups := paramAbiCleanups
      returns := []
      -- R3 (#192) endgame: the same single storage value-use normalization
      -- pass ordinary function bodies get, over the whole assembled
      -- constructor (state-var initializers + base->derived ctor bodies).
      body :=
        SolidCore.Solidity.Source.Stmt.normalizeStorageValueUses
          (SolidCore.Solidity.Source.Stmt.block stmts) }

def ContractDecl.toCore? (decl : ContractDecl) : Option CoreContract :=
  ContractDecl.toCoreFromOrders? [decl] [] [] [] [] [] [] [] [] [decl] [decl]

def ContractDecl.toCoreWithBasesAndUsing? (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl) (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreContract := do
  let storageOrder ← ContractDecl.storageOrder? contracts decl
  let dispatchOrder ← ContractDecl.dispatchOrder? contracts decl
  ContractDecl.toCoreFromOrders?
    contracts sourceUsingDecls sourceFunctions sourceEvents sourceErrors
    sourceConstants sourceUserValueTypes sourceEnums sourceStructs
    storageOrder dispatchOrder

def ContractDecl.toCoreWithBases? (contracts : List ContractDecl)
    (decl : ContractDecl) : Option CoreContract := do
  ContractDecl.toCoreWithBasesAndUsing? [] [] [] [] [] [] [] [] contracts decl

def ContractDecl.constructorFunctionWithBasesAndSource?
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreFunctionDef := do
  let storageOrder ← ContractDecl.storageOrder? contracts decl
  let dispatchOrder ← ContractDecl.dispatchOrder? contracts decl
  ContractDecl.constructorFunctionFromOrders?
    contracts sourceUsingDecls sourceFunctions sourceEvents sourceErrors
    sourceConstants sourceUserValueTypes sourceEnums sourceStructs
    storageOrder dispatchOrder decl.name

def ContractDecl.constructorFunctionWithBases?
    (contracts : List ContractDecl) (decl : ContractDecl) :
    Option CoreFunctionDef :=
  ContractDecl.constructorFunctionWithBasesAndSource? [] [] [] [] [] [] [] []
    contracts decl

def ContractDecl.constructWithBasesAndSourceAtFrom? (fuel : Nat)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (self sender value : Word)
    (args : List CoreValue) :
    Option CoreCallResult := do
  let contract ←
    ContractDecl.toCoreWithBasesAndUsing?
      sourceUsingDecls sourceFunctions sourceEvents sourceErrors sourceConstants
      sourceUserValueTypes sourceEnums sourceStructs
      contracts decl
  let constructor ←
    ContractDecl.constructorFunctionWithBasesAndSource?
      sourceUsingDecls sourceFunctions sourceEvents sourceErrors
      sourceConstants sourceUserValueTypes sourceEnums sourceStructs contracts decl
  SolidCore.Solidity.Source.FunctionDef.call?
    fuel contract.table
    { contract.context with
      self := self
      sender := sender
      value := value
      construction := true }
    constructor state args

def ContractDecl.constructWithBasesAndSourceFrom? (fuel : Nat)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  ContractDecl.constructWithBasesAndSourceAtFrom? fuel
    sourceUsingDecls sourceFunctions sourceEvents sourceErrors
    sourceConstants sourceUserValueTypes sourceEnums sourceStructs
    contracts decl state 0 sender value args

def ContractDecl.constructWithBasesFrom? (fuel : Nat)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  ContractDecl.constructWithBasesAndSourceFrom?
    fuel [] [] [] [] [] [] [] [] contracts decl state sender value args

def ContractDecl.constructWithBases? (fuel : Nat)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  ContractDecl.constructWithBasesFrom? fuel contracts decl state 0 0 args

def ContractDecl.constructFrom? (fuel : Nat) (decl : ContractDecl)
    (state : CoreState) (sender value : Word) (args : List CoreValue) :
    Option CoreCallResult :=
  ContractDecl.constructWithBasesFrom? fuel [decl] decl state sender value args

def ContractDecl.construct? (fuel : Nat) (decl : ContractDecl)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult :=
  ContractDecl.constructWithBases? fuel [decl] decl state args

def SourceUnit.freeUserValueTypes (unit : SourceUnit) :
    List UserValueTypeDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeUserValueType decl => some decl
    | _ => none)

def SourceUnit.freeEnums (unit : SourceUnit) : List EnumDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeEnum decl => some decl
    | _ => none)

def SourceUnit.freeStructs (unit : SourceUnit) : List StructDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeStruct decl => some decl
    | _ => none)

def SourceUnit.freeFunctions (unit : SourceUnit) : List FunctionDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeFunction decl => some decl
    | _ => none)

def SourceUnit.freeEvents (unit : SourceUnit) : List EventDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeEvent decl => some decl
    | _ => none)

def SourceUnit.freeErrors (unit : SourceUnit) : List ErrorDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeError decl => some decl
    | _ => none)

def SourceUnit.freeConstants (unit : SourceUnit) : List StateVarDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.freeConstant decl => some decl
    | _ => none)

def SourceUnit.contracts (unit : SourceUnit) : List ContractDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.contract decl => some decl
    | _ => none)

def SourceUnit.userTypeEnv (unit : SourceUnit) : UserTypeEnv :=
  let freeEnv :=
    UserTypeEnv.extendDecls [] (SourceUnit.freeUserValueTypes unit)
  ContractDecl.userTypeEnvFromContractsInScope
    (ContractDecl.userTypeEnvWithQualifiedContracts freeEnv
      (SourceUnit.contracts unit))
    (SourceUnit.contracts unit)

def SourceUnit.resolveUserTypes (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.userTypeEnv unit
  { unit with items := unit.items.map (SourceItem.resolveUserTypes env) }

def SourceUnit.enumEnv (unit : SourceUnit) : EnumEnv :=
  let freeEnv := EnumEnv.extendDecls [] (SourceUnit.freeEnums unit)
  ContractDecl.enumEnvFromContractsInScope
    (ContractDecl.enumEnvWithQualifiedContracts freeEnv
      (SourceUnit.contracts unit))
    (SourceUnit.contracts unit)

def SourceUnit.resolveEnums (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.enumEnv unit
  { unit with items := unit.items.map (SourceItem.resolveEnums env) }

def SourceUnit.structEnv (unit : SourceUnit) : StructEnv :=
  let freeEnv := StructEnv.extendDecls [] (SourceUnit.freeStructs unit)
  ContractDecl.structEnvFromContractsInScope
    (ContractDecl.structEnvWithQualifiedContracts freeEnv
      (SourceUnit.contracts unit))
    (SourceUnit.contracts unit)

def SourceUnit.resolveStructs (unit : SourceUnit) : SourceUnit :=
  let env := SourceUnit.structEnv unit
  let contracts := SourceUnit.contracts unit
  { unit with
    items :=
      unit.items.map (fun item =>
        match item with
        | SourceItem.contract decl =>
            SourceItem.contract
              (ContractDecl.resolveStructsInHierarchy env contracts decl)
        | other => SourceItem.resolveStructs env other) }

def SourceUnit.resolveSourceTypes (unit : SourceUnit) : SourceUnit :=
  SourceUnit.resolveStructs
    (SourceUnit.resolveEnums (SourceUnit.resolveUserTypes unit))

def SourceUnit.sourceUserTypeEnv (unit : SourceUnit) : UserTypeEnv :=
  ContractDecl.userTypeEnvWithQualifiedContracts
    (UserTypeEnv.extendDecls [] (SourceUnit.freeUserValueTypes unit))
    (SourceUnit.contracts unit)

def SourceUnit.sourceEnumEnv (unit : SourceUnit) : EnumEnv :=
  ContractDecl.enumEnvWithQualifiedContracts
    (EnumEnv.extendDecls [] (SourceUnit.freeEnums unit))
    (SourceUnit.contracts unit)

def SourceUnit.sourceStructEnv (unit : SourceUnit) : StructEnv :=
  ContractDecl.structEnvWithQualifiedContracts
    (StructEnv.extendDecls [] (SourceUnit.freeStructs unit))
    (SourceUnit.contracts unit)

def SourceUnit.userTypeEnvForOrder (unit : SourceUnit)
    (order : List ContractDecl) : UserTypeEnv :=
  ContractDecl.userTypeEnvFromContractsInScope
    (SourceUnit.sourceUserTypeEnv unit) order

def SourceUnit.enumEnvForOrder (unit : SourceUnit)
    (order : List ContractDecl) : EnumEnv :=
  ContractDecl.enumEnvFromContractsInScope
    (SourceUnit.sourceEnumEnv unit) order

def SourceUnit.structEnvForOrder (unit : SourceUnit)
    (order : List ContractDecl) : StructEnv :=
  ContractDecl.structEnvFromContractsInScope
    (SourceUnit.sourceStructEnv unit) order

def ContractDecl.resolveSourceTypesWithInherited
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (inheritedVars : List StateVarDecl) (decl : ContractDecl) :
    ContractDecl :=
  ContractDecl.resolveStructsWithInheritedVars structEnv inheritedVars
    (ContractDecl.resolveEnums enumEnv
      (ContractDecl.resolveUserTypes userEnv decl))

def ContractDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : ContractDecl) : ContractDecl :=
  ContractDecl.resolveSourceTypesWithInherited userEnv enumEnv structEnv
    [] decl

def FunctionDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : FunctionDecl) : FunctionDecl :=
  FunctionDecl.resolveStructs structEnv
    (FunctionDecl.resolveEnums enumEnv
      (FunctionDecl.resolveUserTypes userEnv decl))

def StateVarDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : StateVarDecl) : StateVarDecl :=
  StateVarDecl.resolveStructs structEnv
    (StateVarDecl.resolveEnums enumEnv
      (StateVarDecl.resolveUserTypes userEnv decl))

def EventDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : EventDecl) : EventDecl :=
  EventDecl.resolveStructs structEnv
    (EventDecl.resolveEnums enumEnv
      (EventDecl.resolveUserTypes userEnv decl))

def ErrorDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : ErrorDecl) : ErrorDecl :=
  ErrorDecl.resolveStructs structEnv
    (ErrorDecl.resolveEnums enumEnv
      (ErrorDecl.resolveUserTypes userEnv decl))

def StructDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : StructDecl) : StructDecl :=
  StructDecl.resolveStructs structEnv
    (StructDecl.resolveEnums enumEnv
      (StructDecl.resolveUserTypes userEnv decl))

def UserValueTypeDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (decl : UserValueTypeDecl) :
    UserValueTypeDecl :=
  UserValueTypeDecl.resolveUserTypes userEnv decl

def UsingDecl.resolveSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv)
    (decl : UsingDecl) : UsingDecl :=
  UsingDecl.resolveStructs structEnv
    (UsingDecl.resolveEnums enumEnv
      (UsingDecl.resolveUserTypes userEnv decl))

def SourceItem.resolveFreeSourceTypesWith
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv) :
    SourceItem -> SourceItem
  | SourceItem.pragma name version => SourceItem.pragma name version
  | SourceItem.importPath path alias? => SourceItem.importPath path alias?
  | SourceItem.contract decl => SourceItem.contract decl
  | SourceItem.freeFunction decl =>
      SourceItem.freeFunction
        (FunctionDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)
  | SourceItem.freeConstant decl =>
      SourceItem.freeConstant
        (StateVarDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)
  | SourceItem.freeEvent decl =>
      SourceItem.freeEvent
        (EventDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)
  | SourceItem.freeError decl =>
      SourceItem.freeError
        (ErrorDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)
  | SourceItem.freeStruct decl =>
      SourceItem.freeStruct
        (StructDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)
  | SourceItem.freeEnum decl => SourceItem.freeEnum decl
  | SourceItem.freeUserValueType decl =>
      SourceItem.freeUserValueType
        (UserValueTypeDecl.resolveSourceTypesWith userEnv decl)
  | SourceItem.usingDecl decl =>
      SourceItem.usingDecl
        (UsingDecl.resolveSourceTypesWith userEnv enumEnv structEnv decl)

def SourceUnit.resolveContractSourceTypes? (unit : SourceUnit)
    (decl : ContractDecl) : Option ContractDecl := do
  let order ← ContractDecl.dispatchOrder? (SourceUnit.contracts unit) decl
  let userEnv := SourceUnit.userTypeEnvForOrder unit order
  let enumEnv := SourceUnit.enumEnvForOrder unit order
  let structEnv := SourceUnit.structEnvForOrder unit order
  -- #197: seed the member-rewrite typeEnv with INHERITED state variables,
  -- pre-resolved through the same user-type/enum passes the contract's own
  -- declarations receive before `resolveStructs` runs on them.
  let inheritedVars :=
    (ContractDecl.inheritedStateVarsOfOrder order).map
      (fun stateVar =>
        StateVarDecl.resolveEnums enumEnv
          (StateVarDecl.resolveUserTypes userEnv stateVar))
  some
    (ContractDecl.resolveSourceTypesWithInherited userEnv enumEnv structEnv
      inheritedVars decl)

def SourceUnit.resolveSourceItemContextual? (unit : SourceUnit)
    (userEnv : UserTypeEnv) (enumEnv : EnumEnv) (structEnv : StructEnv) :
    SourceItem -> Option SourceItem
  | SourceItem.contract decl => do
      let decl ← SourceUnit.resolveContractSourceTypes? unit decl
      some (SourceItem.contract decl)
  | item => some (SourceItem.resolveFreeSourceTypesWith userEnv enumEnv structEnv item)

def SourceUnit.resolveSourceTypesContextual? (unit : SourceUnit) :
    Option SourceUnit := do
  let userEnv := SourceUnit.sourceUserTypeEnv unit
  let enumEnv := SourceUnit.sourceEnumEnv unit
  let structEnv := SourceUnit.sourceStructEnv unit
  let items ←
    mapOption
      (SourceUnit.resolveSourceItemContextual? unit userEnv enumEnv structEnv)
      unit.items
  some { unit with items := items }

def SourceUnit.usingDecls (unit : SourceUnit) : List UsingDecl :=
  unit.items.filterMap (fun item =>
    match item with
    | SourceItem.usingDecl usingDecl => some usingDecl
    | _ => none)

def SourceUnit.findContract? (unit : SourceUnit)
    (name : Name) : Option ContractDecl :=
  ContractDecl.findByName? (SourceUnit.contracts unit) name

def SourceUnit.toCoreContract? (unit : SourceUnit)
    (name : Name) : Option CoreContract := do
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.toCoreWithBasesAndUsing?
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
    (SourceUnit.freeConstants unit)
    (SourceUnit.freeUserValueTypes unit)
    (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
    (SourceUnit.contracts unit) decl

def SourceUnit.constructContract? (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option CoreCallResult := do
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructWithBasesAndSourceFrom? fuel
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
    (SourceUnit.freeConstants unit)
    (SourceUnit.freeUserValueTypes unit)
    (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
    (SourceUnit.contracts unit) decl state 0 0 args

def SourceUnit.constructContractAtFrom? (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (self sender value : Word)
    (args : List CoreValue) : Option CoreCallResult := do
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructWithBasesAndSourceAtFrom? fuel
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
    (SourceUnit.freeConstants unit)
    (SourceUnit.freeUserValueTypes unit)
    (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
    (SourceUnit.contracts unit) decl state self sender value args

def SourceUnit.constructContractFrom? (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) : Option CoreCallResult :=
  SourceUnit.constructContractAtFrom? fuel unit name state 0 sender value args

/-- Stage 1e — tree-returning twin of `constructWithBasesAndSourceAtFrom?`. -/
def ContractDecl.constructWithBasesAndSourceAtFromTree (fuel : Nat)
    (sourceUsingDecls : List UsingDecl)
    (sourceFunctions : List FunctionDecl)
    (sourceEvents : List EventDecl)
    (sourceErrors : List ErrorDecl)
    (sourceConstants : List StateVarDecl)
    (sourceUserValueTypes : List UserValueTypeDecl)
    (sourceEnums : List EnumDecl) (sourceStructs : List StructDecl)
    (contracts : List ContractDecl) (decl : ContractDecl)
    (state : CoreState) (self sender value : Word)
    (args : List CoreValue) :
    Option (SolidCore.Solidity.Source.SolI CoreCallResult) := do
  let contract ←
    ContractDecl.toCoreWithBasesAndUsing?
      sourceUsingDecls sourceFunctions sourceEvents sourceErrors sourceConstants
      sourceUserValueTypes sourceEnums sourceStructs
      contracts decl
  let constructor ←
    ContractDecl.constructorFunctionWithBasesAndSource?
      sourceUsingDecls sourceFunctions sourceEvents sourceErrors
      sourceConstants sourceUserValueTypes sourceEnums sourceStructs contracts decl
  SolidCore.Solidity.Source.FunctionDef.call
    fuel contract.table
    { contract.context with
      self := self
      sender := sender
      value := value
      construction := true }
    constructor state args

def SourceUnit.constructContractAtFromTree (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (self sender value : Word)
    (args : List CoreValue) :
    Option (SolidCore.Solidity.Source.SolI CoreCallResult) := do
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructWithBasesAndSourceAtFromTree fuel
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
    (SourceUnit.freeConstants unit)
    (SourceUnit.freeUserValueTypes unit)
    (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
    (SourceUnit.contracts unit) decl state self sender value args

def SourceUnit.constructContractFromTree (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (sender value : Word)
    (args : List CoreValue) :
    Option (SolidCore.Solidity.Source.SolI CoreCallResult) :=
  SourceUnit.constructContractAtFromTree fuel unit name state 0 sender value args

def SourceUnit.constructContractTree (fuel : Nat) (unit : SourceUnit)
    (name : Name) (state : CoreState) (args : List CoreValue) :
    Option (SolidCore.Solidity.Source.SolI CoreCallResult) :=
  SourceUnit.constructContractAtFromTree fuel unit name state 0 0 0 args

def SourceUnit.constructorFunctionFor? (unit : SourceUnit) (name : Name) :
    Option CoreFunctionDef := do
  let decl ← SourceUnit.findContract? unit name
  ContractDecl.constructorFunctionWithBasesAndSource?
    (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
    (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
    (SourceUnit.freeConstants unit)
    (SourceUnit.freeUserValueTypes unit)
    (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
    (SourceUnit.contracts unit) decl

def SourceUnit.constructorParamTys? (unit : SourceUnit) (name : Name) :
    Option (List CoreTy) := do
  let constructor ← SourceUnit.constructorFunctionFor? unit name
  some (constructor.params.map SolidCore.Solidity.Source.BindingDecl.ty)

def SourceUnit.constructorParamAbiCleanups? (unit : SourceUnit)
    (name : Name) : Option (List CoreAbiCleanup) := do
  let constructor ← SourceUnit.constructorFunctionFor? unit name
  some constructor.paramAbiCleanups

def SourceUnit.toCoreContracts? (unit : SourceUnit) :
    Option (List CoreContract) :=
  match SourceUnit.resolveSourceTypesContextual? unit with
  | some unit =>
      mapOption
        (fun decl =>
          ContractDecl.toCoreWithBasesAndUsing?
            (SourceUnit.usingDecls unit) (SourceUnit.freeFunctions unit)
            (SourceUnit.freeEvents unit) (SourceUnit.freeErrors unit)
            (SourceUnit.freeConstants unit)
            (SourceUnit.freeUserValueTypes unit)
            (SourceUnit.freeEnums unit) (SourceUnit.freeStructs unit)
            (SourceUnit.contracts unit) decl)
        (SourceUnit.contracts unit)
  | none => none

def Stmt.eval? (fuel : Nat) (storageNames : List Name)
    (context : CoreContext) (runtime : CoreRuntime) (stmt : Stmt)
    (table : SolidCore.Solidity.Source.FunctionTable := []) :
    Option CoreResult := do
  let coreStmt ← Stmt.toCore? storageNames stmt
  -- Frozen `?`-adapter: fold the interaction tree **fail-closed** under an empty
  -- responder (phase 5 / phase 6 item 7). No query is emitted on this path, so
  -- this is behaviour-identical to the old `SolI.run context` fold; the point is
  -- that a future external call routed through here fails loudly (unmatched →
  -- `none`) rather than fail-open.
  (SolidCore.Solidity.Source.SolI.runWith []
    (SolidCore.Solidity.Source.Stmt.eval fuel table context runtime coreStmt)).toOption

def FunctionDecl.call? (fuel : Nat) (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (context : CoreContext) (state : CoreState) (decl : FunctionDecl)
    (args : List CoreValue) : Option CoreCallResult := do
  let function ←
    FunctionDecl.toCore?
      (storageNames := storageNames)
      (constants := [])
      (extraEnv := [])
      (contracts := [])
      (usingDecls := [])
      (modifiers := modifiers)
      (functions := [decl])
      (freeFunctions := [])
      (decl := decl)
  SolidCore.Solidity.Source.FunctionDef.call? fuel [function.toInternal] context function state args

/-- Witness adapter twin of `Stmt.eval?`: fold under a fail-open responder. -/
def Stmt.evalFailOpen? (fuel : Nat)
    (responder : SolidCore.Solidity.Source.ScriptedResponder)
    (storageNames : List Name)
    (context : CoreContext) (runtime : CoreRuntime) (stmt : Stmt)
    (table : SolidCore.Solidity.Source.FunctionTable := []) :
    Option CoreResult := do
  let coreStmt ← Stmt.toCore? storageNames stmt
  (SolidCore.Solidity.Source.SolI.runFailOpen responder
    (SolidCore.Solidity.Source.Stmt.eval fuel table context runtime coreStmt)).toOption

/-- Witness adapter twin of `FunctionDecl.call?`: fold under a fail-open
    responder. -/
def FunctionDecl.callFailOpen? (fuel : Nat)
    (responder : SolidCore.Solidity.Source.ScriptedResponder)
    (storageNames : List Name)
    (modifiers : List SourceModifierDecl)
    (context : CoreContext) (state : CoreState) (decl : FunctionDecl)
    (args : List CoreValue) : Option CoreCallResult := do
  let function ←
    FunctionDecl.toCore?
      (storageNames := storageNames)
      (constants := [])
      (extraEnv := [])
      (contracts := [])
      (usingDecls := [])
      (modifiers := modifiers)
      (functions := [decl])
      (freeFunctions := [])
      (decl := decl)
  SolidCore.Solidity.Source.FunctionDef.callFailOpen?
    fuel responder context function state args [function.toInternal]

def ContractDecl.call? (fuel : Nat) (decl : ContractDecl)
    (target : SolidCore.Solidity.Source.CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← ContractDecl.toCore? decl
  SolidCore.Solidity.Source.Contract.call? fuel contract target state args

def ContractDecl.callTransaction? (fuel : Nat) (decl : ContractDecl)
    (target : SolidCore.Solidity.Source.CallTarget) (state : CoreState)
    (args : List CoreValue) : Option CoreCallResult := do
  let contract ← ContractDecl.toCore? decl
  SolidCore.Solidity.Source.Contract.callTransaction?
    fuel contract target state args

def SourceUnit.callContract? (fuel : Nat) (unit : SourceUnit)
    (contractName : Name) (target : SolidCore.Solidity.Source.CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← SourceUnit.toCoreContract? unit contractName
  SolidCore.Solidity.Source.Contract.call? fuel contract target state args

def SourceUnit.callContractTransaction? (fuel : Nat) (unit : SourceUnit)
    (contractName : Name) (target : SolidCore.Solidity.Source.CallTarget)
    (state : CoreState) (args : List CoreValue) : Option CoreCallResult := do
  let contract ← SourceUnit.toCoreContract? unit contractName
  SolidCore.Solidity.Source.Contract.callTransaction?
    fuel contract target state args

def CoreValue.asWord? (value : CoreValue) : Option Word :=
  SolidCore.Solidity.Source.Value.asWord? value

def CoreValue.asLowLevelReturn? (value : CoreValue) :
    Option (Word × List Byte) :=
  match value with
  | SolidCore.Solidity.Source.Value.tuple values =>
      match values with
      | successValue :: outputValue :: [] =>
          match successValue, outputValue with
          | SolidCore.Solidity.Source.Value.word success,
              SolidCore.Solidity.Source.Value.bytes output =>
              some (success, output)
          | _, _ => none
      | _ => none
  | _ => none

def CoreValue.asWordPair? (value : CoreValue) : Option (Word × Word) :=
  match value with
  | SolidCore.Solidity.Source.Value.tuple values =>
      match values with
      | xValue :: yValue :: [] =>
          match xValue, yValue with
          | SolidCore.Solidity.Source.Value.word x,
              SolidCore.Solidity.Source.Value.word y =>
              some (x, y)
          | _, _ => none
      | _ => none
  | _ => none

def CoreExpr.evalWord? (context : CoreContext) (runtime : CoreRuntime)
    (expr : CoreExpr) : Option Word :=
  match SolidCore.Solidity.Source.Expr.evalWithRuntimeByContext expr context runtime with
  | Except.ok (value, _) => CoreValue.asWord? value
  | Except.error _ => none

def CoreExpr.evalWordInEmptyContext? (expr : CoreExpr) : Option Word :=
  CoreExpr.evalWord?
    SolidCore.Solidity.Source.Context.empty
    (SolidCore.Solidity.Source.Runtime.ofState
      SolidCore.Solidity.Source.State.empty)
    expr

def CoreCallResult.behavior? : CoreCallResult -> Option Behavior
  | SolidCore.Solidity.Source.CallResult.returned _ [] =>
      some Behavior.stopped
  | SolidCore.Solidity.Source.CallResult.returned _ [value] => do
      let word ← CoreValue.asWord? value
      some (Behavior.returnedWord word)
  | _ => none

def SourceUnit.entryNames? (unit : SourceUnit) :
    Option (Name × Name) :=
  match unit.items with
  | [SourceItem.contract contract] =>
      match contract.items with
      | [ContractItem.function fn] => do
          let functionName ← FunctionDecl.coreName? fn
          some (contract.name, functionName)
      | _ => none
  | _ => none

def SourceUnit.entryCallResult? (fuel : Nat) (unit : SourceUnit) :
    Option CoreCallResult := do
  let (contractName, functionName) ← SourceUnit.entryNames? unit
  SourceUnit.callContract? fuel unit contractName
    (SolidCore.Solidity.Source.CallTarget.name functionName)
    SolidCore.Solidity.Source.State.empty []

def SourceUnit.entryBehavior? (fuel : Nat) (unit : SourceUnit) :
    Option Behavior := do
  let result ← SourceUnit.entryCallResult? fuel unit
  CoreCallResult.behavior? result

def SourceUnit.defaultEntryFuel : Nat := 32

def SourceUnit.defaultEntryBehavior? (unit : SourceUnit) :
    Option Behavior :=
  SourceUnit.entryBehavior? SourceUnit.defaultEntryFuel unit

inductive Semantics : SourceUnit -> Behavior -> Prop where
  | empty {source : SourceUnit} :
      source.items = [] ->
      Semantics source Behavior.stopped
  | entry {source : SourceUnit} {behavior : Behavior} {fuel : Nat} :
      SourceUnit.entryBehavior? fuel source = some behavior ->
      Semantics source behavior



end SolidCore.Solidity.Executable

import SolidCore.Solidity.Interface

namespace SolidCore
namespace Solidity
namespace TypeCheck

abbrev Name := Solidity.Name
abbrev Ty := Solidity.Ty
abbrev Path := Solidity.Path
abbrev TypeEnv := Solidity.Executable.TypeEnv
abbrev SourceUnitAst := Solidity.SourceUnit
abbrev SourceContractDecl := Solidity.ContractDecl
abbrev EvmVersion := SolidCore.Solidity.Source.EvmVersion

namespace EvmVersion

abbrev homestead : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.homestead

abbrev tangerineWhistle : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.tangerineWhistle

abbrev spuriousDragon : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.spuriousDragon

abbrev byzantium : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.byzantium

abbrev constantinople : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.constantinople

abbrev petersburg : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.petersburg

abbrev istanbul : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.istanbul

abbrev berlin : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.berlin

abbrev london : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.london

abbrev paris : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.paris

abbrev shanghai : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.shanghai

abbrev cancun : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.cancun

abbrev prague : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.prague

abbrev osaka : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.osaka

def default : EvmVersion :=
  SolidCore.Solidity.Source.EvmVersion.default

end EvmVersion

structure TypeContext where
  contracts : List Path := []
  contractDecls : List (Path × Solidity.ContractDecl) := []
  structs : List (Path × Solidity.StructDecl) := []
  enums : List (Path × Solidity.EnumDecl) := []
  userValueTypes : List (Path × Ty) := []
  abiCoderV1 : Bool := false
  evmVersion : EvmVersion := EvmVersion.default
  deriving Repr

namespace TypeContext

def empty : TypeContext := {}

def pathOfName (name : Name) : Path :=
  { segments := [name] }

def qualifiedPath (scope name : Name) : Path :=
  { segments := [scope, name] }

def pathMatches (target candidate : Path) : Bool :=
  target == candidate

def pathIn (target : Path) : List Path -> Bool
  | [] => false
  | candidate :: rest =>
      pathMatches target candidate || pathIn target rest

def lookupPath? {α : Type} (target : Path) : List (Path × α) -> Option α
  | [] => none
  | (candidate, value) :: rest =>
      if pathMatches target candidate then
        some value
      else
        lookupPath? target rest

def lookupContract? (ctx : TypeContext) (path : Path) : Option Path :=
  if pathIn path ctx.contracts then some path else none

def lookupStruct? (ctx : TypeContext) (path : Path) :
    Option Solidity.StructDecl :=
  lookupPath? path ctx.structs

def lookupContractDecl? (ctx : TypeContext) (path : Path) :
    Option Solidity.ContractDecl :=
  lookupPath? path ctx.contractDecls

def lookupEnum? (ctx : TypeContext) (path : Path) :
    Option Solidity.EnumDecl :=
  lookupPath? path ctx.enums

def lookupUserValueType? (ctx : TypeContext) (path : Path) :
    Option Ty :=
  lookupPath? path ctx.userValueTypes

def pathIsAdjacentAliasIn {α : Type} (short qualified : Path) :
    List (Path × α) -> Bool
  | [] => false
  | [_] => false
  | (candidate, _) :: tail =>
      match tail with
      | («alias», _) :: _ =>
          (candidate == short && «alias» == qualified) ||
            pathIsAdjacentAliasIn short qualified tail
      | [] => false

def pathsAreLocalAliasIn {α : Type} (entries : List (Path × α))
    (left right : Path) : Bool :=
  match left.segments, right.segments with
  | [_], _ => pathIsAdjacentAliasIn left right entries
  | _, [_] => pathIsAdjacentAliasIn right left entries
  | _, _ => false

def isContractPath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupContract? ctx path with
  | some _ => true
  | none => false

def isLibraryPath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupContractDecl? ctx path with
  | some decl => decl.kind == Solidity.ContractKind.library
  | none => false

def isContractValuePath (ctx : TypeContext) (path : Path) : Bool :=
  isContractPath ctx path && !isLibraryPath ctx path

def isStructPath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupStruct? ctx path with
  | some _ => true
  | none => false

def isEnumPath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupEnum? ctx path with
  | some _ => true
  | none => false

def isUserValueTypePath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupUserValueType? ctx path with
  | some _ => true
  | none => false

def isKnownPath (ctx : TypeContext) (path : Path) : Bool :=
  isContractPath ctx path || isStructPath ctx path ||
    isEnumPath ctx path || isUserValueTypePath ctx path

def contractQualifiedStructEntries (contractName : Name) :
    List Solidity.StructDecl ->
    List (Path × Solidity.StructDecl)
  | [] => []
  | decl :: rest =>
      (qualifiedPath contractName decl.name, decl) ::
        contractQualifiedStructEntries contractName rest

def contractQualifiedEnumEntries (contractName : Name) :
    List Solidity.EnumDecl ->
    List (Path × Solidity.EnumDecl)
  | [] => []
  | decl :: rest =>
      (qualifiedPath contractName decl.name, decl) ::
        contractQualifiedEnumEntries contractName rest

def contractQualifiedUserValueTypeEntries (contractName : Name) :
    List Solidity.UserValueTypeDecl -> List (Path × Ty)
  | [] => []
  | decl :: rest =>
      (qualifiedPath contractName decl.name, decl.underlying) ::
        contractQualifiedUserValueTypeEntries contractName rest

def contractSourceStructEntries :
    List Solidity.ContractDecl ->
    List (Path × Solidity.StructDecl)
  | [] => []
  | contract :: rest =>
      contractQualifiedStructEntries contract.name
        (contract.items.filterMap
          (fun item =>
            match item with
            | Solidity.ContractItem.structDecl decl => some decl
            | _ => none)) ++
        contractSourceStructEntries rest

def contractSourceEnumEntries :
    List Solidity.ContractDecl ->
    List (Path × Solidity.EnumDecl)
  | [] => []
  | contract :: rest =>
      contractQualifiedEnumEntries contract.name
        (contract.items.filterMap
          (fun item =>
            match item with
            | Solidity.ContractItem.enumDecl decl => some decl
            | _ => none)) ++
        contractSourceEnumEntries rest

def contractSourceUserValueTypeEntries :
    List Solidity.ContractDecl -> List (Path × Ty)
  | [] => []
  | contract :: rest =>
      contractQualifiedUserValueTypeEntries contract.name
        (contract.items.filterMap
          (fun item =>
            match item with
            | Solidity.ContractItem.userValueTypeDecl decl =>
                some decl
            | _ => none)) ++
        contractSourceUserValueTypeEntries rest

def withSourceTypes (ctx : TypeContext)
    (contracts : List Solidity.ContractDecl)
    (structs : List Solidity.StructDecl)
    (enums : List Solidity.EnumDecl)
    (userValueTypes : List Solidity.UserValueTypeDecl) :
    TypeContext :=
  { ctx with
    contracts :=
      contracts.map (fun decl => pathOfName decl.name) ++ ctx.contracts
    contractDecls :=
      contracts.map (fun decl => (pathOfName decl.name, decl)) ++
        ctx.contractDecls
    structs :=
      structs.map (fun decl => (pathOfName decl.name, decl)) ++
        contractSourceStructEntries contracts ++ ctx.structs
    enums :=
      enums.map (fun decl => (pathOfName decl.name, decl)) ++
        contractSourceEnumEntries contracts ++ ctx.enums
    userValueTypes :=
      userValueTypes.map
        (fun decl => (pathOfName decl.name, decl.underlying)) ++
        contractSourceUserValueTypeEntries contracts ++
        ctx.userValueTypes }

def contractStructEntries (contractName : Name) :
    List Solidity.StructDecl ->
    List (Path × Solidity.StructDecl)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl) ::
        (qualifiedPath contractName decl.name, decl) ::
        contractStructEntries contractName rest

def contractEnumEntries (contractName : Name) :
    List Solidity.EnumDecl ->
    List (Path × Solidity.EnumDecl)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl) ::
        (qualifiedPath contractName decl.name, decl) ::
        contractEnumEntries contractName rest

def contractUserValueTypeEntries (contractName : Name) :
    List Solidity.UserValueTypeDecl -> List (Path × Ty)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl.underlying) ::
        (qualifiedPath contractName decl.name, decl.underlying) ::
        contractUserValueTypeEntries contractName rest

def withContractTypes (ctx : TypeContext) (contractName : Name)
    (structs : List Solidity.StructDecl)
    (enums : List Solidity.EnumDecl)
    (userValueTypes : List Solidity.UserValueTypeDecl) :
    TypeContext :=
  { ctx with
    structs := contractStructEntries contractName structs ++ ctx.structs
    enums := contractEnumEntries contractName enums ++ ctx.enums
    userValueTypes :=
      contractUserValueTypeEntries contractName userValueTypes ++
        ctx.userValueTypes }

end TypeContext

inductive TypeError where
  | unsupported : String -> TypeError
  | duplicateName : String -> Name -> TypeError
  | unknownIdentifier : Name -> TypeError
  | unknownFunction : Name -> TypeError
  | unknownEvent : Name -> TypeError
  | unknownError : Name -> TypeError
  | unknownType : Path -> TypeError
  | ambiguousFunction : Name -> TypeError
  | missingTypeAnnotation : Name -> TypeError
  | invalidType : Ty -> TypeError
  | invalidMappingKey : Ty -> TypeError
  | invalidAbiType : Ty -> TypeError
  | invalidAbiCall : String -> TypeError
  | invalidConversion : Ty -> Ty -> TypeError
  | invalidStructConstructor : Name -> TypeError
  | invalidEnum : Name -> TypeError
  | invalidUserValueType : Name -> Ty -> TypeError
  | invalidVariableDecl : String -> TypeError
  | invalidFunctionHeader : String -> TypeError
  | invalidEventHeader : Name -> String -> TypeError
  | invalidErrorHeader : Name -> String -> TypeError
  | invalidContractHeader : String -> TypeError
  | invalidOverride : String -> TypeError
  | invalidTryCatch : String -> TypeError
  | mutabilityViolation : String -> TypeError
  | duplicateSignature : Name -> TypeError
  | valueCallToNonpayable : TypeError
  | invalidDataLocation : Ty -> Option Solidity.DataLocation ->
      TypeError
  | expectedType : Ty -> Ty -> TypeError
  | expectedBool : Ty -> TypeError
  | expectedNumeric : Ty -> TypeError
  | expectedInteger : Ty -> TypeError
  | expectedLValue : Solidity.Expr -> TypeError
  | arityMismatch : String -> Nat -> Nat -> TypeError
  | returnArityMismatch : Nat -> Nat -> TypeError
  | breakOutsideLoop
  | continueOutsideLoop
  | modifierPlaceholderOutsideModifier
  deriving Repr

namespace Result

def isOk {α : Type} : Except TypeError α -> Bool
  | Except.ok _ => true
  | Except.error _ => false

def isError {α : Type} : Except TypeError α -> Bool
  | Except.ok _ => false
  | Except.error _ => true

def toOption {α : Type} : Except TypeError α -> Option α
  | Except.ok value => some value
  | Except.error _ => none

end Result

def require (ok : Bool) (err : TypeError) : Except TypeError Unit :=
  if ok then Except.ok () else Except.error err

def requireEqTy (expected actual : Ty) : Except TypeError Unit :=
  require (actual == expected) (TypeError.expectedType expected actual)

def Ty.isBool : Ty -> Bool
  | Solidity.Ty.bool => true
  | _ => false

def Ty.isUnsignedInteger : Ty -> Bool
  | Solidity.Ty.uint _ => true
  | _ => false

def Ty.isSignedInteger : Ty -> Bool
  | Solidity.Ty.int _ => true
  | _ => false

def Ty.isInteger (ty : Ty) : Bool :=
  Ty.isUnsignedInteger ty || Ty.isSignedInteger ty

def Ty.isFixedPoint : Ty -> Bool
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | _ => false

def Ty.isSignedArithmeticOperand : Ty -> Bool
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | _ => false

def Ty.isNumeric : Ty -> Bool
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | _ => false

def Ty.isArithmeticOperand : Ty -> Bool
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | _ => false

def Ty.isFixedBytesOperand : Ty -> Bool
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | _ => false

def Ty.isBitwiseOperand (ty : Ty) : Bool :=
  Ty.isInteger ty || Ty.isFixedBytesOperand ty

def Ty.isRelationalOperand (types : TypeContext) (ty : Ty) : Bool :=
  match ty with
  | Solidity.Ty.address _ => true
  -- solc 0.8.35 defines ordered comparisons (`<`/`<=`/`>`/`>=`) on same-enum
  -- operands (compares ordinals, result `bool`). At this layer an enum type is
  -- carried as `Ty.user path`; `Ty.enum _` is the post-resolution shape. Both
  -- accept. Contracts are ALSO `Ty.user path` but are NOT ordered-comparable in
  -- solc, so we gate on `isEnumPath` (unlike equality, which also allows
  -- contracts). Same-enum-only is enforced upstream by `commonCheckedTyFor`:
  -- distinct enum paths have no `commonImplicit?`, so they never reach here.
  | Solidity.Ty.enum _ => true
  | Solidity.Ty.user path => types.isEnumPath path
  | _ => Ty.isArithmeticOperand ty || Ty.isFixedBytesOperand ty

def Ty.isShiftLeftOperand (ty : Ty) : Bool :=
  Ty.isInteger ty || Ty.isFixedBytesOperand ty

def Ty.integerBits? : Ty -> Option Nat
  | Solidity.Ty.uint bits => some bits
  | Solidity.Ty.int bits => some bits
  | _ => none

def Ty.isBuiltInValueTypeShape : Ty -> Bool
  | Solidity.Ty.bool => true
  | Solidity.Ty.address _ => true
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | _ => false

def TypeContext.isValueTypeShape (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.bool => true
  | Solidity.Ty.address _ => true
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | Solidity.Ty.user path =>
      types.isContractValuePath path || types.isEnumPath path ||
        types.isUserValueTypePath path
  | Solidity.Ty.functionWithLocations _ _ _ _ _ _ => true
  | _ => false

def TypeContext.isConstantStateVarTypeShape
    (types : TypeContext) (ty : Ty) : Bool :=
  TypeContext.isValueTypeShape types ty ||
    ty == Solidity.Ty.bytes ||
      ty == Solidity.Ty.string

def TypeContext.isImmutableStateVarTypeShape
    (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.functionWithLocations _ _ _ _ _
      Solidity.Visibility.external_ => false
  | ty => TypeContext.isValueTypeShape types ty

def Ty.isMappingKeyShape (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.bool => true
  | Solidity.Ty.address _ => true
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | Solidity.Ty.bytes => true
  | Solidity.Ty.string => true
  | Solidity.Ty.user path =>
      types.isContractValuePath path || types.isEnumPath path ||
        types.isUserValueTypePath path
  | _ => false

mutual

def Ty.needsDataLocation (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.bytes => true
  | Solidity.Ty.string => true
  | Solidity.Ty.array _ _ => true
  | Solidity.Ty.mapping _ _ => true
  | Solidity.Ty.user path => types.isStructPath path
  | Solidity.Ty.tuple tys =>
      Tys.needsDataLocation types tys
  | _ => false

def Tys.needsDataLocation (types : TypeContext) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.needsDataLocation types ty ||
        Tys.needsDataLocation types rest

end

mutual

def Ty.containsLibraryType (types : TypeContext) : Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.user path => types.isLibraryPath path
  | fuel + 1, Solidity.Ty.array element _ =>
      Ty.containsLibraryType types fuel element
  | fuel + 1, Solidity.Ty.mapping key value =>
      Ty.containsLibraryType types fuel key ||
        Ty.containsLibraryType types fuel value
  | fuel + 1, Solidity.Ty.tuple tys =>
      Tys.containsLibraryType types fuel tys
  | fuel + 1, Solidity.Ty.functionWithLocations params _ returns _
      _ _ =>
      Tys.containsLibraryType types fuel params ||
        Tys.containsLibraryType types fuel returns
  | _ + 1, _ => false

def Tys.containsLibraryType (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.containsLibraryType types fuel ty ||
        Tys.containsLibraryType types fuel rest

end

mutual

def TypeContext.tyContainsFixedPointFuel (types : TypeContext)
    (fuel : Nat) : Ty -> Bool
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.array element _ =>
      match fuel with
      | 0 => false
      | fuel + 1 => TypeContext.tyContainsFixedPointFuel types fuel element
  | Solidity.Ty.mapping key value =>
      match fuel with
      | 0 => false
      | fuel + 1 =>
          TypeContext.tyContainsFixedPointFuel types fuel key ||
            TypeContext.tyContainsFixedPointFuel types fuel value
  | Solidity.Ty.tuple tys =>
      match fuel with
      | 0 => false
      | fuel + 1 => Tys.containsFixedPointFuel types fuel tys
  | Solidity.Ty.user path =>
      match fuel with
      | 0 => false
      | fuel + 1 =>
          match types.lookupUserValueType? path with
          | some underlying =>
              TypeContext.tyContainsFixedPointFuel types fuel underlying
          | none =>
              match types.lookupStruct? path with
              | some decl =>
                  StructFields.containsFixedPointFuel types fuel decl.fields
              | none => false
  | _ => false

def Tys.containsFixedPointFuel (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      TypeContext.tyContainsFixedPointFuel types fuel ty ||
        Tys.containsFixedPointFuel types fuel rest

def StructFields.containsFixedPointFuel
    (types : TypeContext) (fuel : Nat) :
    List Solidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      TypeContext.tyContainsFixedPointFuel types fuel field.ty ||
        StructFields.containsFixedPointFuel types fuel rest

end

def TypeContext.tyContainsFixedPoint (types : TypeContext) (ty : Ty) :
    Bool :=
  TypeContext.tyContainsFixedPointFuel types 64 ty

def TypeContext.requireNoFixedPointValue
    (types : TypeContext) (ty : Ty) (what : String) :
    Except TypeError Unit :=
  require (!types.tyContainsFixedPoint ty)
    (TypeError.unsupported (what ++ " fixed point value"))

def TypeContext.requireNoFixedPointAssignment
    (types : TypeContext) (actual expected : Ty) :
    Except TypeError Unit := do
  types.requireNoFixedPointValue actual "assignment from"
  types.requireNoFixedPointValue expected "assignment to"

mutual

def Ty.isExternalFunctionAbiTypeShape (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.bool => true
  | _ + 1, Solidity.Ty.address _ => true
  | _ + 1, Solidity.Ty.uint _ => true
  | _ + 1, Solidity.Ty.int _ => true
  | _ + 1, Solidity.Ty.fixed _ _ => true
  | _ + 1, Solidity.Ty.ufixed _ _ => true
  | _ + 1, Solidity.Ty.bytesN _ => true
  | _ + 1, Solidity.Ty.fixedBytes _ => true
  | _ + 1, Solidity.Ty.bytes => true
  | _ + 1, Solidity.Ty.string => true
  | fuel + 1, Solidity.Ty.array element _ =>
      Ty.isExternalFunctionAbiTypeShape types fuel element
  | fuel + 1, Solidity.Ty.tuple tys =>
      Tys.allExternalFunctionAbiTypeShape types fuel tys
  | fuel + 1, Solidity.Ty.user path =>
      if types.isContractValuePath path || types.isEnumPath path then
        true
      else
        match types.lookupUserValueType? path with
        | some underlying =>
            Ty.isExternalFunctionAbiTypeShape types fuel underlying
        | none =>
            match types.lookupStruct? path with
            | some decl =>
                StructFields.allExternalFunctionAbiTypeShape types fuel
                  decl.fields
            | none => false
  | fuel + 1, Solidity.Ty.functionWithLocations params _ returns _
      _ visibility =>
      visibility == Solidity.Visibility.external_ &&
        Tys.allExternalFunctionAbiTypeShape types fuel params &&
          Tys.allExternalFunctionAbiTypeShape types fuel returns
  | _ + 1, _ => false

def Tys.allExternalFunctionAbiTypeShape (types : TypeContext)
    (fuel : Nat) : List Ty -> Bool
  | [] => true
  | ty :: rest =>
      Ty.isExternalFunctionAbiTypeShape types fuel ty &&
        Tys.allExternalFunctionAbiTypeShape types fuel rest

def StructFields.allExternalFunctionAbiTypeShape (types : TypeContext)
    (fuel : Nat) : List Solidity.StructField -> Bool
  | [] => true
  | field :: rest =>
      Ty.isExternalFunctionAbiTypeShape types fuel field.ty &&
        StructFields.allExternalFunctionAbiTypeShape types fuel rest

end

mutual

def Ty.containsMapping (types : TypeContext) : Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.mapping _ _ => true
  | fuel + 1, Solidity.Ty.array element _ =>
      Ty.containsMapping types fuel element
  | fuel + 1, Solidity.Ty.tuple tys =>
      Tys.containsMapping types fuel tys
  | fuel + 1, Solidity.Ty.user path =>
      match types.lookupStruct? path with
      | some structDecl => StructFields.containsMapping types fuel structDecl.fields
      | none => false
  | fuel + 1, Solidity.Ty.functionWithLocations params _ returns _
      _ _ =>
      Tys.containsMapping types fuel params ||
        Tys.containsMapping types fuel returns
  | _, _ => false

def Tys.containsMapping (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.containsMapping types fuel ty || Tys.containsMapping types fuel rest

def StructFields.containsMapping (types : TypeContext) (fuel : Nat) :
    List Solidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      Ty.containsMapping types fuel field.ty ||
        StructFields.containsMapping types fuel rest

end

def Ty.functionDataLocationValid (types : TypeContext) (ty : Ty)
    (location : Option Solidity.DataLocation) : Bool :=
  if Ty.needsDataLocation types ty then
    location.isSome &&
      (!Ty.containsMapping types 64 ty ||
        location == some Solidity.DataLocation.storage)
  else
    location.isNone

def Tys.functionDataLocationsValid (types : TypeContext) :
    List Ty -> List (Option Solidity.DataLocation) -> Bool
  | [], [] => true
  | ty :: tyRest, location :: locationRest =>
      Ty.functionDataLocationValid types ty location &&
        Tys.functionDataLocationsValid types tyRest locationRest
  | _, _ => false

def Tys.externalFunctionDataLocationsValid (types : TypeContext) :
    List Ty -> List (Option Solidity.DataLocation) -> Bool
  | [], [] => true
  | ty :: tyRest, location :: locationRest =>
      Ty.functionDataLocationValid types ty location &&
        location != some Solidity.DataLocation.storage &&
        Tys.externalFunctionDataLocationsValid types tyRest locationRest
  | _, _ => false

mutual

def Ty.isValid (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.uint bits =>
      bits > 0 && bits <= 256 && bits % 8 == 0
  | Solidity.Ty.int bits =>
      bits > 0 && bits <= 256 && bits % 8 == 0
  | Solidity.Ty.fixed bits decimals =>
      Solidity.Ty.validFixedPointShape bits decimals
  | Solidity.Ty.ufixed bits decimals =>
      Solidity.Ty.validFixedPointShape bits decimals
  | Solidity.Ty.bytesN size => size > 0 && size <= 32
  | Solidity.Ty.fixedBytes size => size > 0 && size <= 32
  | Solidity.Ty.array element none => Ty.isValid types element
  | Solidity.Ty.array element (some size) =>
      size > 0 && Ty.isValid types element
  | Solidity.Ty.mapping key value =>
      Ty.isValid types key && Ty.isValid types value &&
        Ty.isMappingKeyShape types key
  | Solidity.Ty.tuple tys => Tys.allValid types tys
  | Solidity.Ty.user path => types.isKnownPath path
  | Solidity.Ty.functionWithLocations params paramLocations returns
      returnLocations mutability visibility =>
      Tys.allValid types params && Tys.allValid types returns &&
        Tys.functionDataLocationsValid types params paramLocations &&
        Tys.functionDataLocationsValid types returns returnLocations &&
        (mutability != Solidity.StateMutability.payable ||
          visibility == Solidity.Visibility.external_) &&
        (visibility == Solidity.Visibility.internal_ ||
          (visibility == Solidity.Visibility.external_ &&
            Tys.externalFunctionDataLocationsValid types params
              paramLocations &&
            Tys.externalFunctionDataLocationsValid types returns
              returnLocations &&
            Tys.allExternalFunctionAbiTypeShape types 64 params &&
              Tys.allExternalFunctionAbiTypeShape types 64 returns))
  | _ => true

def Tys.allValid (types : TypeContext) : List Ty -> Bool
  | [] => true
  | ty :: rest => Ty.isValid types ty && Tys.allValid types rest

end

mutual

def Ty.abiEncodedDynamic? (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => true
  | _ + 1, Solidity.Ty.bytes => true
  | _ + 1, Solidity.Ty.string => true
  | _ + 1, Solidity.Ty.array _ none => true
  | fuel + 1, Solidity.Ty.array element (some _) =>
      Ty.abiEncodedDynamic? types fuel element
  | fuel + 1, Solidity.Ty.tuple tys =>
      Tys.anyAbiEncodedDynamic? types fuel tys
  | fuel + 1, Solidity.Ty.user path =>
      match types.lookupUserValueType? path with
      | some underlying => Ty.abiEncodedDynamic? types fuel underlying
      | none =>
          match types.lookupStruct? path with
          | some decl => StructFields.anyAbiEncodedDynamic? types fuel decl.fields
          | none => false
  | _ + 1, _ => false

def Tys.anyAbiEncodedDynamic? (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.abiEncodedDynamic? types fuel ty ||
        Tys.anyAbiEncodedDynamic? types fuel rest

def StructFields.anyAbiEncodedDynamic? (types : TypeContext) (fuel : Nat) :
    List Solidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      Ty.abiEncodedDynamic? types fuel field.ty ||
        StructFields.anyAbiEncodedDynamic? types fuel rest

end

mutual

def Ty.requiresAbiCoderV2? (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => true
  | fuel + 1, Solidity.Ty.array element _ =>
      Ty.requiresAbiCoderV2? types fuel element ||
        Ty.abiEncodedDynamic? types fuel element
  | _ + 1, Solidity.Ty.tuple _ => true
  | fuel + 1, Solidity.Ty.user path =>
      match types.lookupStruct? path with
      | some _ => true
      | none =>
          match types.lookupUserValueType? path with
          | some underlying => Ty.requiresAbiCoderV2? types fuel underlying
          | none => false
  | fuel + 1, Solidity.Ty.functionWithLocations params _ returns _
      _ _ =>
      Tys.anyRequiresAbiCoderV2? types fuel params ||
        Tys.anyRequiresAbiCoderV2? types fuel returns
  | _ + 1, _ => false

def Tys.anyRequiresAbiCoderV2? (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.requiresAbiCoderV2? types fuel ty ||
        Tys.anyRequiresAbiCoderV2? types fuel rest

end

def TypeContext.abiCoderSupports (types : TypeContext) (ty : Ty) :
    Bool :=
  !types.abiCoderV1 || !Ty.requiresAbiCoderV2? types 64 ty

def Tys.firstAbiCoderV2Only? (types : TypeContext) :
    List Ty -> Option Ty
  | [] => none
  | ty :: rest =>
      if TypeContext.abiCoderSupports types ty then
        Tys.firstAbiCoderV2Only? types rest
      else
        some ty

def Parameters.firstAbiCoderV2OnlyTy? (types : TypeContext) :
    List Solidity.Parameter -> Option Ty
  | [] => none
  | param :: rest =>
      if TypeContext.abiCoderSupports types param.ty then
        Parameters.firstAbiCoderV2OnlyTy? types rest
      else
        some param.ty

-- SHALLOW omission, matching solc `FunctionType(VariableDeclaration)`
-- (Types.cpp): at the gettered struct's own level, only a *direct* mapping
-- member and a *direct* (non-string/bytes) array member are omitted from the
-- getter. A nested struct member is returned WHOLE (not recursed into), so a
-- mapping buried inside a nested struct does NOT drop the member here — instead
-- the returned member makes the whole getter illegal (error 6744), enforced in
-- `StateVarDecl.check`.
def Ty.omittedFromStructPublicGetter? (_types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.mapping _ _ => true
  | _ + 1, Solidity.Ty.array _ _ => true
  | _ + 1, _ => false

def structGetterReturnTys (types : TypeContext) :
    List Solidity.StructField -> List Ty
  | [] => []
  | field :: rest =>
      if Ty.omittedFromStructPublicGetter? types 64 field.ty then
        structGetterReturnTys types rest
      else
        field.ty :: structGetterReturnTys types rest

def tupleGetterReturnTys (types : TypeContext) : List Ty -> List Ty
  | [] => []
  | ty :: rest =>
      if Ty.omittedFromStructPublicGetter? types 64 ty then
        tupleGetterReturnTys types rest
      else
        ty :: tupleGetterReturnTys types rest

def Ty.publicGetterShape? (types : TypeContext) :
    Nat -> Ty -> Option (List Ty × List Ty)
  | 0, _ => none
  | fuel + 1, Solidity.Ty.mapping key value => do
      let tail ← Ty.publicGetterShape? types fuel value
      some (key :: tail.fst, tail.snd)
  | fuel + 1, Solidity.Ty.array element _ => do
      let tail ← Ty.publicGetterShape? types fuel element
      some (Solidity.Ty.uint 256 :: tail.fst, tail.snd)
  | _ + 1, Solidity.Ty.tuple tys =>
      some ([], tupleGetterReturnTys types tys)
  | _ + 1, Solidity.Ty.user path =>
      match types.lookupStruct? path with
      | some structDecl =>
          some ([], structGetterReturnTys types structDecl.fields)
      | none => some ([], [Solidity.Ty.user path])
  | _ + 1, ty => some ([], [ty])

mutual

def TypeContext.abiCanonicalFuel? (types : TypeContext) :
    Nat -> Ty -> Option String
  | 0, _ => none
  | _ + 1, Solidity.Ty.bool => some "bool"
  | _ + 1, Solidity.Ty.address _ => some "address"
  | _ + 1, Solidity.Ty.uint bits =>
      if bits == 0 then
        some "uint256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("uint" ++ toString bits)
      else
        none
  | _ + 1, Solidity.Ty.int bits =>
      if bits == 0 then
        some "int256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("int" ++ toString bits)
      else
        none
  | _ + 1, Solidity.Ty.fixed bits decimals =>
      if Solidity.Ty.validFixedPointShape bits decimals then
        some ("fixed" ++ toString bits ++ "x" ++ toString decimals)
      else
        none
  | _ + 1, Solidity.Ty.ufixed bits decimals =>
      if Solidity.Ty.validFixedPointShape bits decimals then
        some ("ufixed" ++ toString bits ++ "x" ++ toString decimals)
      else
        none
  | _ + 1, Solidity.Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | _ + 1, Solidity.Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | _ + 1, Solidity.Ty.bytes => some "bytes"
  | _ + 1, Solidity.Ty.string => some "string"
  | fuel + 1, Solidity.Ty.array ty none => do
      let base ← TypeContext.abiCanonicalFuel? types fuel ty
      some (base ++ "[]")
  | fuel + 1, Solidity.Ty.array ty (some size) => do
      let base ← TypeContext.abiCanonicalFuel? types fuel ty
      some (base ++ "[" ++ toString size ++ "]")
  | fuel + 1, Solidity.Ty.tuple tys => do
      let elements ← TypeContext.abiCanonicalListFuel? types fuel tys
      some ("(" ++
        Solidity.Executable.joinStringsWith "," elements ++ ")")
  | fuel + 1, Solidity.Ty.user path =>
      match types.lookupContractDecl? path with
      | some decl =>
          if decl.kind == Solidity.ContractKind.library then
            none
          else
            some "address"
      | none =>
          match types.lookupEnum? path with
          | some _ => some "uint8"
          | none =>
              match types.lookupUserValueType? path with
              | some underlying =>
                  TypeContext.abiCanonicalFuel? types fuel underlying
              | none =>
                  match types.lookupStruct? path with
                  | some decl =>
                      StructDecl.abiCanonicalFuel? types fuel decl
                  | none => none
  | _ + 1, Solidity.Ty.functionWithLocations _ _ _ _ _ visibility =>
      if visibility == Solidity.Visibility.external_ then
        some "function"
      else
        none
  | _ + 1, _ => none

def TypeContext.abiCanonicalListFuel? (types : TypeContext) (fuel : Nat) :
    List Ty -> Option (List String)
  | [] => some []
  | ty :: rest => do
      let head ← TypeContext.abiCanonicalFuel? types fuel ty
      let tail ← TypeContext.abiCanonicalListFuel? types fuel rest
      some (head :: tail)

def StructDecl.abiCanonicalFuel? (types : TypeContext) (fuel : Nat)
    (decl : Solidity.StructDecl) : Option String := do
  let elements ← StructFields.abiCanonicalFuel? types fuel decl.fields
  some ("(" ++
    Solidity.Executable.joinStringsWith "," elements ++ ")")

def StructFields.abiCanonicalFuel? (types : TypeContext) (fuel : Nat) :
    List Solidity.StructField -> Option (List String)
  | [] => some []
  | field :: rest => do
      let head ← TypeContext.abiCanonicalFuel? types fuel field.ty
      let tail ← StructFields.abiCanonicalFuel? types fuel rest
      some (head :: tail)

end

def TypeContext.abiCanonical? (types : TypeContext) (ty : Ty) :
    Option String :=
  TypeContext.abiCanonicalFuel? types 64 ty

def TypeContext.abiCanonicalList? (types : TypeContext)
    (tys : List Ty) : Option (List String) :=
  TypeContext.abiCanonicalListFuel? types 64 tys

def TypeContext.isAbiEncodable (types : TypeContext) (ty : Ty) : Bool :=
  match TypeContext.abiCanonical? types ty with
  | some _ => true
  | none => false

def Tys.firstNonAbiEncodable? (types : TypeContext) :
    List Ty -> Option Ty
  | [] => none
  | ty :: rest =>
      if TypeContext.isAbiEncodable types ty then
        Tys.firstNonAbiEncodable? types rest
      else
        some ty

def StateMutability.canImplicitlyConvertFunction
    (actual expected : Solidity.StateMutability) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | Solidity.StateMutability.pure,
      Solidity.StateMutability.view => true
    | Solidity.StateMutability.pure,
      Solidity.StateMutability.nonpayable => true
    | Solidity.StateMutability.view,
      Solidity.StateMutability.nonpayable => true
    | Solidity.StateMutability.payable,
      Solidity.StateMutability.nonpayable => true
    | _, _ => false

def Ty.canImplicitlyConvert (actual expected : Ty) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | Solidity.Ty.address true,
      Solidity.Ty.address false => true
    | Solidity.Ty.uint actualBits,
      Solidity.Ty.uint expectedBits => actualBits <= expectedBits
    | Solidity.Ty.int actualBits,
      Solidity.Ty.int expectedBits => actualBits <= expectedBits
    -- A1: solc IntegerType::isImplicitlyConvertibleTo (Types.cpp:611-614)
    -- forbids ALL implicit signed<->unsigned conversions (uintN->intM and
    -- intN->uintM). Only same-signedness widening is implicit. The former
    -- `uint actualBits -> int expectedBits` arm was removed.
    | Solidity.Ty.fixed actualBits actualDecimals,
      Solidity.Ty.fixed expectedBits expectedDecimals =>
        Solidity.Ty.fixedPointImplicitlyConvertible
          true actualBits actualDecimals true expectedBits expectedDecimals
    | Solidity.Ty.ufixed actualBits actualDecimals,
      Solidity.Ty.ufixed expectedBits expectedDecimals =>
        Solidity.Ty.fixedPointImplicitlyConvertible
          false actualBits actualDecimals false expectedBits expectedDecimals
    | Solidity.Ty.ufixed actualBits actualDecimals,
      Solidity.Ty.fixed expectedBits expectedDecimals =>
        Solidity.Ty.fixedPointImplicitlyConvertible
          false actualBits actualDecimals true expectedBits expectedDecimals
    | Solidity.Ty.bytesN actualSize,
      Solidity.Ty.bytesN expectedSize => actualSize <= expectedSize
    | Solidity.Ty.fixedBytes actualSize,
      Solidity.Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | Solidity.Ty.bytesN actualSize,
      Solidity.Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | Solidity.Ty.fixedBytes actualSize,
      Solidity.Ty.bytesN expectedSize =>
        actualSize <= expectedSize
    | Solidity.Ty.functionWithLocations actualParams
        actualParamLocations actualReturns actualReturnLocations
        actualMutability actualVisibility,
      Solidity.Ty.functionWithLocations expectedParams
        expectedParamLocations expectedReturns expectedReturnLocations
        expectedMutability expectedVisibility =>
        actualParams == expectedParams &&
          actualParamLocations == expectedParamLocations &&
          actualReturns == expectedReturns &&
          actualReturnLocations == expectedReturnLocations &&
          actualVisibility == expectedVisibility &&
          StateMutability.canImplicitlyConvertFunction
            actualMutability expectedMutability
    | _, _ => false

-- G14 / R2: acceptance of a copy assignment INTO a (non-pointer) storage array
-- with an implicitly-convertible element type and/or a differing length. solc's
-- rule (`ArrayType::isImplicitlyConvertibleTo` for a non-pointer storage dest,
-- `Types.cpp:1628-1665`) is: base implicitly convertible; a DYNAMIC dest accepts
-- any source length (dynamic or fixed source); a FIXED dest `T[N]` requires a
-- FIXED source `S[M]` with `N ≥ M`. The runtime resizes/pads the dest to the
-- source length, converts each element (sign/zero-extending an integer widening
-- to the dest width — a widening never overflows, so never Panic 0x11), and
-- zero-fills / pads the tail (probed against the pin, 2026-07-08):
--   * dyn dest ← fixed src ACCEPT; fixed dest N<M REJECT; fixed dest N≥M ACCEPT;
--   * signed↔unsigned base REJECT; base narrowing REJECT; fixed dest ← dyn src
--     REJECT (all mirrored by the base/length checks below).
--
-- The base must be an INTEGER type (uint/int) that `canImplicitlyConvert` maps
-- (same-signedness widening — this already forbids signed↔unsigned and
-- narrowing, exactly as solc). Restricting to integer bases keeps every accepted
-- shape one whose copied VALUES the interpreter reproduces bit-for-bit against
-- Forge (see the R2 DECISIONS entry). The strict same-base rule still governs
-- pointer/memory targets and every non-storage context, so this is only
-- consulted for a genuine storage-variable dest.
def Ty.integerArrayElemWiden? (srcElem destElem : Ty) : Bool :=
  srcElem.isInteger && destElem.isInteger &&
    Ty.canImplicitlyConvert srcElem destElem

def Ty.storageArrayCopyAssignable? (destTy srcTy : Ty) : Bool :=
  match destTy, srcTy with
  -- Dynamic dest: any source length (dynamic OR fixed source).
  | Solidity.Ty.array destElem none,
    Solidity.Ty.array srcElem _ =>
      Ty.integerArrayElemWiden? srcElem destElem
  -- Fixed dest `T[N]`: fixed source `S[M]` with N ≥ M.
  | Solidity.Ty.array destElem (some n),
    Solidity.Ty.array srcElem (some m) =>
      m <= n && Ty.integerArrayElemWiden? srcElem destElem
  | _, _ => false

def Ty.fixedBytesSize? : Ty -> Option Nat
  | Solidity.Ty.bytesN size =>
      if 0 < size && size <= 32 then some size else none
  | Solidity.Ty.fixedBytes size =>
      if 0 < size && size <= 32 then some size else none
  | _ => none

def Ty.isFixedBytes (ty : Ty) : Bool :=
  match Ty.fixedBytesSize? ty with
  | some _ => true
  | none => false

def Ty.uintBits? : Ty -> Option Nat
  | Solidity.Ty.uint bits =>
      if bits > 0 && bits <= 256 && bits % 8 == 0 then some bits else none
  | _ => none

def Ty.intBits? : Ty -> Option Nat
  | Solidity.Ty.int bits =>
      if bits > 0 && bits <= 256 && bits % 8 == 0 then some bits else none
  | _ => none

def Ty.isSignedIntegerTy : Ty -> Bool
  | Solidity.Ty.int _ => true
  | _ => false

def Ty.sameIntegerWidth (actual target : Ty) : Bool :=
  match actual.integerBits?, target.integerBits? with
  | some actualBits, some targetBits => actualBits == targetBits
  | _, _ => false

def Ty.sameIntegerSignedness (actual target : Ty) : Bool :=
  actual.isSignedIntegerTy == target.isSignedIntegerTy

def Ty.integerExplicitConversionAllowed (actual target : Ty) : Bool :=
  (actual.isInteger && target.isInteger) &&
    (Ty.sameIntegerWidth actual target || Ty.sameIntegerSignedness actual target)

-- A3: solc FixedBytesType::isExplicitlyConvertibleTo (Types.cpp:1364-1365)
-- allows bytesN <-> integer only for UNSIGNED integers of the same bit width
-- (`!integerType->isSigned() && numBits == numBytes*8`); the symmetric
-- IntegerType::isExplicitlyConvertibleTo (Types.cpp:638-639) likewise requires
-- `!isSigned()`. So `int256(bytes32)` / `bytes32(int256)` are rejected. Use
-- uintBits? (unsigned only) rather than integerBits? (any integer).
def Ty.fixedBytesIntegerSameSize (fixedTy intTy : Ty) : Bool :=
  match fixedTy.fixedBytesSize?, intTy.uintBits? with
  | some size, some bits => size * 8 == bits
  | _, _ => false

def TypeContext.isContractTy (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.user path => types.isContractPath path
  | _ => false

def TypeContext.isEnumTy (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.user path => types.isEnumPath path
  | _ => false

def TypeContext.isUserValueTy (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.user path => types.isUserValueTypePath path
  | _ => false

def TypeContext.contractHasAncestorPathFuel
    (types : TypeContext) : Nat -> Path -> Path -> Bool
  | 0, _, _ => false
  | fuel + 1, contractPath, ancestorPath =>
      if contractPath == ancestorPath then
        true
      else
        match types.lookupContractDecl? contractPath with
        | none => false
        | some decl =>
            decl.bases.any
              (fun base =>
                TypeContext.contractHasAncestorPathFuel types fuel
                  base.base ancestorPath)

def TypeContext.contractsRelated (types : TypeContext)
    (left right : Path) : Bool :=
  TypeContext.contractHasAncestorPathFuel types 64 left right ||
    TypeContext.contractHasAncestorPathFuel types 64 right left

def FunctionDecl.canReceiveEther
    (fn : Solidity.FunctionDecl) : Bool :=
  (fn.kind == Solidity.FunctionKind.receive &&
      fn.mutability == Solidity.StateMutability.payable) ||
    (fn.kind == Solidity.FunctionKind.fallback &&
      fn.mutability == Solidity.StateMutability.payable)

def ContractItems.canReceiveEther :
    List Solidity.ContractItem -> Bool
  | [] => false
  | Solidity.ContractItem.function fn :: rest =>
      FunctionDecl.canReceiveEther fn || ContractItems.canReceiveEther rest
  | _ :: rest => ContractItems.canReceiveEther rest

def TypeContext.contractCanReceiveEtherFuel
    (types : TypeContext) : Nat -> Path -> Bool
  | 0, _ => false
  | fuel + 1, path =>
      match types.lookupContractDecl? path with
      | none => false
      | some decl =>
          ContractItems.canReceiveEther decl.items ||
            decl.bases.any (fun base =>
              TypeContext.contractCanReceiveEtherFuel types fuel base.base)

def TypeContext.contractCanReceiveEther (types : TypeContext)
    (path : Path) : Bool :=
  TypeContext.contractCanReceiveEtherFuel types 64 path

def TypeContext.canImplicitlyConvert (types : TypeContext)
    (actual expected : Ty) : Bool :=
  if Ty.canImplicitlyConvert actual expected then
    true
  else
    match actual, expected with
    | Solidity.Ty.user actualPath,
      Solidity.Ty.user expectedPath =>
        TypeContext.pathsAreLocalAliasIn
          types.structs actualPath expectedPath ||
        TypeContext.pathsAreLocalAliasIn
          types.enums actualPath expectedPath ||
        TypeContext.pathsAreLocalAliasIn
          types.userValueTypes actualPath expectedPath ||
        (types.isContractPath actualPath &&
            types.isContractPath expectedPath &&
            TypeContext.contractHasAncestorPathFuel types 64
              actualPath expectedPath)
    | _, _ => false

def fixedPointLiteralRaw? (decimals : Nat)
    (expr : Solidity.Expr) : Option Nat := do
  let value ← Solidity.Executable.Expr.numberLiteralRat? expr
  let scaled := value.num * (10 ^ decimals : Int)
  let den := Int.ofNat value.den
  if den == 0 then
    none
  else if scaled % den == 0 then
    let q := scaled / den
    if q < 0 then none else some q.toNat
  else
    none

def negatedFixedPointLiteralRaw? (decimals : Nat) :
    Solidity.Expr -> Option Nat
  | Solidity.Expr.unary Solidity.UnaryOp.neg inner =>
      fixedPointLiteralRaw? decimals inner
  | Solidity.Expr.call
      (Solidity.Expr.typeName _) [Solidity.Arg.positional expr] =>
      negatedFixedPointLiteralRaw? decimals expr
  | _ => none

def fixedPointLiteralFits (target : Ty)
    (expr : Solidity.Expr) : Bool :=
  match target with
  | Solidity.Ty.fixed bits decimals =>
      Solidity.Ty.validFixedPointShape bits decimals &&
        match negatedFixedPointLiteralRaw? decimals expr with
        | some magnitude => magnitude <= 2 ^ (bits - 1)
        | none =>
            match fixedPointLiteralRaw? decimals expr with
            | some value => value < 2 ^ (bits - 1)
            | none => false
  | Solidity.Ty.ufixed bits decimals =>
      Solidity.Ty.validFixedPointShape bits decimals &&
        match negatedFixedPointLiteralRaw? decimals expr with
        | some magnitude => magnitude == 0
        | none =>
            match fixedPointLiteralRaw? decimals expr with
            | some value => value < 2 ^ bits
            | none => false
  | _ => false

def typeConversionLiteralFits (target : Ty)
    (expr : Solidity.Expr) : Bool :=
  match Solidity.Executable.Expr.toCoreNumericLiteralAs? target expr with
  | some _ => true
  | none =>
      match Solidity.Executable.Expr.toCoreFixedBytesLiteralAs?
          target expr with
      | some _ => true
      | none =>
          fixedPointLiteralFits target expr ||
            match target with
            | Solidity.Ty.address false =>
                match Solidity.Executable.Expr.toCoreAddressLiteral?
                    expr with
                | some _ => true
                | none => false
            | _ => false

def implicitLiteralFits (target : Ty)
    (expr : Solidity.Expr) : Bool :=
  match Solidity.Executable.Expr.toCoreNumericLiteralAs? target expr with
  | some _ => true
  | none =>
      match Solidity.Executable.Expr.toCoreFixedBytesLiteralAs?
          target expr with
      | some _ => true
      | none =>
          (target == Solidity.Ty.bytes &&
            match expr with
            | Solidity.Expr.literal
                (Solidity.Literal.string _) => true
            | Solidity.Expr.literal
                (Solidity.Literal.unicodeString _) => true
            | _ => false) ||
            fixedPointLiteralFits target expr

def exprIsUint256ZeroLiteral (expr : Solidity.Expr) : Bool :=
  match
      Solidity.Executable.Expr.toCoreNumericLiteralAs?
        (Solidity.Ty.uint 256) expr with
  | some (SolidCore.Solidity.Source.Expr.word value) =>
      SolidCore.Solidity.Source.wordEq value 0
  | _ => false

def exprIsUntypedNumberLiteralExpression :
    Solidity.Expr -> Bool
  | Solidity.Expr.literal
      (Solidity.Literal.number _) => true
  | Solidity.Expr.literal
      (Solidity.Literal.unitNumber _ _) => true
  | Solidity.Expr.unary Solidity.UnaryOp.neg inner =>
      exprIsUntypedNumberLiteralExpression inner
  | Solidity.Expr.unary Solidity.UnaryOp.bitNot inner =>
      exprIsUntypedNumberLiteralExpression inner
  | Solidity.Expr.binary _ lhs rhs =>
      exprIsUntypedNumberLiteralExpression lhs &&
        exprIsUntypedNumberLiteralExpression rhs
  | _ => false

def exprIsUntypedImplicitLiteralExpression
    (expr : Solidity.Expr) : Bool :=
  exprIsUntypedNumberLiteralExpression expr ||
    Solidity.Executable.Expr.isFixedBytesLiteralCandidate expr

def enumUntypedLiteralConversionAllowed? (types : TypeContext)
    (path : Path) (expr : Solidity.Expr) : Option Bool :=
  if exprIsUntypedNumberLiteralExpression expr then
    some
      (match types.lookupEnum? path with
      | some decl =>
          match Solidity.Executable.EnumDecl.maxValue? decl with
          | some maxValue =>
              match
                  Solidity.Executable.Expr.toCoreNumericLiteralAs?
                    (Solidity.Ty.uint 256) expr with
              | some (SolidCore.Solidity.Source.Expr.word value) =>
                  value <= maxValue
              | _ => false
          | none => false
      | none => false)
  else
    none

def Ty.canExplicitlyConvert (types : TypeContext)
    (sourceExpr : Solidity.Expr) (actual target : Ty) : Bool :=
  if exprIsUntypedNumberLiteralExpression sourceExpr then
    match target with
    | Solidity.Ty.address false =>
        typeConversionLiteralFits target sourceExpr
    | Solidity.Ty.uint _
    | Solidity.Ty.int _
    | Solidity.Ty.fixed _ _
    | Solidity.Ty.ufixed _ _
    | Solidity.Ty.bytesN _
    | Solidity.Ty.fixedBytes _ =>
        typeConversionLiteralFits target sourceExpr
    | Solidity.Ty.user path =>
        match enumUntypedLiteralConversionAllowed? types path sourceExpr with
        | some allowed => allowed
        | none => false
    | _ => false
  else if actual == target then
    true
  else
    match actual, target with
    | _, Solidity.Ty.address true => false
    | Solidity.Ty.address _, Solidity.Ty.address false => true
    | Solidity.Ty.uint 160, Solidity.Ty.address false => true
    | Solidity.Ty.bytesN 20, Solidity.Ty.address false => true
    | Solidity.Ty.fixedBytes 20, Solidity.Ty.address false => true
    | Solidity.Ty.user path, Solidity.Ty.address false =>
        types.isContractPath path
    | _, Solidity.Ty.address false =>
        typeConversionLiteralFits target sourceExpr
    | Solidity.Ty.string, Solidity.Ty.bytes => true
    | Solidity.Ty.bytes, Solidity.Ty.string => true
    | _, Solidity.Ty.uint _ =>
        (match actual with
        | Solidity.Ty.user path => types.isEnumPath path
        | _ => false) ||
          actual.isFixedPoint ||
          Ty.integerExplicitConversionAllowed actual target ||
          Ty.fixedBytesIntegerSameSize actual target ||
          (match actual with
          | Solidity.Ty.address false =>
              target == Solidity.Ty.uint 160
          | _ => false) ||
          typeConversionLiteralFits target sourceExpr
    | _, Solidity.Ty.int _ =>
        Ty.integerExplicitConversionAllowed actual target ||
          actual.isFixedPoint ||
          Ty.fixedBytesIntegerSameSize actual target ||
          typeConversionLiteralFits target sourceExpr
    | _, Solidity.Ty.fixed _ _
    | _, Solidity.Ty.ufixed _ _ =>
        actual.isFixedPoint ||
          typeConversionLiteralFits target sourceExpr
    | _, Solidity.Ty.bytesN _ =>
        if Solidity.Executable.Expr.isFixedBytesLiteralCandidate
            sourceExpr then
          typeConversionLiteralFits target sourceExpr
        else
          (actual.isFixedBytes || actual == Solidity.Ty.bytes ||
            (actual == Solidity.Ty.address false &&
              target == Solidity.Ty.bytesN 20) ||
            Ty.fixedBytesIntegerSameSize target actual) ||
            typeConversionLiteralFits target sourceExpr
    | _, Solidity.Ty.fixedBytes _ =>
        if Solidity.Executable.Expr.isFixedBytesLiteralCandidate
            sourceExpr then
          typeConversionLiteralFits target sourceExpr
        else
          (actual.isFixedBytes || actual == Solidity.Ty.bytes ||
            (actual == Solidity.Ty.address false &&
              target == Solidity.Ty.fixedBytes 20) ||
            Ty.fixedBytesIntegerSameSize target actual) ||
            typeConversionLiteralFits target sourceExpr
    | Solidity.Ty.address sourcePayable,
      Solidity.Ty.user path =>
        types.isContractPath path &&
          (sourcePayable || !types.contractCanReceiveEther path)
    | Solidity.Ty.user actualPath, Solidity.Ty.user targetPath =>
        if types.isContractPath actualPath && types.isContractPath targetPath then
          -- A4: solc ContractType::isExplicitlyConvertibleTo (Types.cpp:1491)
          -- falls through to isImplicitlyConvertibleTo (Types.cpp:1475-1486),
          -- which permits contract->contract only when the target is in the
          -- source's linearized bases, i.e. an UP-cast (derived->base). A
          -- down-cast (base->derived) is a type error. Require the target to be
          -- an ancestor (base) of the source, not merely related.
          TypeContext.contractHasAncestorPathFuel types 64 actualPath targetPath
        else if types.isEnumPath targetPath then
          actual.isInteger
        else
          false
    | _, Solidity.Ty.user path =>
        if types.isEnumPath path then
          match enumUntypedLiteralConversionAllowed? types path sourceExpr with
          | some allowed => allowed
          | none => actual.isInteger
        else
          false
    | _, _ => false

def checkTy (types : TypeContext) (ty : Ty) : Except TypeError Unit :=
  require (Ty.isValid types ty) (TypeError.invalidType ty)

def checkLocationForTy (types : TypeContext) (ty : Ty)
    (location : Option Solidity.DataLocation) :
    Except TypeError Unit := do
  checkTy types ty
  require (!Ty.containsLibraryType types 64 ty)
    (TypeError.invalidType ty)
  if !Ty.needsDataLocation types ty && location.isSome &&
      !(match ty with
        | Solidity.Ty.tuple _ => true
        | _ => false) then
    Except.error (TypeError.invalidDataLocation ty location)
  else if Ty.needsDataLocation types ty && location.isNone then
    Except.error (TypeError.invalidDataLocation ty location)
  else if Ty.containsMapping types 64 ty then
    match location with
    | some Solidity.DataLocation.storage => Except.ok ()
    | _ => Except.error (TypeError.invalidDataLocation ty location)
  else
    Except.ok ()

structure FunctionSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  paramStorageRefs : List Bool := []
  paramDataLocations :
    List (Option Solidity.DataLocation) := []
  returns : List Ty := []
  returnStorageRefs : List Bool := []
  returnDataLocations :
    List (Option Solidity.DataLocation) := []
  visibility : Option Solidity.Visibility := none
  mutability : Solidity.StateMutability :=
    Solidity.StateMutability.nonpayable
  origin : Option Path := none
  -- Whether the declaration has an implementation body. Used to keep abstract
  -- (unimplemented) base functions out of `super.f()` resolution (G6). Defaults
  -- to `true` so signatures built for already-concrete callables are unaffected.
  hasBody : Bool := true
  deriving Repr

structure ModifierSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  paramStorageRefs : List Bool := []
  paramDataLocations :
    List (Option Solidity.DataLocation) := []
  deriving Repr

structure ErrorSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  deriving Repr

structure EventSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  anonymous : Bool := false
  deriving Repr

structure CheckEnv where
  types : TypeContext := {}
  vars : TypeEnv := []
  stateNames : List Name := []
  localNames : List Name := []
  blockScopeNames : List Name := []
  localStorageRefs : List Name := []
  localDataLocations : List (Name × Solidity.DataLocation) := []
  constantBindings : List (Name × Bool) := []
  immutableNames : List Name := []
  functions : List FunctionSig := []
  superFunctions : List FunctionSig := []
  modifiers : List ModifierSig := []
  modifierDecls : List Solidity.ModifierDecl := []
  usingDecls : List Solidity.UsingDecl := []
  errors : List ErrorSig := []
  events : List EventSig := []
  -- G8: names of the current contract's (own + inherited) NON-error members —
  -- functions, state vars, modifiers, events. A `revert E(...)` whose `E` names
  -- one of these resolves to a non-error declaration that shadows any free
  -- error `E`, which solc rejects (TypeError 1885 "has to be an error" /
  -- "not callable"). Excludes free functions/events (those do NOT shadow a
  -- contract-level error), so a contract error `E` alongside a free function
  -- `E` still reverts correctly.
  contractNonErrorMemberNames : List Name := []
  contractKind : Option Solidity.ContractKind := none
  currentContractAbstract : Bool := false
  currentContract : Option Path := none
  ancestorPaths : List Path := []
  currentMutability : Option Solidity.StateMutability := none
  currentVisibility : Option Solidity.Visibility := none
  returnTys : List Ty := []
  returnNames : List (Option Name) := []
  returnStorageRefs : List Bool := []
  returnDataLocations :
    List (Option Solidity.DataLocation) := []
  loopDepth : Nat := 0
  inModifier : Bool := false
  inUnchecked : Bool := false
  inConstructor : Bool := false
  inReceive : Bool := false
  -- CF2: names of the current scope's internal/private/free functions that
  -- PROVABLY always revert (never reach the function exit). solc's
  -- `ControlFlowRevertPruner` reroutes a call to such a callee to the revert
  -- node, so paths after the call cannot reach the function exit; the
  -- storage/calldata-pointer-return definite-assignment check (error 3464) then
  -- runs on the pruned CFG. A call to one of these names is treated as a
  -- terminating statement here (see `Stmt.pointerReturnFlowFuel`).
  alwaysRevertNames : List Name := []
  deriving Repr

def CheckEnv.lookupVar? (env : CheckEnv) (name : Name) : Option Ty :=
  Solidity.Executable.TypeEnv.lookup? env.vars name

def CheckEnv.isStateName (env : CheckEnv) (name : Name) : Bool :=
  Solidity.Executable.nameIn name env.stateNames

def CheckEnv.isLocalName (env : CheckEnv) (name : Name) : Bool :=
  Solidity.Executable.nameIn name env.localNames

def CheckEnv.isLocalStorageRef (env : CheckEnv) (name : Name) : Bool :=
  Solidity.Executable.nameIn name env.localStorageRefs

def CheckEnv.isPointerReturnName (env : CheckEnv) (name : Name) : Bool :=
  let rec go :
      List (Option Name) ->
      List (Option Solidity.DataLocation) -> Bool
    | some candidate :: nameRest, location :: locationRest =>
        (candidate == name &&
          (location == some Solidity.DataLocation.storage ||
            location == some Solidity.DataLocation.calldata)) ||
          go nameRest locationRest
    | _ :: nameRest, _ :: locationRest => go nameRest locationRest
    | _, _ => false
  go env.returnNames env.returnDataLocations

def CheckEnv.lookupLocalDataLocation? (env : CheckEnv)
    (name : Name) : Option Solidity.DataLocation :=
  let rec go : List (Name × Solidity.DataLocation) ->
      Option Solidity.DataLocation
    | [] => none
    | (candidate, location) :: rest =>
        if candidate == name then some location else go rest
  go env.localDataLocations

def CheckEnv.lookupConstantBinding? (env : CheckEnv)
    (name : Name) : Option Bool :=
  let rec go : List (Name × Bool) -> Option Bool
    | [] => none
    | (candidate, isConstant) :: rest =>
        if candidate == name then some isConstant else go rest
  go env.constantBindings

def CheckEnv.isConstantName (env : CheckEnv) (name : Name) : Bool :=
  match env.lookupConstantBinding? name with
  | some true => true
  | _ => false

def CheckEnv.isImmutableName (env : CheckEnv) (name : Name) : Bool :=
  !env.isLocalName name &&
    Solidity.Executable.nameIn name env.immutableNames

def CheckEnv.extendDataLocations (env : CheckEnv)
    (locations : List (Name × Solidity.DataLocation)) :
    CheckEnv :=
  { env with localDataLocations := locations ++ env.localDataLocations }

def CheckEnv.extendVarWithStorageRef (env : CheckEnv)
    (name : Name) (ty : Ty) (isStorageRef : Bool) :
    CheckEnv :=
  { env with
    vars := (name, ty) :: env.vars
    constantBindings := (name, false) :: env.constantBindings
    localNames := name :: env.localNames
    localStorageRefs :=
      if isStorageRef then name :: env.localStorageRefs
      else env.localStorageRefs }

def CheckEnv.extendVar (env : CheckEnv) (name : Name) (ty : Ty) :
    CheckEnv :=
  env.extendVarWithStorageRef name ty false

def CheckEnv.extendVars (env : CheckEnv) : List (Name × Ty) -> CheckEnv
  | [] => env
  | binding :: rest =>
      CheckEnv.extendVars (CheckEnv.extendVar env binding.fst binding.snd) rest

def CheckEnv.extendVarsWithStorageRefs (env : CheckEnv) :
    List (Name × Ty × Bool) -> CheckEnv
  | [] => env
  | (name, ty, isStorageRef) :: rest =>
      CheckEnv.extendVarsWithStorageRefs
        (env.extendVarWithStorageRef name ty isStorageRef) rest

def CheckEnv.inLibrary (env : CheckEnv) : Bool :=
  env.contractKind == some Solidity.ContractKind.library

def CheckEnv.enterLoop (env : CheckEnv) : CheckEnv :=
  { env with loopDepth := env.loopDepth + 1 }

def CheckEnv.enterModifier (env : CheckEnv) : CheckEnv :=
  { env with inModifier := true, inConstructor := false }

def CheckEnv.enterUnchecked (env : CheckEnv) : CheckEnv :=
  { env with inUnchecked := true }

def lookupModifierDeclIn? (target : Name) :
    List Solidity.ModifierDecl ->
    Option Solidity.ModifierDecl
  | [] => none
  | decl :: rest =>
      if decl.name == target then
        some decl
      else
        lookupModifierDeclIn? target rest

def CheckEnv.lookupModifierDecl? (env : CheckEnv) (target : Name) :
    Option Solidity.ModifierDecl :=
  lookupModifierDeclIn? target env.modifierDecls

def CheckEnv.isCurrentOrAncestorContract (env : CheckEnv)
    (path : Path) : Bool :=
  match env.currentContract with
  | some current =>
      TypeContext.pathMatches current path ||
        TypeContext.pathIn path env.ancestorPaths
  | none => false

def mutabilityAllowsStateRead :
    Option Solidity.StateMutability -> Bool
  | some Solidity.StateMutability.pure => false
  | _ => true

def mutabilityAllowsStateWrite :
    Option Solidity.StateMutability -> Bool
  | some Solidity.StateMutability.pure => false
  | some Solidity.StateMutability.view => false
  | _ => true

def mutabilityAllowsLogOrCreate :
    Option Solidity.StateMutability -> Bool :=
  mutabilityAllowsStateWrite

def mutabilityAllowsCall
    (caller : Option Solidity.StateMutability)
    (callee : Solidity.StateMutability) : Bool :=
  match caller with
  | some Solidity.StateMutability.pure =>
      callee == Solidity.StateMutability.pure
  | some Solidity.StateMutability.view =>
      callee == Solidity.StateMutability.pure ||
        callee == Solidity.StateMutability.view
  | _ => true

def requireStateReadAllowed (env : CheckEnv) :
    Except TypeError Unit :=
  require (mutabilityAllowsStateRead env.currentMutability)
    (TypeError.mutabilityViolation "state read in pure function")

def requireStateWriteAllowed (env : CheckEnv) :
    Except TypeError Unit :=
  require (mutabilityAllowsStateWrite env.currentMutability)
    (TypeError.mutabilityViolation "state write in view or pure function")

def requireLogOrCreateAllowed (env : CheckEnv) (what : String) :
    Except TypeError Unit :=
  require (mutabilityAllowsLogOrCreate env.currentMutability)
    (TypeError.mutabilityViolation what)

def requireCallMutabilityAllowed (env : CheckEnv)
    (callee : Solidity.StateMutability) :
    Except TypeError Unit :=
  require (mutabilityAllowsCall env.currentMutability callee)
    (TypeError.mutabilityViolation
      "call mutability exceeds current function mutability")

def callMemberMutability? (member : Name) :
    Option Solidity.StateMutability :=
  if member == "staticcall" then
    some Solidity.StateMutability.view
  else if member == "call" || member == "delegatecall" ||
      member == "send" || member == "transfer" then
    some Solidity.StateMutability.nonpayable
  else
    none

def requireCallExprMutabilityAllowed (env : CheckEnv)
    (fn : Solidity.Expr) : Except TypeError Unit :=
  match fn with
  | Solidity.Expr.member _ member =>
      match callMemberMutability? member with
      | some mutability => requireCallMutabilityAllowed env mutability
      | none => Except.ok ()
  | _ => Except.ok ()

def builtinIdentCallMutability? (name : Name) :
    Option Solidity.StateMutability :=
  if name == "gasleft" || name == "blockhash" || name == "blobhash" then
    some Solidity.StateMutability.view
  else
    none

def requireBuiltinIdentCallAllowed (env : CheckEnv) (name : Name) :
    Except TypeError Unit :=
  match builtinIdentCallMutability? name with
  | some mutability => requireCallMutabilityAllowed env mutability
  | none => Except.ok ()

def requireCancunOrLater (env : CheckEnv) (what : String) :
    Except TypeError Unit :=
  require env.types.evmVersion.cancunOrLater
    (TypeError.unsupported (what ++ " requires Cancun EVM"))

def requireConstantinopleOrLater (env : CheckEnv) (what : String) :
    Except TypeError Unit :=
  require env.types.evmVersion.constantinopleOrLater
    (TypeError.unsupported (what ++ " requires Constantinople EVM"))

def requireIstanbulOrLater (env : CheckEnv) (what : String) :
    Except TypeError Unit :=
  require env.types.evmVersion.istanbulOrLater
    (TypeError.unsupported (what ++ " requires Istanbul EVM"))

def requireLondonOrLater (env : CheckEnv) (what : String) :
    Except TypeError Unit :=
  require env.types.evmVersion.londonOrLater
    (TypeError.unsupported (what ++ " requires London EVM"))

def namesUniqueFrom (seen : List Name) : List Name -> Bool
  | [] => true
  | name :: rest =>
      !Solidity.Executable.nameIn name seen &&
        namesUniqueFrom (name :: seen) rest

def namesUnique (names : List Name) : Bool :=
  namesUniqueFrom [] names

def ensureUniqueNames (what : String) (names : List Name) :
    Except TypeError Unit :=
  match names with
  | [] => Except.ok ()
  | name :: rest =>
      if Solidity.Executable.nameIn name rest then
        Except.error (TypeError.duplicateName what name)
      else
        ensureUniqueNames what rest

def ensureNamesDisjointFrom (what : String) (reserved : List Name) :
    List Name -> Except TypeError Unit
  | [] => Except.ok ()
  | name :: rest => do
      require (!Solidity.Executable.nameIn name reserved)
        (TypeError.duplicateName what name)
      ensureNamesDisjointFrom what reserved rest

def Parameter.check (types : TypeContext)
    (param : Solidity.Parameter) :
    Except TypeError Unit :=
  checkLocationForTy types param.ty param.location

def Parameter.hasStorageLocation
    (param : Solidity.Parameter) : Bool :=
  param.location == some Solidity.DataLocation.storage

def Parameter.isStorageRef (types : TypeContext)
    (param : Solidity.Parameter) : Bool :=
  Ty.needsDataLocation types param.ty &&
    Parameter.hasStorageLocation param

def Parameters.check (types : TypeContext) :
    List Solidity.Parameter ->
    Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      Parameter.check types param
      Parameters.check types rest

def Parameters.namedTypes : List Solidity.Parameter ->
    List (Name × Ty)
  | [] => []
  | param :: rest =>
      match param.name with
      | some name => (name, param.ty) :: Parameters.namedTypes rest
      | none => Parameters.namedTypes rest

def Parameters.namedTypeStorageRefs (types : TypeContext) :
    List Solidity.Parameter -> List (Name × Ty × Bool)
  | [] => []
  | param :: rest =>
      match param.name with
      | some name =>
          (name, param.ty, Parameter.isStorageRef types param) ::
            Parameters.namedTypeStorageRefs types rest
      | none => Parameters.namedTypeStorageRefs types rest

def Parameters.namedDataLocations (types : TypeContext) :
    List Solidity.Parameter ->
    List (Name × Solidity.DataLocation)
  | [] => []
  | param :: rest =>
      match param.name, param.location with
      | some name, some location =>
          if Ty.needsDataLocation types param.ty then
            (name, location) :: Parameters.namedDataLocations types rest
          else
            Parameters.namedDataLocations types rest
      | _, _ => Parameters.namedDataLocations types rest

def Parameters.tys (params : List Solidity.Parameter) : List Ty :=
  params.map Solidity.Parameter.ty

def Parameters.storageRefFlags (types : TypeContext) :
    List Solidity.Parameter -> List Bool
  | [] => []
  | param :: rest =>
      Parameter.isStorageRef types param ::
        Parameters.storageRefFlags types rest

def Parameters.storageLocationFlags :
    List Solidity.Parameter -> List Bool
  | [] => []
  | param :: rest =>
      Parameter.hasStorageLocation param ::
        Parameters.storageLocationFlags rest

def Parameters.dataLocations :
    List Solidity.Parameter ->
    List (Option Solidity.DataLocation)
  | [] => []
  | param :: rest => param.location :: Parameters.dataLocations rest

def Parameters.anyStorageRef (types : TypeContext) :
    List Solidity.Parameter -> Bool
  | [] => false
  | param :: rest =>
      Parameter.isStorageRef types param ||
        Parameters.anyStorageRef types rest

def Parameters.anyCalldata : List Solidity.Parameter -> Bool
  | [] => false
  | param :: rest =>
      param.location == some Solidity.DataLocation.calldata ||
        Parameters.anyCalldata rest

def Parameters.firstMappingContainingTy? (types : TypeContext) :
    List Solidity.Parameter -> Option Ty
  | [] => none
  | param :: rest =>
      if Ty.containsMapping types 64 param.ty then
        some param.ty
      else
        Parameters.firstMappingContainingTy? types rest

def Parameters.firstNonAbiEncodableTy? (types : TypeContext) :
    List Solidity.Parameter -> Option Ty
  | [] => none
  | param :: rest =>
      if TypeContext.isAbiEncodable types param.ty then
        Parameters.firstNonAbiEncodableTy? types rest
      else
        some param.ty

def FunctionDecl.signature? (fn : Solidity.FunctionDecl) :
    Option FunctionSig :=
  match fn.kind, fn.name with
  | Solidity.FunctionKind.function, some name =>
      some
        { name := name
          params := Parameters.tys fn.params
          paramNames := fn.params.map Solidity.Parameter.name
          paramStorageRefs := Parameters.storageLocationFlags fn.params
          paramDataLocations := Parameters.dataLocations fn.params
          returns := Parameters.tys fn.returns
          returnStorageRefs := Parameters.storageLocationFlags fn.returns
          returnDataLocations := Parameters.dataLocations fn.returns
          visibility := fn.visibility
          mutability := fn.mutability
          hasBody := fn.body.isSome }
  | _, _ => none

def FunctionDecls.signatures : List Solidity.FunctionDecl ->
    List FunctionSig
  | [] => []
  | fn :: rest =>
      match FunctionDecl.signature? fn with
      | some sig => sig :: FunctionDecls.signatures rest
      | none => FunctionDecls.signatures rest

def FunctionDecl.constructorSignature? (fn : Solidity.FunctionDecl) :
    Option FunctionSig :=
  if fn.kind == Solidity.FunctionKind.constructor then
    some
      { name := "constructor"
        params := Parameters.tys fn.params
        paramNames := fn.params.map Solidity.Parameter.name
        paramStorageRefs := Parameters.storageLocationFlags fn.params
        paramDataLocations := Parameters.dataLocations fn.params
        returns := []
        returnStorageRefs := []
        returnDataLocations := []
        visibility := none
        mutability := fn.mutability }
  else
    none

def ContractItems.constructorSignature? :
    List Solidity.ContractItem -> Option FunctionSig
  | [] => none
  | Solidity.ContractItem.function fn :: rest =>
      match FunctionDecl.constructorSignature? fn with
      | some sig => some sig
      | none => ContractItems.constructorSignature? rest
  | _ :: rest => ContractItems.constructorSignature? rest

def ContractDecl.defaultConstructorSignature
    (decl : Solidity.ContractDecl) : FunctionSig :=
  { name := decl.name
    params := []
    paramNames := []
    returns := []
    visibility := none
    mutability := Solidity.StateMutability.nonpayable }

def ContractDecl.constructorSignature
    (decl : Solidity.ContractDecl) : FunctionSig :=
  match ContractItems.constructorSignature? decl.items with
  | some sig => sig
  | none => ContractDecl.defaultConstructorSignature decl

def ModifierDecl.signature (modifier : Solidity.ModifierDecl) :
    ModifierSig :=
  { name := modifier.name
    params := Parameters.tys modifier.params
    paramNames := modifier.params.map Solidity.Parameter.name
    paramStorageRefs := Parameters.storageLocationFlags modifier.params
    paramDataLocations := Parameters.dataLocations modifier.params }

def EventDecl.signature (event : Solidity.EventDecl) : EventSig :=
  { name := event.name
    params := event.params.map (fun param => param.ty)
    paramNames := event.params.map Solidity.EventParam.name
    anonymous := event.anonymous }

def ErrorDecl.signature (err : Solidity.ErrorDecl) : ErrorSig :=
  { name := err.name
    params := Parameters.tys err.params
    paramNames := err.params.map Solidity.Parameter.name }

def EnumDecl.hasCase (decl : Solidity.EnumDecl)
    (target : Name) : Bool :=
  Solidity.Executable.nameIn target decl.cases

def sameLength {α β : Type} : List α -> List β -> Bool
  | [], [] => true
  | _ :: xs, _ :: ys => sameLength xs ys
  | _, _ => false

abbrev ArgInfo := Option Name × Ty

namespace ArgInfos

def tys : List ArgInfo -> List Ty
  | [] => []
  | (_, ty) :: rest => ty :: tys rest

def anyNamed : List ArgInfo -> Bool
  | [] => false
  | (some _, _) :: _ => true
  | (none, _) :: rest => anyNamed rest

def anyPositional : List ArgInfo -> Bool
  | [] => false
  | (none, _) :: _ => true
  | (some _, _) :: rest => anyPositional rest

def namedNames : List ArgInfo -> List Name
  | [] => []
  | (some name, _) :: rest => name :: namedNames rest
  | (none, _) :: rest => namedNames rest

def lookupNamed? (target : Name) : List ArgInfo -> Option Ty
  | [] => none
  | (some name, ty) :: rest =>
      if name == target then some ty else lookupNamed? target rest
  | (none, _) :: rest => lookupNamed? target rest

def collectNamed? : List (Option Name) -> List ArgInfo -> Option (List Ty)
  | [], _ => some []
  | some name :: rest, infos => do
      let ty ← lookupNamed? name infos
      let tail ← collectNamed? rest infos
      some (ty :: tail)
  | none :: _, _ => none

def orderedTys? (paramNames : List (Option Name)) (infos : List ArgInfo) :
    Option (List Ty) :=
  if anyNamed infos then
    if anyPositional infos then
      none
    else if !(namesUnique (namedNames infos)) then
      none
    else if infos.length == paramNames.length then
      collectNamed? paramNames infos
    else
      none
  else
    some (tys infos)

end ArgInfos

def FunctionSig.paramsAccept : List Ty -> List Ty -> Bool
  | [], [] => true
  | actual :: actualRest, expected :: expectedRest =>
      Ty.canImplicitlyConvert actual expected &&
        FunctionSig.paramsAccept actualRest expectedRest
  | _, _ => false

def FunctionSig.matchesArgs (sig : FunctionSig) (args : List ArgInfo) : Bool :=
  match ArgInfos.orderedTys? sig.paramNames args with
  | some argTys => FunctionSig.paramsAccept argTys sig.params
  | none => false

def FunctionSig.lookupParamTyByName? :
    List (Option Name) -> List Ty -> Name -> Option Ty
  | some paramName :: nameRest, ty :: tyRest, target =>
      if paramName == target then
        some ty
      else
        FunctionSig.lookupParamTyByName? nameRest tyRest target
  | _ :: nameRest, _ :: tyRest, target =>
      FunctionSig.lookupParamTyByName? nameRest tyRest target
  | _, _, _ => none

def resultTyFromReturns : List Ty -> Ty
  | [] => Solidity.Ty.tuple []
  | [ty] => ty
  | tys => Solidity.Ty.tuple tys

def returnStorageRefsSingle : List Ty -> List Bool -> Bool
  | [_], [true] => true
  | _, _ => false

def returnDataLocationSingle? :
    List Ty -> List (Option Solidity.DataLocation) ->
    Option Solidity.DataLocation
  | [_], [location] => location
  | _, _ => none

def returnNamesAllNamed : List (Option Name) -> Bool
  | [] => true
  | some _ :: rest => returnNamesAllNamed rest
  | none :: _ => false

def FunctionSig.singleStorageRefReturn (sig : FunctionSig) : Bool :=
  returnStorageRefsSingle sig.returns sig.returnStorageRefs

def FunctionSig.sameSignature (a b : FunctionSig) : Bool :=
  a.name == b.name && a.params == b.params

def FunctionSig.sameResolutionTarget (a b : FunctionSig) : Bool :=
  a.name == b.name &&
    a.params == b.params &&
    a.paramNames == b.paramNames &&
    a.paramStorageRefs == b.paramStorageRefs &&
    a.returns == b.returns &&
    a.returnStorageRefs == b.returnStorageRefs &&
    a.visibility == b.visibility &&
    a.mutability == b.mutability &&
    a.origin == b.origin

def FunctionSig.withOrigin (origin : Path) (sig : FunctionSig) :
    FunctionSig :=
  { sig with origin := some origin }

def FunctionSig.withLibraryOrigin
    (library : Path) (sig : FunctionSig) : FunctionSig :=
  { sig with origin := some { segments := library.segments ++ [sig.name] } }

def FunctionSig.atAbiBoundary (types : TypeContext)
    (sig : FunctionSig) : FunctionSig :=
  { sig with
    paramStorageRefs := List.replicate sig.params.length false
    paramDataLocations := List.replicate sig.params.length none
    returnStorageRefs := List.replicate sig.returns.length false
    returnDataLocations :=
      sig.returns.map (fun ty =>
        if Ty.needsDataLocation types ty then
          some Solidity.DataLocation.memory
        else
          none) }

def libraryAbiParamDataLocations :
    List Bool -> List (Option Solidity.DataLocation) ->
    List (Option Solidity.DataLocation)
  | [], _ => []
  | needsStorage :: storageRest, locations =>
      let location :=
        if needsStorage then
          some Solidity.DataLocation.storage
        else
          none
      location ::
        libraryAbiParamDataLocations storageRest locations.tail

def FunctionSig.externallyCallable (sig : FunctionSig) : Bool :=
  sig.visibility == some Solidity.Visibility.public_ ||
    sig.visibility == some Solidity.Visibility.external_

def FunctionSig.atLibraryCallBoundary (types : TypeContext)
    (sig : FunctionSig) : FunctionSig :=
  if sig.externallyCallable then
    let abiSig := sig.atAbiBoundary types
    { abiSig with
      paramStorageRefs := sig.paramStorageRefs
      paramDataLocations :=
        libraryAbiParamDataLocations sig.paramStorageRefs
          sig.paramDataLocations }
  else
    sig

def FunctionSig.abiParamTypes? (types : TypeContext)
    (sig : FunctionSig) : Option (List String) :=
  TypeContext.abiCanonicalList? types sig.params

def FunctionSig.abiSignature? (types : TypeContext)
    (sig : FunctionSig) : Option String := do
  let params ← sig.abiParamTypes? types
  some
    (sig.name ++ "(" ++
      Solidity.Executable.joinStringsWith "," params ++ ")")

def FunctionSig.abiSelector? (types : TypeContext)
    (sig : FunctionSig) : Option SolidCore.Solidity.Shared.Word := do
  let signature ← sig.abiSignature? types
  some (SolidCore.Solidity.Source.ABI.selectorFromSignature signature)

def FunctionSig.sameExternalAbiSignature
    (types : TypeContext) (a b : FunctionSig) : Bool :=
  if a.name == b.name && a.externallyCallable && b.externallyCallable then
    match a.abiParamTypes? types, b.abiParamTypes? types with
    | some aParams, some bParams => aParams == bParams
    | _, _ => false
  else
    false

def FunctionSig.sameExternalAbiSelector
    (types : TypeContext) (a b : FunctionSig) : Bool :=
  if a.externallyCallable && b.externallyCallable then
    match a.abiSelector? types, b.abiSelector? types with
    | some aSelector, some bSelector => aSelector == bSelector
    | _, _ => false
  else
    false

def FunctionSig.externalAbiSelectorEntry? (types : TypeContext)
    (sig : FunctionSig) : Option (SolidCore.Solidity.Shared.Word × Name) :=
  if sig.externallyCallable then do
    let selector ← sig.abiSelector? types
    some (selector, sig.name)
  else
    none

def FunctionSigs.ensureNoDuplicateSignatures :
    List FunctionSig -> Except TypeError Unit
  | [] => Except.ok ()
  | sig :: rest => do
      if rest.any (fun other => FunctionSig.sameSignature sig other) then
        Except.error (TypeError.duplicateSignature sig.name)
      else
        FunctionSigs.ensureNoDuplicateSignatures rest

def FunctionSigs.ensureNoDuplicateExternalAbiSignatures
    (types : TypeContext) : List FunctionSig -> Except TypeError Unit
  | [] => Except.ok ()
  | sig :: rest => do
      if rest.any (fun other =>
          FunctionSig.sameExternalAbiSignature types sig other) then
        Except.error (TypeError.duplicateSignature sig.name)
      else
        FunctionSigs.ensureNoDuplicateExternalAbiSignatures types rest

def FunctionSigs.externalAbiSelectorEntries
    (types : TypeContext) (sigs : List FunctionSig) :
    List (SolidCore.Solidity.Shared.Word × Name) :=
  sigs.filterMap (FunctionSig.externalAbiSelectorEntry? types)

def FunctionSigs.ensureNoDuplicateExternalAbiSelectorEntries :
    List (SolidCore.Solidity.Shared.Word × Name) -> Except TypeError Unit
  | [] => Except.ok ()
  | (selector, name) :: rest => do
      if rest.any (fun other => other.fst == selector) then
        Except.error (TypeError.duplicateSignature name)
      else
        FunctionSigs.ensureNoDuplicateExternalAbiSelectorEntries rest

def FunctionSigs.ensureNoDuplicateExternalAbiSelectors
    (types : TypeContext) (sigs : List FunctionSig) : Except TypeError Unit :=
  FunctionSigs.ensureNoDuplicateExternalAbiSelectorEntries
    (FunctionSigs.externalAbiSelectorEntries types sigs)

def FunctionSigs.resolveLoop (target : Name) (args : List ArgInfo) :
    Option FunctionSig -> List FunctionSig ->
    Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesArgs args then
        match found? with
        | none => FunctionSigs.resolveLoop target args (some sig) rest
        | some found =>
            if FunctionSig.sameResolutionTarget found sig then
              FunctionSigs.resolveLoop target args (some found) rest
            else
              Except.error (TypeError.ambiguousFunction target)
      else
        FunctionSigs.resolveLoop target args found? rest

def FunctionSigs.resolve (functions : List FunctionSig)
    (target : Name) (args : List ArgInfo) : Except TypeError FunctionSig :=
  FunctionSigs.resolveLoop target args none functions

def FunctionSig.internallyCallable (sig : FunctionSig) : Bool :=
  !(sig.visibility == some Solidity.Visibility.external_)

def FunctionSig.nonPrivate (sig : FunctionSig) : Bool :=
  !(sig.visibility == some Solidity.Visibility.private_)

def FunctionSig.internalFunctionValueTy? (sig : FunctionSig) :
    Option Ty :=
  if sig.internallyCallable then
    some
      (Solidity.Ty.functionWithLocations sig.params
        sig.paramDataLocations sig.returns sig.returnDataLocations
        sig.mutability Solidity.Visibility.internal_)
  else
    none

def canonicalExternalFunctionDataLocations :
    List (Option Solidity.DataLocation) ->
    List (Option Solidity.DataLocation) :=
  List.map (fun location =>
    if location.isSome then
      some Solidity.DataLocation.memory
    else
      none)

def FunctionSig.externalFunctionValueTy? (sig : FunctionSig) :
    Option Ty :=
  if sig.externallyCallable then
    some
      (Solidity.Ty.functionWithLocations sig.params
        (canonicalExternalFunctionDataLocations sig.paramDataLocations)
        sig.returns
        (canonicalExternalFunctionDataLocations sig.returnDataLocations)
        sig.mutability Solidity.Visibility.external_)
  else
    none

def FunctionSig.internalFunctionValueAssignableTo
    (types : TypeContext) (expected : Ty) (sig : FunctionSig) : Bool :=
  match FunctionSig.internalFunctionValueTy? sig with
  | some actual => TypeContext.canImplicitlyConvert types actual expected
  | none => false

namespace FunctionSigs

def resolveInternalFunctionValueByNameLoop
    (target : Name) :
    Option FunctionSig -> List FunctionSig -> Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.internallyCallable then
        match found? with
        | none =>
            resolveInternalFunctionValueByNameLoop target (some sig) rest
        | some found =>
            -- The same internal function may appear more than once in the
            -- visible-signatures list (e.g. a modifier body's environment
            -- unions `functionSigsForModifierBodies` with the caller's own
            -- `functions`); a genuine duplicate of the SAME resolution target
            -- is not an ambiguity (mirrors `resolveExternalFunctionValueByName`
            -- and the call-site `FunctionSigs.resolveLoop`).
            if FunctionSig.sameResolutionTarget found sig then
              resolveInternalFunctionValueByNameLoop target (some found) rest
            else
              Except.error (TypeError.ambiguousFunction target)
      else
        resolveInternalFunctionValueByNameLoop target found? rest

def resolveInternalFunctionValueByName
    (functions : List FunctionSig) (target : Name) :
    Except TypeError FunctionSig :=
  resolveInternalFunctionValueByNameLoop target none functions

def resolveExternalFunctionValueByNameLoop
    (target : Name) :
    Option FunctionSig -> List FunctionSig -> Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.externallyCallable then
        match found? with
        | none =>
            resolveExternalFunctionValueByNameLoop target (some sig) rest
        | some found =>
            if FunctionSig.sameResolutionTarget found sig then
              resolveExternalFunctionValueByNameLoop target (some found) rest
            else
              Except.error (TypeError.ambiguousFunction target)
      else
        resolveExternalFunctionValueByNameLoop target found? rest

def resolveExternalFunctionValueByName
    (functions : List FunctionSig) (target : Name) :
    Except TypeError FunctionSig :=
  resolveExternalFunctionValueByNameLoop target none functions

def resolveInternalFunctionValueAssignableTo (types : TypeContext)
    (functions : List FunctionSig) (target : Name) (expected : Ty) :
    Except TypeError FunctionSig := do
  let sig ← resolveInternalFunctionValueByName functions target
  if FunctionSig.internalFunctionValueAssignableTo types expected sig then
      Except.ok sig
  else
    match FunctionSig.internalFunctionValueTy? sig with
    | some actual => Except.error (TypeError.expectedType expected actual)
    | none => Except.error (TypeError.unknownFunction target)

def containsSameSignature (target : FunctionSig) : List FunctionSig -> Bool
  | [] => false
  | sig :: rest =>
      FunctionSig.sameSignature target sig ||
        containsSameSignature target rest

def addIfNewSignature (sigs : List FunctionSig)
    (sig : FunctionSig) : List FunctionSig :=
  if containsSameSignature sig sigs then
    sigs
  else
    sigs ++ [sig]

def addExternalIfNewSignature (sigs : List FunctionSig)
    (sig : FunctionSig) : List FunctionSig :=
  if sig.externallyCallable then
    addIfNewSignature sigs sig
  else
    sigs

def addNonPrivateIfNewSignature (sigs : List FunctionSig)
    (sig : FunctionSig) : List FunctionSig :=
  if sig.nonPrivate then
    addIfNewSignature sigs sig
  else
    sigs

def addExternalAllIfNewSignature (sigs : List FunctionSig) :
    List FunctionSig -> List FunctionSig
  | [] => sigs
  | sig :: rest =>
      addExternalAllIfNewSignature (addExternalIfNewSignature sigs sig) rest

def addNonPrivateAllIfNewSignature (sigs : List FunctionSig) :
    List FunctionSig -> List FunctionSig
  | [] => sigs
  | sig :: rest =>
      addNonPrivateAllIfNewSignature
        (addNonPrivateIfNewSignature sigs sig) rest

def nonPrivate : List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      if sig.nonPrivate then
        sig :: nonPrivate rest
      else
        nonPrivate rest

def withOrigin (origin : Path) : List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      FunctionSig.withOrigin origin sig :: withOrigin origin rest

def withLibraryOrigin
    (library : Path) : List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      FunctionSig.withLibraryOrigin library sig ::
        withLibraryOrigin library rest

def atAbiBoundary (types : TypeContext) :
    List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      sig.atAbiBoundary types :: atAbiBoundary types rest

def atLibraryCallBoundary (types : TypeContext) :
    List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      sig.atLibraryCallBoundary types ::
        atLibraryCallBoundary types rest

end FunctionSigs

def ContractDecl.directFunctionSigs
    (decl : Solidity.ContractDecl) : List FunctionSig :=
  decl.items.filterMap
    (fun item =>
      match item with
      | Solidity.ContractItem.function fn =>
          FunctionDecl.signature? fn
      | _ => none)

def ContractItem.localTypeName? :
    Solidity.ContractItem -> Option Name
  | Solidity.ContractItem.structDecl decl => some decl.name
  | Solidity.ContractItem.enumDecl decl => some decl.name
  | Solidity.ContractItem.userValueTypeDecl decl => some decl.name
  | _ => none

def localTypePathQualified (contractName : Name)
    (localTypeNames : List Name) (path : Path) : Path :=
  match path.segments with
  | [name] =>
      if localTypeNames.contains name then
        TypeContext.qualifiedPath contractName name
      else
        path
  | _ => path

mutual

def Ty.qualifyLocalUserTypes (contractName : Name)
    (localTypeNames : List Name) : Ty -> Ty
  | Solidity.Ty.array element size =>
      Solidity.Ty.array
        (Ty.qualifyLocalUserTypes contractName localTypeNames element) size
  | Solidity.Ty.mapping key value =>
      Solidity.Ty.mapping
        (Ty.qualifyLocalUserTypes contractName localTypeNames key)
        (Ty.qualifyLocalUserTypes contractName localTypeNames value)
  | Solidity.Ty.tuple tys =>
      Solidity.Ty.tuple
        (Tys.qualifyLocalUserTypes contractName localTypeNames tys)
  | Solidity.Ty.user path =>
      Solidity.Ty.user
        (localTypePathQualified contractName localTypeNames path)
  | Solidity.Ty.functionWithLocations params paramLocations returns
      returnLocations mutability visibility =>
      Solidity.Ty.functionWithLocations
        (Tys.qualifyLocalUserTypes contractName localTypeNames params)
        paramLocations
        (Tys.qualifyLocalUserTypes contractName localTypeNames returns)
        returnLocations mutability visibility
  | ty => ty

def Tys.qualifyLocalUserTypes (contractName : Name)
    (localTypeNames : List Name) : List Ty -> List Ty
  | [] => []
  | ty :: rest =>
      Ty.qualifyLocalUserTypes contractName localTypeNames ty ::
        Tys.qualifyLocalUserTypes contractName localTypeNames rest

end

def FunctionSig.qualifyLocalUserTypes (contractName : Name)
    (localTypeNames : List Name) (sig : FunctionSig) : FunctionSig :=
  { sig with
    params := Tys.qualifyLocalUserTypes contractName localTypeNames sig.params
    returns :=
      Tys.qualifyLocalUserTypes contractName localTypeNames sig.returns }

def ContractDecl.localTypeNames
    (decl : Solidity.ContractDecl) : List Name :=
  decl.items.filterMap ContractItem.localTypeName?

def ContractDecl.directFunctionSigsQualifiedLocalTypes
    (decl : Solidity.ContractDecl) : List FunctionSig :=
  let localTypeNames := ContractDecl.localTypeNames decl
  (ContractDecl.directFunctionSigs decl).map
    (FunctionSig.qualifyLocalUserTypes decl.name localTypeNames)

def CheckEnv.localTypeQualifierContract? (env : CheckEnv)
    (structPath : Path) : Option Name :=
  match structPath.segments with
  | contractName :: _ =>
      match env.types.lookupContractDecl? (TypeContext.pathOfName contractName) with
      | some _ => some contractName
      | none =>
          match env.currentContract, structPath.segments with
          | some current, [_] =>
              match current.segments with
              | [currentName] => some currentName
              | _ => none
          | _, _ => none
  | [] => none

def CheckEnv.qualifyStructFieldTy (env : CheckEnv)
    (structPath : Path) (ty : Ty) : Ty :=
  match env.localTypeQualifierContract? structPath with
  | some contractName =>
      match env.types.lookupContractDecl? (TypeContext.pathOfName contractName) with
      | some contract =>
          Ty.qualifyLocalUserTypes contractName
            (ContractDecl.localTypeNames contract) ty
      | none => ty
  | none => ty

def TypeContext.firstKnownQualifiedUserPath? (types : TypeContext)
    (name : Name) : List Path -> Option Path
  | [] => none
  | { segments := [contractName] } :: rest =>
      let candidate := TypeContext.qualifiedPath contractName name
      if types.isKnownPath candidate then
        some candidate
      else
        TypeContext.firstKnownQualifiedUserPath? types name rest
  | _ :: rest => TypeContext.firstKnownQualifiedUserPath? types name rest

def CheckEnv.qualifyVisibleLocalUserPath (env : CheckEnv)
    (path : Path) : Path :=
  match path.segments with
  | [name] =>
      let candidateContracts :=
        match env.currentContract with
        | some current => current :: env.ancestorPaths
        | none => env.ancestorPaths
      match env.types.firstKnownQualifiedUserPath? name candidateContracts with
      | some qualified => qualified
      | none => path
  | _ => path

mutual

def Ty.qualifyVisibleLocalUserTypes (env : CheckEnv) : Ty -> Ty
  | Solidity.Ty.array element size =>
      Solidity.Ty.array
        (Ty.qualifyVisibleLocalUserTypes env element) size
  | Solidity.Ty.mapping key value =>
      Solidity.Ty.mapping
        (Ty.qualifyVisibleLocalUserTypes env key)
        (Ty.qualifyVisibleLocalUserTypes env value)
  | Solidity.Ty.tuple tys =>
      Solidity.Ty.tuple
        (Tys.qualifyVisibleLocalUserTypes env tys)
  | Solidity.Ty.user path =>
      Solidity.Ty.user
        (env.qualifyVisibleLocalUserPath path)
  | Solidity.Ty.functionWithLocations params paramLocations returns
      returnLocations mutability visibility =>
      Solidity.Ty.functionWithLocations
        (Tys.qualifyVisibleLocalUserTypes env params)
        paramLocations
        (Tys.qualifyVisibleLocalUserTypes env returns)
        returnLocations mutability visibility
  | ty => ty

def Tys.qualifyVisibleLocalUserTypes (env : CheckEnv) : List Ty -> List Ty
  | [] => []
  | ty :: rest =>
      Ty.qualifyVisibleLocalUserTypes env ty ::
        Tys.qualifyVisibleLocalUserTypes env rest

end

def CheckEnv.qualifyCurrentLocalUserTypes (env : CheckEnv) (ty : Ty) : Ty :=
  Ty.qualifyVisibleLocalUserTypes env ty

def StateVarDecl.publicGetterFunctionSig?
    (types : TypeContext) (decl : Solidity.StateVarDecl) :
    Option FunctionSig :=
  match decl.visibility with
  | some Solidity.Visibility.public_ => do
      let shape ← Ty.publicGetterShape? types 64 decl.ty
      some
        { name := decl.name
          params := shape.fst
          paramNames := List.replicate shape.fst.length none
          paramStorageRefs := List.replicate shape.fst.length false
          returns := shape.snd
          returnStorageRefs := List.replicate shape.snd.length false
          visibility := some Solidity.Visibility.external_
          mutability := Solidity.StateMutability.view }
  | _ => none

def ContractDecl.directPublicGetterSigs
    (types : TypeContext) (decl : Solidity.ContractDecl) :
    List FunctionSig :=
  let localTypeNames := ContractDecl.localTypeNames decl
  decl.items.filterMap
    (fun item =>
      match item with
      | Solidity.ContractItem.stateVar stateVar =>
          match StateVarDecl.publicGetterFunctionSig? types stateVar with
          | some sig =>
              some
                (FunctionSig.qualifyLocalUserTypes
                  decl.name localTypeNames sig)
          | none => none
      | _ => none)

def ContractDecl.directExternalFunctionSigs
    (types : TypeContext) (decl : Solidity.ContractDecl) :
    List FunctionSig :=
  ContractDecl.directFunctionSigsQualifiedLocalTypes decl ++
    ContractDecl.directPublicGetterSigs types decl

def ContractDecl.directModifierDecls
    (decl : Solidity.ContractDecl) :
    List Solidity.ModifierDecl :=
  decl.items.filterMap
    (fun item =>
      match item with
      | Solidity.ContractItem.modifierDecl modifier =>
          some modifier
      | _ => none)

namespace ModifierDecls

def containsName (name : Name) :
    List Solidity.ModifierDecl -> Bool
  | [] => false
  | modifier :: rest =>
      modifier.name == name || containsName name rest

def addIfNewName (modifiers : List Solidity.ModifierDecl)
    (modifier : Solidity.ModifierDecl) :
    List Solidity.ModifierDecl :=
  if containsName modifier.name modifiers then
    modifiers
  else
    modifiers ++ [modifier]

def addAllIfNewName (modifiers : List Solidity.ModifierDecl) :
    List Solidity.ModifierDecl ->
    List Solidity.ModifierDecl
  | [] => modifiers
  | modifier :: rest =>
      addAllIfNewName (addIfNewName modifiers modifier) rest

def signatures (modifiers : List Solidity.ModifierDecl) :
    List ModifierSig :=
  modifiers.map ModifierDecl.signature

end ModifierDecls

def ContractDecl.modifierDeclsFromOrderFrom
    (modifiers : List Solidity.ModifierDecl) :
    List Solidity.ContractDecl ->
    List Solidity.ModifierDecl
  | [] => modifiers
  | decl :: rest =>
      ContractDecl.modifierDeclsFromOrderFrom
        (ModifierDecls.addAllIfNewName modifiers
          (ContractDecl.directModifierDecls decl))
        rest

def ContractDecl.modifierDeclsFromOrder
    (order : List Solidity.ContractDecl) :
    List Solidity.ModifierDecl :=
  ContractDecl.modifierDeclsFromOrderFrom [] order

def ContractDecl.externalFunctionSigsFromOrderFrom (types : TypeContext)
    (sigs : List FunctionSig) :
    List Solidity.ContractDecl -> List FunctionSig
  | [] => sigs
  | decl :: rest =>
      ContractDecl.externalFunctionSigsFromOrderFrom types
        (FunctionSigs.addExternalAllIfNewSignature sigs
          (ContractDecl.directExternalFunctionSigs types decl))
        rest

def ContractDecl.externalFunctionSigsFromOrder (types : TypeContext)
    (order : List Solidity.ContractDecl) : List FunctionSig :=
  ContractDecl.externalFunctionSigsFromOrderFrom types [] order

def ContractDecl.nonPrivateFunctionSigsFromOrderFrom
    (sigs : List FunctionSig) :
    List Solidity.ContractDecl -> List FunctionSig
  | [] => sigs
  | decl :: rest =>
      ContractDecl.nonPrivateFunctionSigsFromOrderFrom
        (FunctionSigs.addNonPrivateAllIfNewSignature sigs
          (ContractDecl.directFunctionSigsQualifiedLocalTypes decl))
        rest

def ContractDecl.nonPrivateFunctionSigsFromOrder
    (order : List Solidity.ContractDecl) : List FunctionSig :=
  ContractDecl.nonPrivateFunctionSigsFromOrderFrom [] order

def TypeContext.lookupContractExternalFunctionSigs?
    (types : TypeContext) (path : Path) : Option (List FunctionSig) := do
  let decl ← types.lookupContractDecl? path
  let order ←
    Solidity.Executable.ContractDecl.dispatchOrder?
      (types.contractDecls.map Prod.snd) decl
  some
    (FunctionSigs.atAbiBoundary types
      (ContractDecl.externalFunctionSigsFromOrder types order))

def TypeContext.resolveContractMemberFunction
    (types : TypeContext) (path : Path) (member : Name)
    (args : List ArgInfo) : Except TypeError FunctionSig :=
  match types.lookupContractExternalFunctionSigs? path with
  | some sigs => FunctionSigs.resolve sigs member args
  | none => Except.error (TypeError.unknownFunction member)

def TypeContext.resolveContractExternalFunctionValue
    (types : TypeContext) (path : Path) (member : Name) :
    Except TypeError FunctionSig :=
  match types.lookupContractExternalFunctionSigs? path with
  | some sigs => FunctionSigs.resolveExternalFunctionValueByName sigs member
  | none => Except.error (TypeError.unknownFunction member)

/-- Member-form internal-function VALUE resolution (boundary-completion arc,
    member-form residue): `Lib.f` / `Contract.f` used in value position names
    the same internal-function-pointer value a bare identifier `f` would, when
    `f` is an internally-callable (non-private, non-external) function directly
    declared on the named library/contract. Returns the resolved signature so
    the caller can project `FunctionSig.internalFunctionValueTy?`. -/
def TypeContext.resolveInternalFunctionValueMember?
    (types : TypeContext) (path : Path) (member : Name) :
    Option FunctionSig :=
  match types.lookupContractDecl? path with
  | some decl =>
      let sigs :=
        (ContractDecl.directFunctionSigsQualifiedLocalTypes decl).filter
          FunctionSig.nonPrivate
      match FunctionSigs.resolveInternalFunctionValueByName sigs member with
      | Except.ok sig =>
          -- A LIBRARY member is an internal-function-pointer value only when the
          -- library function is declared `internal`; `public`/`external` library
          -- functions are special (delegatecall entry points) and solc rejects
          -- converting them to a function type. A contract member may be any
          -- internally-callable (internal or public) function.
          let visibilityOk :=
            if decl.kind == Solidity.ContractKind.library then
              sig.visibility == some Solidity.Visibility.internal_
            else
              FunctionSig.internallyCallable sig
          if visibilityOk then some sig else none
      | Except.error _ => none
  | none => none

def ModifierSig.paramsAccept : List Ty -> List Ty -> Bool
  | [], [] => true
  | actual :: actualRest, expected :: expectedRest =>
      Ty.canImplicitlyConvert actual expected &&
        ModifierSig.paramsAccept actualRest expectedRest
  | _, _ => false

def ModifierSig.matchesArgs (sig : ModifierSig) (args : List ArgInfo) : Bool :=
  match ArgInfos.orderedTys? sig.paramNames args with
  | some argTys => ModifierSig.paramsAccept argTys sig.params
  | none => false

def ModifierSigs.resolveLoop (target : Name) (args : List ArgInfo) :
    Option ModifierSig -> List ModifierSig ->
    Except TypeError ModifierSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesArgs args then
        match found? with
        | none => ModifierSigs.resolveLoop target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        ModifierSigs.resolveLoop target args found? rest

def ModifierSigs.resolve (modifiers : List ModifierSig)
    (target : Name) (args : List ArgInfo) : Except TypeError ModifierSig :=
  ModifierSigs.resolveLoop target args none modifiers

def EventSig.matchesArgs (sig : EventSig) (args : List ArgInfo) : Bool :=
  match ArgInfos.orderedTys? sig.paramNames args with
  | some argTys => FunctionSig.paramsAccept argTys sig.params
  | none => false

def EventSig.abiParamTypes? (types : TypeContext)
    (sig : EventSig) : Option (List String) :=
  TypeContext.abiCanonicalList? types sig.params

def EventSig.sameAbiSignature
    (types : TypeContext) (a b : EventSig) : Bool :=
  if a.name == b.name then
    match a.abiParamTypes? types, b.abiParamTypes? types with
    | some aParams, some bParams => aParams == bParams
    | _, _ => false
  else
    false

def EventSigs.ensureNoDuplicateAbiSignatures
    (types : TypeContext) : List EventSig -> Except TypeError Unit
  | [] => Except.ok ()
  | sig :: rest => do
      if rest.any (fun other => EventSig.sameAbiSignature types sig other) then
        Except.error (TypeError.duplicateSignature sig.name)
      else
        EventSigs.ensureNoDuplicateAbiSignatures types rest

def EventSigs.ensureNoDuplicateAbiSignaturesAgainst
    (types : TypeContext) (inherited : List EventSig) :
    List EventSig -> Except TypeError Unit
  | [] => Except.ok ()
  | sig :: rest => do
      if inherited.any (fun other => EventSig.sameAbiSignature types sig other) then
        Except.error (TypeError.duplicateSignature sig.name)
      else
        EventSigs.ensureNoDuplicateAbiSignaturesAgainst
          types inherited rest

def EventSigs.withoutNamesOf (locals : List EventSig) :
    List EventSig -> List EventSig
  | [] => []
  | sig :: rest =>
      if locals.any (fun localSig => localSig.name == sig.name) then
        EventSigs.withoutNamesOf locals rest
      else
        sig :: EventSigs.withoutNamesOf locals rest

def EventSigs.resolveLoop (target : Name) (args : List ArgInfo) :
    Option EventSig -> List EventSig -> Except TypeError EventSig
  | none, [] => Except.error (TypeError.unknownEvent target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesArgs args then
        match found? with
        | none => EventSigs.resolveLoop target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        EventSigs.resolveLoop target args found? rest

def EventSigs.resolve (events : List EventSig)
    (target : Name) (args : List ArgInfo) : Except TypeError EventSig :=
  EventSigs.resolveLoop target args none events

def EventSigs.resolveByNameLoop (target : Name) :
    Option EventSig -> List EventSig -> Except TypeError EventSig
  | none, [] => Except.error (TypeError.unknownEvent target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target then
        match found? with
        | none => EventSigs.resolveByNameLoop target (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        EventSigs.resolveByNameLoop target found? rest

def EventSigs.resolveByName (events : List EventSig) (target : Name) :
    Except TypeError EventSig :=
  EventSigs.resolveByNameLoop target none events

def ErrorSig.matchesArgs (sig : ErrorSig) (args : List ArgInfo) : Bool :=
  match ArgInfos.orderedTys? sig.paramNames args with
  | some argTys => FunctionSig.paramsAccept argTys sig.params
  | none => false

def ErrorSigs.resolveLoop (target : Name) (args : List ArgInfo) :
    Option ErrorSig -> List ErrorSig -> Except TypeError ErrorSig
  | none, [] => Except.error (TypeError.unknownError target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesArgs args then
        match found? with
        | none => ErrorSigs.resolveLoop target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        ErrorSigs.resolveLoop target args found? rest

def ErrorSigs.resolve (errors : List ErrorSig)
    (target : Name) (args : List ArgInfo) : Except TypeError ErrorSig :=
  ErrorSigs.resolveLoop target args none errors

def ErrorSigs.resolveByNameLoop (target : Name) :
    Option ErrorSig -> List ErrorSig -> Except TypeError ErrorSig
  | none, [] => Except.error (TypeError.unknownError target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target then
        match found? with
        | none => ErrorSigs.resolveByNameLoop target (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        ErrorSigs.resolveByNameLoop target found? rest

def ErrorSigs.resolveByName (errors : List ErrorSig) (target : Name) :
    Except TypeError ErrorSig :=
  ErrorSigs.resolveByNameLoop target none errors

def ErrorSigs.withoutNamesOf (locals : List ErrorSig) :
    List ErrorSig -> List ErrorSig
  | [] => []
  | sig :: rest =>
      if locals.any (fun localSig => localSig.name == sig.name) then
        ErrorSigs.withoutNamesOf locals rest
      else
        sig :: ErrorSigs.withoutNamesOf locals rest

-- OV1: solc removes a file-level (free) function from a contract's name scope
-- whenever a member function (the contract's own — any visibility — or a
-- non-private inherited one) declares the SAME NAME (name-based shadowing,
-- warning 2519). A single same-named member removes ALL free overloads of that
-- name. Mirror `ErrorSigs.withoutNamesOf`/`EventSigs.withoutNamesOf`.
def FunctionSigs.withoutNamesOf (locals : List FunctionSig) :
    List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      if locals.any (fun localSig => localSig.name == sig.name) then
        FunctionSigs.withoutNamesOf locals rest
      else
        sig :: FunctionSigs.withoutNamesOf locals rest

def Expr.directIdentName? : Solidity.Expr -> Option Name
  | Solidity.Expr.ident name => some name
  | _ => none

structure CheckedExpr where
  source : Solidity.Expr
  ty : Ty
  lvalue : Bool := false
  stateLValue : Bool := false
  storageRefs : List Bool := []
  dataLocations : List (Option Solidity.DataLocation) := []
  dataLocation? : Option Solidity.DataLocation := none
  arraySlice : Bool := false
  deriving Repr

def FunctionSig.checkedResult (sig : FunctionSig)
    (source : Solidity.Expr) : CheckedExpr :=
  let storageRef := sig.singleStorageRefReturn
  let location :=
    match returnDataLocationSingle? sig.returns sig.returnDataLocations with
    | some location => some location
    | none =>
        if storageRef then
          some Solidity.DataLocation.storage
        else
          none
  { source := source
    ty := resultTyFromReturns sig.returns
    lvalue := false
    stateLValue := storageRef
    storageRefs := sig.returnStorageRefs
    dataLocations := sig.returnDataLocations
    dataLocation? := location }

def CheckedExpr.locationIsCalldata (expr : CheckedExpr) : Bool :=
  expr.dataLocation? == some Solidity.DataLocation.calldata

def CheckedExpr.locationAssignableTo
    (expr : CheckedExpr)
    (expected : Option Solidity.DataLocation) : Bool :=
  match expected with
  | some Solidity.DataLocation.storage => expr.stateLValue
  | some Solidity.DataLocation.calldata => expr.locationIsCalldata
  | _ => true

def CheckedExpr.expectLocationAssignableTo
    (expr : CheckedExpr) (expectedTy : Ty)
    (expected : Option Solidity.DataLocation) :
    Except TypeError Unit :=
  require (expr.locationAssignableTo expected)
    (TypeError.invalidDataLocation expectedTy expected)

def CheckedExpr.expectWritableLocation (expr : CheckedExpr)
    (target : Solidity.Expr) : Except TypeError Unit :=
  require
    (!(expr.locationIsCalldata && (Expr.directIdentName? target).isNone))
    (TypeError.invalidDataLocation expr.ty
      (some Solidity.DataLocation.calldata))

def CheckedExpr.expectStorageMutationTarget (expr : CheckedExpr)
    (target : Solidity.Expr) : Except TypeError Unit := do
  require (expr.lvalue || expr.stateLValue) (TypeError.expectedLValue target)
  require
    (expr.dataLocation? == some Solidity.DataLocation.storage)
    (TypeError.invalidDataLocation expr.ty expr.dataLocation?)

def CheckEnv.assignmentRebindsStoragePointer
    (env : CheckEnv) (target : Solidity.Expr)
    (actualStorageRef : Bool) : Bool :=
  match Expr.directIdentName? target with
  | some name =>
      actualStorageRef &&
        (env.isPointerReturnName name || env.isLocalStorageRef name)
  | none => false

def CheckEnv.requireNoMappingStorageCopy
    (env : CheckEnv) (target : Solidity.Expr)
    (targetChecked : CheckedExpr) (actualStorageRef : Bool) :
    Except TypeError Unit :=
  require
    (!(targetChecked.stateLValue &&
        !env.assignmentRebindsStoragePointer target actualStorageRef &&
        Ty.containsMapping env.types 64 targetChecked.ty))
    (TypeError.unsupported
      "assignment to storage value containing mapping")

def CheckedExpr.expectBool (expr : CheckedExpr) : Except TypeError Unit :=
  require expr.ty.isBool (TypeError.expectedBool expr.ty)

def CheckedExpr.expectInteger (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isInteger (TypeError.expectedInteger expr.ty)

def CheckedExpr.expectNumeric (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isNumeric (TypeError.expectedNumeric expr.ty)

def CheckedExpr.requiresExactLiteralFit (expr : CheckedExpr) : Bool :=
  expr.ty.isNumeric && exprIsUntypedNumberLiteralExpression expr.source

def CheckedExpr.canImplicitlyAssignTo (expr : CheckedExpr)
    (expected : Ty) : Bool :=
  Ty.canImplicitlyConvert expr.ty expected ||
    implicitLiteralFits expected expr.source

def CheckedExpr.canImplicitlyAssignToIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) : Bool :=
  TypeContext.canImplicitlyConvert types expr.ty expected ||
    implicitLiteralFits expected expr.source

def CheckedExpr.canAssignTo (expr : CheckedExpr) (expected : Ty) :
    Bool :=
  if expr.requiresExactLiteralFit then
    implicitLiteralFits expected expr.source
  else
    expr.canImplicitlyAssignTo expected

def CheckedExpr.canAssignToIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) : Bool :=
  if expr.requiresExactLiteralFit then
    implicitLiteralFits expected expr.source
  else
    expr.canImplicitlyAssignToIn types expected

def CheckedExpr.expectAssignableTo (expr : CheckedExpr) (expected : Ty) :
    Except TypeError Unit :=
  require (expr.canAssignTo expected)
    (TypeError.expectedType expected expr.ty)

def CheckedExpr.expectAssignableToIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) :
    Except TypeError Unit := do
  types.requireNoFixedPointAssignment expr.ty expected
  require (expr.canAssignToIn types expected)
    (TypeError.expectedType expected expr.ty)

def CheckedExpr.expectImplicitlyAssignableTo (expr : CheckedExpr)
    (expected : Ty) : Except TypeError Unit :=
  require (expr.canImplicitlyAssignTo expected)
    (TypeError.expectedType expected expr.ty)

def CheckedExpr.expectImplicitlyAssignableToIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) : Except TypeError Unit := do
  types.requireNoFixedPointAssignment expr.ty expected
  require (expr.canImplicitlyAssignToIn types expected)
    (TypeError.expectedType expected expr.ty)

abbrev TupleAssignmentTarget :=
  Option (Solidity.Expr × CheckedExpr)

def checkTupleAssignmentTargetAgainstTy (env : CheckEnv)
    (actualStorageRef : Bool)
    (actualLocation : Option Solidity.DataLocation)
    (target : Solidity.Expr)
    (targetChecked : CheckedExpr) (rhsTy : Ty) :
    Except TypeError Ty := do
  env.requireNoMappingStorageCopy target targetChecked actualStorageRef
  match Expr.directIdentName? target with
  | some name =>
      require (!env.isLocalStorageRef name || actualStorageRef)
        (TypeError.invalidDataLocation targetChecked.ty
          (some Solidity.DataLocation.storage))
  | none => Except.ok ()
  if targetChecked.locationIsCalldata then
    require
      (actualLocation == some Solidity.DataLocation.calldata)
      (TypeError.invalidDataLocation targetChecked.ty
        targetChecked.dataLocation?)
  else
    Except.ok ()
  require
    (TypeContext.canImplicitlyConvert env.types rhsTy targetChecked.ty)
    (TypeError.expectedType targetChecked.ty rhsTy)
  env.types.requireNoFixedPointAssignment rhsTy targetChecked.ty
  Except.ok targetChecked.ty

def checkTupleAssignmentTargetsWithTys (env : CheckEnv)
    : List TupleAssignmentTarget -> List Ty -> List Bool ->
    List (Option Solidity.DataLocation) ->
    Except TypeError (List Ty)
  | [], [], _, _ => Except.ok []
  | none :: targetRest, _ :: tyRest, storageRefs, locations =>
      checkTupleAssignmentTargetsWithTys env targetRest tyRest
        storageRefs.tail locations.tail
  | some (target, targetChecked) :: targetRest,
      rhsTy :: tyRest, storageRefs, locations => do
      let ty ←
        checkTupleAssignmentTargetAgainstTy env
          (storageRefs.head?.getD false) (locations.head?.join)
          target targetChecked rhsTy
      let tail ←
        checkTupleAssignmentTargetsWithTys env targetRest tyRest
          storageRefs.tail locations.tail
      Except.ok (ty :: tail)
  | targets, tys, _, _ =>
      Except.error
        (TypeError.arityMismatch
          "tuple assignment" targets.length tys.length)

def Arg.name? : Solidity.Arg -> Option Name
  | Solidity.Arg.positional _ => none
  | Solidity.Arg.named name _ => some name

namespace Args

def anyNamed : List Solidity.Arg -> Bool
  | [] => false
  | Solidity.Arg.named _ _ :: _ => true
  | Solidity.Arg.positional _ :: rest => anyNamed rest

def positionalExprs? : List Solidity.Arg ->
    Option (List Solidity.Expr)
  | [] => some []
  | Solidity.Arg.positional expr :: rest => do
      let tail ← positionalExprs? rest
      some (expr :: tail)
  | Solidity.Arg.named _ _ :: _ => none

end Args

def checkedArgInfos : List Solidity.Arg -> List CheckedExpr ->
    List ArgInfo
  | [], [] => []
  | arg :: argRest, checked :: checkedRest =>
      (Arg.name? arg, checked.ty) :: checkedArgInfos argRest checkedRest
  | _, _ => []

abbrev CheckedArgInfo := Option Name × CheckedExpr

namespace CheckedArgInfos

def anyNamed : List CheckedArgInfo -> Bool
  | [] => false
  | (some _, _) :: _ => true
  | (none, _) :: rest => anyNamed rest

def anyPositional : List CheckedArgInfo -> Bool
  | [] => false
  | (none, _) :: _ => true
  | (some _, _) :: rest => anyPositional rest

def namedNames : List CheckedArgInfo -> List Name
  | [] => []
  | (some name, _) :: rest => name :: namedNames rest
  | (none, _) :: rest => namedNames rest

def lookupNamed? (target : Name) : List CheckedArgInfo -> Option CheckedExpr
  | [] => none
  | (some name, checked) :: rest =>
      if name == target then some checked else lookupNamed? target rest
  | (none, _) :: rest => lookupNamed? target rest

def collectNamed? : List (Option Name) -> List CheckedArgInfo ->
    Option (List CheckedExpr)
  | [], _ => some []
  | some name :: rest, infos => do
      let checked ← lookupNamed? name infos
      let tail ← collectNamed? rest infos
      some (checked :: tail)
  | none :: _, _ => none

def ordered? (paramNames : List (Option Name))
    (infos : List CheckedArgInfo) : Option (List CheckedExpr) :=
  if anyNamed infos then
    if anyPositional infos then
      none
    else if !(namesUnique (namedNames infos)) then
      none
    else if infos.length == paramNames.length then
      collectNamed? paramNames infos
    else
      none
  else
    some (infos.map Prod.snd)

end CheckedArgInfos

def checkedArgInfosFull : List Solidity.Arg -> List CheckedExpr ->
    List CheckedArgInfo
  | [], [] => []
  | arg :: argRest, checked :: checkedRest =>
      (Arg.name? arg, checked) :: checkedArgInfosFull argRest checkedRest
  | _, _ => []

def Expr.literalNat? : Solidity.Expr -> Option Nat
  | Solidity.Expr.literal
      (Solidity.Literal.number text) =>
      Solidity.Executable.parseNumberNat? text
  | Solidity.Expr.literal
      (Solidity.Literal.unitNumber text unit) =>
      Solidity.Executable.parseUnitNumberNat? text unit
  | _ => none

def Ty.commonImplicit? (left right : Ty) : Option Ty :=
  if left == right then
    some left
  else
    match left, right with
    | Solidity.Ty.address _,
      Solidity.Ty.address _ =>
        some (Solidity.Ty.address false)
    | Solidity.Ty.uint leftBits,
      Solidity.Ty.uint rightBits =>
        some (Solidity.Ty.uint (max leftBits rightBits))
    | Solidity.Ty.int leftBits,
      Solidity.Ty.int rightBits =>
        some (Solidity.Ty.int (max leftBits rightBits))
    | Solidity.Ty.fixed leftBits leftDecimals,
      Solidity.Ty.fixed rightBits rightDecimals =>
        Solidity.Ty.commonFixedPoint?
          true leftBits leftDecimals true rightBits rightDecimals
    | Solidity.Ty.ufixed leftBits leftDecimals,
      Solidity.Ty.ufixed rightBits rightDecimals =>
        Solidity.Ty.commonFixedPoint?
          false leftBits leftDecimals false rightBits rightDecimals
    | Solidity.Ty.fixed leftBits leftDecimals,
      Solidity.Ty.ufixed rightBits rightDecimals =>
        Solidity.Ty.commonFixedPoint?
          true leftBits leftDecimals false rightBits rightDecimals
    | Solidity.Ty.ufixed leftBits leftDecimals,
      Solidity.Ty.fixed rightBits rightDecimals =>
        Solidity.Ty.commonFixedPoint?
          false leftBits leftDecimals true rightBits rightDecimals
    | Solidity.Ty.bytesN leftSize,
      Solidity.Ty.bytesN rightSize =>
        some (Solidity.Ty.bytesN (max leftSize rightSize))
    | Solidity.Ty.fixedBytes leftSize,
      Solidity.Ty.fixedBytes rightSize =>
        some (Solidity.Ty.fixedBytes (max leftSize rightSize))
    | Solidity.Ty.bytesN leftSize,
      Solidity.Ty.fixedBytes rightSize =>
        some (Solidity.Ty.fixedBytes (max leftSize rightSize))
    | Solidity.Ty.fixedBytes leftSize,
      Solidity.Ty.bytesN rightSize =>
        some (Solidity.Ty.fixedBytes (max leftSize rightSize))
    | _, _ =>
        if Ty.canImplicitlyConvert left right then
          some right
        else if Ty.canImplicitlyConvert right left then
          some left
        else
          none

-- solc's bottom-up type of an inline array literal, mirroring
-- `TypeChecker::visit(TupleExpression)` (isInlineArray) restricted to the case
-- where the deduced type is decidable WITHOUT an environment — i.e. every leaf
-- is a bare (untyped) number literal:
--   * element 0 seeds the accumulator with its `mobileType()` — the
--     smallest-fitting `uintN`/`intN` (`RationalNumberType::mobileType`), e.g.
--     `1 ↦ uint8`, `256 ↦ uint16`, `-1 ↦ int8`;
--   * each later element folds via `Type::commonType(acc, rawElem)`: a bare
--     number literal that still fits the accumulator keeps it, otherwise the
--     accumulator widens to `commonImplicit?` of the accumulator and the
--     literal's mobile type; nested arrays recurse.
-- `exprIsUntypedNumberLiteralExpression` does NOT see through a `T(x)`
-- conversion (unlike `numberLiteralRat?`), so an explicitly typed element such
-- as `uint256(1)` makes this return `none`; the caller then falls back to the
-- ordinary `checkExpr`-typed assignability check, which is already solc-faithful
-- for arrays whose over-wide `uint256[n]` typing does NOT arise (any typed /
-- variable element). Order-sensitive exactly like solc (`[int8(-1),2]` is
-- accepted elsewhere; a bare-only `[2,3]` seeds `uint8`).
-- Returns `none` for empty / ragged / no-common-type literals too, so callers
-- reject exactly as solc's 6378 "Unable to deduce common type" does.
def inlineArrayBottomUpTyFuel? : Nat -> Solidity.Expr -> Option Ty
  | 0, _ => none
  | _ + 1, Solidity.Expr.array [] => none
  | fuel + 1, Solidity.Expr.array (head :: rest) =>
      (inlineArrayBottomUpTyFuel? fuel head).bind fun firstTy =>
        (rest.foldl
          (fun acc? element =>
            acc?.bind fun acc =>
              if exprIsUntypedNumberLiteralExpression element then
                if implicitLiteralFits acc element then some acc
                else
                  (Solidity.Executable.Expr.untypedLiteralMobileTy? element).bind
                    (fun litMobile => Ty.commonImplicit? acc litMobile)
              else
                (inlineArrayBottomUpTyFuel? fuel element).bind
                  (fun elementTy => Ty.commonImplicit? acc elementTy))
          (some firstTy)).map fun common =>
            Solidity.Ty.array common (some (head :: rest).length)
  | _ + 1, expr =>
      if exprIsUntypedNumberLiteralExpression expr then
        Solidity.Executable.Expr.untypedLiteralMobileTy? expr
      else
        none

def inlineArrayBottomUpTy? (expr : Solidity.Expr) : Option Ty :=
  inlineArrayBottomUpTyFuel? 128 expr

-- Assignability of an inline array literal against a fixed-size array target,
-- applied wherever a checked expression meets an expected type (assignment,
-- return, and every argument position). When the literal has a bare-only
-- bottom-up type, require it to EQUAL the target element type (solc's
-- `ArrayType::isImplicitlyConvertibleTo` demands an IDENTICAL base type for
-- fixed→fixed memory arrays — no implicit widening; this also correctly accepts
-- `uint8[3] = [1,2,3]`, which the uint256-typed `checked.ty` would otherwise
-- fail). Otherwise defer to the ordinary check, which is solc-faithful for every
-- other array (a typed / variable element already yields a precise element type
-- in `checkExpr`).
def arrayLiteralFixedWidenCheck (types : TypeContext)
    (checked : CheckedExpr) (expected : Ty) : Except TypeError Unit :=
  match checked.source, expected with
  | Solidity.Expr.array _, Solidity.Ty.array _ (some _) =>
      match inlineArrayBottomUpTy? checked.source with
      | some litTy =>
          if litTy == expected then Except.ok ()
          else Except.error (TypeError.expectedType expected checked.ty)
      | none => checked.expectAssignableToIn types expected
  | _, _ => checked.expectAssignableToIn types expected

def Expr.isDirectLiteral : Solidity.Expr -> Bool
  | Solidity.Expr.literal _ => true
  | _ => false

def CheckedExpr.commonArrayElementTy? (left right : CheckedExpr) :
    Option Ty :=
  if Expr.isDirectLiteral right.source &&
      implicitLiteralFits left.ty right.source then
    some left.ty
  else if Expr.isDirectLiteral left.source &&
      implicitLiteralFits right.ty left.source then
    some right.ty
  else
    Ty.commonImplicit? left.ty right.ty

def CheckedExprs.commonArrayElementTyFrom? (current : Ty) :
    List CheckedExpr -> Option Ty
  | [] => some current
  | checked :: rest => do
      let probe : CheckedExpr :=
        { source := checked.source
          ty := current
          lvalue := false
          stateLValue := false }
      let next ← CheckedExpr.commonArrayElementTy? probe checked
      CheckedExprs.commonArrayElementTyFrom? next rest

def CheckedExprs.commonArrayElementTy? :
    List CheckedExpr -> Option Ty
  | [] => none
  | checked :: rest =>
      CheckedExprs.commonArrayElementTyFrom? checked.ty rest

def CheckedExpr.commonOperandTy? (left right : CheckedExpr) : Option Ty :=
  CheckedExpr.commonArrayElementTy? left right

def CheckedExprs.expectAssignableToSame (_what : String)
    (left right : CheckedExpr) (ty : Ty) : Except TypeError Unit := do
  left.expectImplicitlyAssignableTo ty
  right.expectImplicitlyAssignableTo ty

def CheckedExprs.commonCheckedTyFor
    (what : String) (allowed : Ty -> Bool) (err : Ty -> TypeError)
    (left right : CheckedExpr) : Except TypeError Ty := do
  let ty ←
    match CheckedExpr.commonOperandTy? left right with
    | some ty => Except.ok ty
    | none => Except.error (TypeError.expectedType left.ty right.ty)
  require (allowed ty) (err ty)
  CheckedExprs.expectAssignableToSame what left right ty
  Except.ok ty

def CheckedExprs.arithmeticTy (left right : CheckedExpr) :
    Except TypeError Ty :=
  CheckedExprs.commonCheckedTyFor "arithmetic expression"
    Ty.isArithmeticOperand TypeError.expectedInteger left right

def CheckedExprs.bitwiseTy (left right : CheckedExpr) :
    Except TypeError Ty :=
  CheckedExprs.commonCheckedTyFor "bitwise expression"
    Ty.isBitwiseOperand TypeError.expectedNumeric left right

def CheckedExprs.relationalTy (types : TypeContext) (left right : CheckedExpr) :
    Except TypeError Ty :=
  CheckedExprs.commonCheckedTyFor "relational expression"
    (Ty.isRelationalOperand types) TypeError.expectedNumeric left right

-- G3: `==`/`!=` are builtin-defined only on value types, contracts, enums,
-- addresses and function pointers (solc TypeError 2271 otherwise; the reference
-- types bytes/string/array/mapping/struct and UDVTs have no builtin equality —
-- `Types.cpp` `binaryOperatorResult(Equal, …)` returns null for them).
def Ty.isEqualityComparable (types : TypeContext) : Solidity.Ty -> Bool
  | Solidity.Ty.bool => true
  | Solidity.Ty.address _ => true
  | Solidity.Ty.uint _ => true
  | Solidity.Ty.int _ => true
  | Solidity.Ty.fixed _ _ => true
  | Solidity.Ty.ufixed _ _ => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | Solidity.Ty.enum _ => true
  | Solidity.Ty.functionWithLocations _ _ _ _ _ _ => true
  -- A `user` path is a contract, an enum, or a UDVT. Contracts (address-like)
  -- and enums have builtin equality; UDVTs do not (need a user-defined operator).
  | Solidity.Ty.user path =>
      TypeContext.isContractPath types path || TypeContext.isEnumPath types path
  | _ => false

def CheckedExpr.expectUnsignedInteger (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isUnsignedInteger
    (TypeError.expectedInteger expr.ty)

def CheckedExpr.expectShiftLeftOperand (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isShiftLeftOperand
    (TypeError.expectedNumeric expr.ty)

def CheckedExpr.expectSignedInteger (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isSignedInteger
    (TypeError.expectedInteger expr.ty)

-- Overload-matching assignability of a checked argument, bottom-up-aware for an
-- inline array literal argument. `canAssignToIn` uses the uint256-typed
-- `checked.ty` (so it would accept the widened `[1,2,3] : uint256[3]` for a
-- `uint256[3]` parameter, which solc rejects); when the argument is an inline
-- array literal with a bare-only bottom-up type we instead require that type to
-- EQUAL the parameter type (solc's `ArrayType::isImplicitlyConvertibleTo`
-- demands an identical fixed-array base — this both rejects `uint256[3]` and
-- keeps `uint8[3]` matching). This is the sole matching predicate behind every
-- `resolveChecked` call site (internal / external / member / super / library /
-- with-options), so the fix applies uniformly; it is NOT used by the per-element
-- array-literal validation inside `checkExpr`.
def CheckedExpr.canAssignToWidenIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) : Bool :=
  match expr.source, expected with
  | Solidity.Expr.array _, Solidity.Ty.array _ (some _) =>
      match inlineArrayBottomUpTy? expr.source with
      | some litTy => litTy == expected
      | none => expr.canAssignToIn types expected
  | _, _ => expr.canAssignToIn types expected

def checkedExprParamsAccept (types : TypeContext) :
    List CheckedExpr -> List Ty -> Bool
  | [], [] => true
  | actual :: actualRest, expected :: expectedRest =>
      actual.canAssignToWidenIn types expected &&
        checkedExprParamsAccept types actualRest expectedRest
  | _, _ => false

def checkedExprParamsAcceptStorageRefs (types : TypeContext) :
    List CheckedExpr -> List Ty -> List Bool -> Bool
  | [], [], [] => true
  | actual :: actualRest, expected :: expectedRest,
      needsStorage :: storageRest =>
      actual.canAssignToWidenIn types expected &&
        (!needsStorage || actual.stateLValue) &&
        checkedExprParamsAcceptStorageRefs types actualRest expectedRest
          storageRest
  | actual, expected, [] => checkedExprParamsAccept types actual expected
  | _, _, _ => false

def checkedExprDataLocationsAccept :
    List CheckedExpr ->
    List (Option Solidity.DataLocation) -> Bool
  | _, [] => true
  | actual :: actualRest, expected :: expectedRest =>
      actual.locationAssignableTo expected &&
        checkedExprDataLocationsAccept actualRest expectedRest
  | _, _ => false

def FunctionSig.matchesCheckedArgs
    (types : TypeContext) (sig : FunctionSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered =>
      checkedExprParamsAcceptStorageRefs types ordered sig.params
        sig.paramStorageRefs &&
      checkedExprDataLocationsAccept ordered sig.paramDataLocations
  | none => false

namespace FunctionSigs

def resolveCheckedLoop (types : TypeContext)
    (target : Name) (args : List CheckedArgInfo) :
    Option FunctionSig -> List FunctionSig ->
    Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesCheckedArgs types args then
        match found? with
        | none => resolveCheckedLoop types target args (some sig) rest
        | some found =>
            if FunctionSig.sameResolutionTarget found sig then
              resolveCheckedLoop types target args (some found) rest
            else
              Except.error (TypeError.ambiguousFunction target)
      else
        resolveCheckedLoop types target args found? rest

def resolveChecked (types : TypeContext) (functions : List FunctionSig)
    (target : Name) (args : List CheckedArgInfo) :
    Except TypeError FunctionSig :=
  resolveCheckedLoop types target args none functions

end FunctionSigs

def TypeContext.resolveContractMemberFunctionChecked
    (types : TypeContext) (path : Path) (member : Name)
    (args : List CheckedArgInfo) : Except TypeError FunctionSig :=
  match types.lookupContractExternalFunctionSigs? path with
  | some sigs => FunctionSigs.resolveChecked types sigs member args
  | none => Except.error (TypeError.unknownFunction member)

-- EC1: an `abi.encodeCall` function pointer must reference a UNIQUE function.
-- solc resolves it by name alone (NOT by argument type) and separately checks
-- each argument implicitly convertible to its parameter; a narrower integer or
-- an integer literal argument must therefore not be rejected at resolution. The
-- general contextual (type-exact) resolver over-rejected those. Resolve by
-- name + arity here without inspecting argument types (arity distinguishes the
-- legitimate no-overload case; a genuine same-arity overload is ambiguous, as in
-- solc). The per-argument assignability check happens at the call site.
def TypeContext.resolveEncodeCallPointerSig
    (types : TypeContext) (path : Path) (member : Name) (argCount : Nat) :
    Except TypeError FunctionSig :=
  match types.lookupContractExternalFunctionSigs? path with
  | some sigs =>
      match sigs.filter
          (fun s => s.name == member && s.params.length == argCount) with
      | [] => Except.error (TypeError.unknownFunction member)
      | first :: rest =>
          if rest.all (fun s => FunctionSig.sameResolutionTarget first s) then
            Except.ok first
          else
            Except.error (TypeError.ambiguousFunction member)
  | none => Except.error (TypeError.unknownFunction member)

def ModifierSig.matchesCheckedArgs
    (types : TypeContext) (sig : ModifierSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered =>
      checkedExprParamsAcceptStorageRefs types ordered sig.params
        sig.paramStorageRefs &&
      checkedExprDataLocationsAccept ordered sig.paramDataLocations
  | none => false

namespace ModifierSigs

def resolveCheckedLoop (types : TypeContext)
    (target : Name) (args : List CheckedArgInfo) :
    Option ModifierSig -> List ModifierSig ->
    Except TypeError ModifierSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesCheckedArgs types args then
        match found? with
        | none => resolveCheckedLoop types target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveCheckedLoop types target args found? rest

def resolveChecked (types : TypeContext) (modifiers : List ModifierSig)
    (target : Name) (args : List CheckedArgInfo) :
    Except TypeError ModifierSig :=
  resolveCheckedLoop types target args none modifiers

end ModifierSigs

def EventSig.matchesCheckedArgs
    (types : TypeContext) (sig : EventSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered => checkedExprParamsAccept types ordered sig.params
  | none => false

namespace EventSigs

def resolveCheckedLoop (types : TypeContext)
    (target : Name) (args : List CheckedArgInfo) :
    Option EventSig -> List EventSig -> Except TypeError EventSig
  | none, [] => Except.error (TypeError.unknownEvent target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesCheckedArgs types args then
        match found? with
        | none => resolveCheckedLoop types target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveCheckedLoop types target args found? rest

def resolveChecked (types : TypeContext) (events : List EventSig)
    (target : Name) (args : List CheckedArgInfo) :
    Except TypeError EventSig :=
  resolveCheckedLoop types target args none events

end EventSigs

def ErrorSig.matchesCheckedArgs
    (types : TypeContext) (sig : ErrorSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered => checkedExprParamsAccept types ordered sig.params
  | none => false

namespace ErrorSigs

def resolveCheckedLoop (types : TypeContext)
    (target : Name) (args : List CheckedArgInfo) :
    Option ErrorSig -> List ErrorSig -> Except TypeError ErrorSig
  | none, [] => Except.error (TypeError.unknownError target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesCheckedArgs types args then
        match found? with
        | none => resolveCheckedLoop types target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveCheckedLoop types target args found? rest

def resolveChecked (types : TypeContext) (errors : List ErrorSig)
    (target : Name) (args : List CheckedArgInfo) :
    Except TypeError ErrorSig :=
  resolveCheckedLoop types target args none errors

end ErrorSigs

def FunctionSig.usingMemberCandidate?
    (types : TypeContext) (receiver : CheckedExpr) (member : Name)
    (sig : FunctionSig) :
    Option FunctionSig :=
  if sig.name == member && sig.nonPrivate then
    match sig.params, sig.paramNames, sig.paramStorageRefs,
        sig.paramDataLocations with
    | selfTy :: params, _ :: paramNames,
        selfNeedsStorage :: paramStorageRefs,
        selfLocation :: paramDataLocations =>
        if TypeContext.canImplicitlyConvert types receiver.ty selfTy ||
            implicitLiteralFits selfTy receiver.source then
          if (!selfNeedsStorage || receiver.stateLValue) &&
              receiver.locationAssignableTo selfLocation then
            some
              { sig with
                params := params
                paramNames := paramNames
                paramStorageRefs := paramStorageRefs
                paramDataLocations := paramDataLocations }
          else
            none
        else
          none
    | selfTy :: params, _ :: paramNames,
        selfNeedsStorage :: paramStorageRefs, [] =>
        if TypeContext.canImplicitlyConvert types receiver.ty selfTy ||
            implicitLiteralFits selfTy receiver.source then
          if !selfNeedsStorage || receiver.stateLValue then
            some
              { sig with
                params := params
                paramNames := paramNames
                paramStorageRefs := paramStorageRefs }
          else
            none
        else
          none
    | selfTy :: params, _ :: paramNames, [], [] =>
        if TypeContext.canImplicitlyConvert types receiver.ty selfTy ||
            implicitLiteralFits selfTy receiver.source then
          some { sig with params := params, paramNames := paramNames }
        else
          none
    | _, _, _, _ => none
  else
    none

namespace FunctionSigs

def usingMemberCandidates (types : TypeContext)
    (receiver : CheckedExpr) (member : Name) :
    List FunctionSig -> List FunctionSig
  | [] => []
  | sig :: rest =>
      match FunctionSig.usingMemberCandidate? types receiver member sig with
      | some candidate =>
          candidate :: usingMemberCandidates types receiver member rest
      | none => usingMemberCandidates types receiver member rest

end FunctionSigs

def UsingFunction.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name)
    (binding : Solidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some _ => Except.ok []
  | none =>
      let (libraryPath, functionName) ←
        match Solidity.Executable.pathInitLast? binding.function with
        | some parts => Except.ok parts
        | none => Except.error (TypeError.unknownFunction member)
      if functionName == member then
        if libraryPath.segments.isEmpty then
          Except.ok
            (FunctionSigs.usingMemberCandidates env.types receiver member
              (FunctionSigs.withOrigin binding.function
                ((FunctionSigs.nonPrivate env.functions).filter
                  (fun sig => sig.name == functionName))))
        else
          let libraryDecl ←
            match env.types.lookupContractDecl? libraryPath with
            | some libraryDecl => Except.ok libraryDecl
            | none => Except.error (TypeError.unknownType libraryPath)
          require (libraryDecl.kind == Solidity.ContractKind.library)
            (TypeError.invalidContractHeader "using target is not a library")
          Except.ok
            (FunctionSigs.usingMemberCandidates env.types receiver member
              (FunctionSigs.withOrigin binding.function
                ((FunctionSigs.nonPrivate
                  (FunctionSigs.atLibraryCallBoundary env.types
                    (ContractDecl.directFunctionSigsQualifiedLocalTypes
                      libraryDecl))).filter
                    (fun sig => sig.name == functionName))))
      else
        Except.ok []

def UsingFunctions.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name) :
    List Solidity.UsingFunction ->
    Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | binding :: rest => do
      let head ← UsingFunction.memberCandidates env receiver member binding
      let tail ← UsingFunctions.memberCandidates env receiver member rest
      Except.ok (head ++ tail)

def UsingDecl.appliesToReceiver
    (decl : Solidity.UsingDecl) (receiverTy : Ty) : Bool :=
  match decl.target with
  | some targetTy => receiverTy == targetTy
  | none => true

def UsingDecl.appliesToBinaryOperands
    (decl : Solidity.UsingDecl) (lhsTy rhsTy : Ty) : Bool :=
  match decl.target with
  | some targetTy => lhsTy == targetTy || rhsTy == targetTy
  | none => true

def UsingFunction.same (a b : Solidity.UsingFunction) : Bool :=
  a.function == b.function && a.operator? == b.operator?

def UsingFunctions.same :
    List Solidity.UsingFunction ->
      List Solidity.UsingFunction -> Bool
  | [], [] => true
  | a :: restA, b :: restB =>
      UsingFunction.same a b && UsingFunctions.same restA restB
  | _, _ => false

def UsingDecl.same
    (a b : Solidity.UsingDecl) : Bool :=
  a.library == b.library &&
    UsingFunctions.same a.functions b.functions &&
    a.target == b.target &&
    a.global == b.global

namespace UsingDecls

def containsSame (target : Solidity.UsingDecl) :
    List Solidity.UsingDecl -> Bool
  | [] => false
  | decl :: rest =>
      UsingDecl.same target decl || containsSame target rest

def dedupAux (seen : List Solidity.UsingDecl) :
    List Solidity.UsingDecl ->
      List Solidity.UsingDecl
  | [] => []
  | decl :: rest =>
      if containsSame decl seen then
        dedupAux seen rest
      else
        decl :: dedupAux (decl :: seen) rest

def dedup (decls : List Solidity.UsingDecl) :
    List Solidity.UsingDecl :=
  dedupAux [] decls

end UsingDecls

def BinaryOp.userDefinedOperatorResultTy? (targetTy : Ty) :
    Solidity.BinaryOp -> Option Ty
  | Solidity.BinaryOp.add
  | Solidity.BinaryOp.sub
  | Solidity.BinaryOp.mul
  | Solidity.BinaryOp.div
  | Solidity.BinaryOp.mod
  | Solidity.BinaryOp.bitAnd
  | Solidity.BinaryOp.bitOr
  | Solidity.BinaryOp.bitXor => some targetTy
  | Solidity.BinaryOp.lt
  | Solidity.BinaryOp.gt
  | Solidity.BinaryOp.le
  | Solidity.BinaryOp.ge
  | Solidity.BinaryOp.eq
  | Solidity.BinaryOp.ne => some Solidity.Ty.bool
  | _ => none

def UnaryOp.userDefinedOperatorResultTy? (targetTy : Ty) :
    Solidity.UnaryOp -> Option Ty
  | Solidity.UnaryOp.bitNot
  | Solidity.UnaryOp.neg => some targetTy
  | _ => none

def UsingOperator.userDefinedResultTy? (targetTy : Ty) :
    Solidity.UsingOperator -> Option Ty
  | Solidity.UsingOperator.binary op =>
      BinaryOp.userDefinedOperatorResultTy? targetTy op
  | Solidity.UsingOperator.unary op =>
      UnaryOp.userDefinedOperatorResultTy? targetTy op

def FunctionSig.hasParamTy (targetTy : Ty) : List Ty -> Bool
  | [] => false
  | ty :: rest => ty == targetTy || FunctionSig.hasParamTy targetTy rest

def FunctionSig.matchesUserDefinedBinaryOperator
    (types : TypeContext) (targetTy : Ty)
    (op : Solidity.BinaryOp) (lhs rhs : CheckedExpr)
    (sig : FunctionSig) : Bool :=
  match BinaryOp.userDefinedOperatorResultTy? targetTy op with
  | some resultTy =>
      sig.mutability == Solidity.StateMutability.pure &&
        sig.returns == [resultTy] &&
        FunctionSig.hasParamTy targetTy sig.params &&
        sig.matchesCheckedArgs types [(none, lhs), (none, rhs)]
  | none => false

def FunctionSig.matchesUserDefinedUnaryOperator
    (types : TypeContext) (targetTy : Ty)
    (op : Solidity.UnaryOp) (operand : CheckedExpr)
    (sig : FunctionSig) : Bool :=
  match UnaryOp.userDefinedOperatorResultTy? targetTy op with
  | some resultTy =>
      sig.mutability == Solidity.StateMutability.pure &&
        sig.returns == [resultTy] &&
        FunctionSig.hasParamTy targetTy sig.params &&
        sig.matchesCheckedArgs types [(none, operand)]
  | none => false

def FunctionSig.matchesUserDefinedOperatorDecl (targetTy : Ty)
    (operator : Solidity.UsingOperator)
    (sig : FunctionSig) : Bool :=
  -- solc `TypeChecker.cpp:4158-4186` (error 1884): an operator function's
  -- parameters must ALL be exactly the target type — for a binary operator both
  -- params are `T`, for a unary operator the single param is `T` — and it must
  -- return the operator's result type (`T`, or `bool` for comparisons, as fixed
  -- by `userDefinedOperatorResultTy?`). Requiring `hasParamTy` (target appears in
  -- ≥1 position) was too weak, wrongly admitting e.g. `f(T, uint) as +`.
  match operator with
  | Solidity.UsingOperator.binary op =>
      match BinaryOp.userDefinedOperatorResultTy? targetTy op with
      | some resultTy =>
          sig.mutability == Solidity.StateMutability.pure &&
            sig.params.length == 2 &&
            sig.params.all (· == targetTy) &&
            sig.returns == [resultTy]
      | none => false
  | Solidity.UsingOperator.unary op =>
      match UnaryOp.userDefinedOperatorResultTy? targetTy op with
      | some resultTy =>
          sig.mutability == Solidity.StateMutability.pure &&
            sig.params.length == 1 &&
            sig.params.all (· == targetTy) &&
            sig.returns == [resultTy]
      | none => false

def UsingFunction.binaryOperatorCandidates (env : CheckEnv)
    (targetTy : Ty) (op : Solidity.BinaryOp)
    (lhs rhs : CheckedExpr)
    (binding : Solidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some (Solidity.UsingOperator.binary bindingOp) =>
      if bindingOp == op then
        let (libraryPath, functionName) ←
          match Solidity.Executable.pathInitLast? binding.function with
          | some parts => Except.ok parts
          | none => Except.error (TypeError.unknownFunction "operator")
        if libraryPath.segments.isEmpty then
          Except.ok
            ((FunctionSigs.withOrigin binding.function
              (FunctionSigs.nonPrivate env.functions)).filter
                (fun sig =>
                  sig.name == functionName &&
                    sig.matchesUserDefinedBinaryOperator
                      env.types targetTy op lhs rhs))
        else
          Except.ok []
      else
        Except.ok []
  | _ => Except.ok []

def UsingFunctions.binaryOperatorCandidates (env : CheckEnv)
    (targetTy : Ty) (op : Solidity.BinaryOp)
    (lhs rhs : CheckedExpr) :
    List Solidity.UsingFunction ->
    Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | binding :: rest => do
      let head ←
        UsingFunction.binaryOperatorCandidates
          env targetTy op lhs rhs binding
      let tail ←
        UsingFunctions.binaryOperatorCandidates env targetTy op lhs rhs rest
      Except.ok (head ++ tail)

def UsingFunction.unaryOperatorCandidates (env : CheckEnv)
    (targetTy : Ty) (op : Solidity.UnaryOp)
    (operand : CheckedExpr)
    (binding : Solidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some (Solidity.UsingOperator.unary bindingOp) =>
      if bindingOp == op then
        let (libraryPath, functionName) ←
          match Solidity.Executable.pathInitLast? binding.function with
          | some parts => Except.ok parts
          | none => Except.error (TypeError.unknownFunction "operator")
        if libraryPath.segments.isEmpty then
          Except.ok
            ((FunctionSigs.withOrigin binding.function
              (FunctionSigs.nonPrivate env.functions)).filter
                (fun sig =>
                  sig.name == functionName &&
                    sig.matchesUserDefinedUnaryOperator
                      env.types targetTy op operand))
        else
          Except.ok []
      else
        Except.ok []
  | _ => Except.ok []

def UsingFunctions.unaryOperatorCandidates (env : CheckEnv)
    (targetTy : Ty) (op : Solidity.UnaryOp)
    (operand : CheckedExpr) :
    List Solidity.UsingFunction ->
    Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | binding :: rest => do
      let head ←
        UsingFunction.unaryOperatorCandidates
          env targetTy op operand binding
      let tail ←
        UsingFunctions.unaryOperatorCandidates env targetTy op operand rest
      Except.ok (head ++ tail)

def UsingDecl.binaryOperatorCandidates (env : CheckEnv)
    (op : Solidity.BinaryOp) (lhs rhs : CheckedExpr)
    (decl : Solidity.UsingDecl) :
    Except TypeError (List FunctionSig) := do
  match decl.target with
  | some targetTy =>
      if UsingDecl.appliesToBinaryOperands decl lhs.ty rhs.ty then
        UsingFunctions.binaryOperatorCandidates
          env targetTy op lhs rhs decl.functions
      else
        Except.ok []
  | none => Except.ok []

def UsingDecl.unaryOperatorCandidates (env : CheckEnv)
    (op : Solidity.UnaryOp) (operand : CheckedExpr)
    (decl : Solidity.UsingDecl) :
    Except TypeError (List FunctionSig) := do
  match decl.target with
  | some targetTy =>
      if UsingDecl.appliesToReceiver decl operand.ty then
        UsingFunctions.unaryOperatorCandidates
          env targetTy op operand decl.functions
      else
        Except.ok []
  | none => Except.ok []

def UsingDecls.binaryOperatorCandidates (env : CheckEnv)
    (op : Solidity.BinaryOp) (lhs rhs : CheckedExpr) :
    List Solidity.UsingDecl -> Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | decl :: rest => do
      let head ← UsingDecl.binaryOperatorCandidates env op lhs rhs decl
      let tail ←
        UsingDecls.binaryOperatorCandidates env op lhs rhs rest
      Except.ok (head ++ tail)

def UsingDecls.unaryOperatorCandidates (env : CheckEnv)
    (op : Solidity.UnaryOp) (operand : CheckedExpr) :
    List Solidity.UsingDecl -> Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | decl :: rest => do
      let head ← UsingDecl.unaryOperatorCandidates env op operand decl
      let tail ←
        UsingDecls.unaryOperatorCandidates env op operand rest
      Except.ok (head ++ tail)

def UsingDecl.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name)
    (decl : Solidity.UsingDecl) :
    Except TypeError (List FunctionSig) := do
  if UsingDecl.appliesToReceiver decl receiver.ty then
    if decl.functions.isEmpty then
      let libraryDecl ←
        match env.types.lookupContractDecl? decl.library with
        | some libraryDecl => Except.ok libraryDecl
        | none => Except.error (TypeError.unknownType decl.library)
      require (libraryDecl.kind == Solidity.ContractKind.library)
        (TypeError.invalidContractHeader "using target is not a library")
      Except.ok
        (FunctionSigs.usingMemberCandidates env.types receiver member
          (FunctionSigs.withLibraryOrigin decl.library
            (FunctionSigs.nonPrivate
              (FunctionSigs.atLibraryCallBoundary env.types
                (ContractDecl.directFunctionSigsQualifiedLocalTypes
                  libraryDecl)))))
    else
      UsingFunctions.memberCandidates env receiver member decl.functions
  else
    Except.ok []

def UsingDecls.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name) :
    List Solidity.UsingDecl -> Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | decl :: rest => do
      let head ← UsingDecl.memberCandidates env receiver member decl
      let tail ← UsingDecls.memberCandidates env receiver member rest
      Except.ok (head ++ tail)

def CheckEnv.resolveUsingMemberFunctionChecked (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name)
    (args : List CheckedArgInfo) : Except TypeError FunctionSig := do
  let candidates ←
    UsingDecls.memberCandidates env receiver member env.usingDecls
  FunctionSigs.resolveChecked env.types candidates member args

def CheckEnv.resolveUsingBinaryOperator? (env : CheckEnv)
    (op : Solidity.BinaryOp) (lhs rhs : CheckedExpr) :
    Except TypeError (Option FunctionSig) := do
  let candidates ←
    UsingDecls.binaryOperatorCandidates env op lhs rhs env.usingDecls
  match candidates with
  | [] => Except.ok none
  | [sig] => Except.ok (some sig)
  | _ => Except.error (TypeError.ambiguousFunction "operator")

def CheckEnv.resolveUsingUnaryOperator? (env : CheckEnv)
    (op : Solidity.UnaryOp) (operand : CheckedExpr) :
    Except TypeError (Option FunctionSig) := do
  let candidates ←
    UsingDecls.unaryOperatorCandidates env op operand env.usingDecls
  match candidates with
  | [] => Except.ok none
  | [sig] => Except.ok (some sig)
  | _ => Except.error (TypeError.ambiguousFunction "operator")

def TypeContext.resolveLibraryFunctionChecked (types : TypeContext)
    (libraryName member : Name) (args : List CheckedArgInfo) :
    Except TypeError FunctionSig := do
  let path := TypeContext.pathOfName libraryName
  let libraryDecl ←
    match types.lookupContractDecl? path with
    | some libraryDecl => Except.ok libraryDecl
    | none => Except.error (TypeError.unknownType path)
  require (libraryDecl.kind == Solidity.ContractKind.library)
    (TypeError.invalidContractHeader "library call target is not a library")
  FunctionSigs.resolveChecked types
    (FunctionSigs.nonPrivate
      (FunctionSigs.atLibraryCallBoundary types
        (ContractDecl.directFunctionSigsQualifiedLocalTypes libraryDecl)))
    member args

def CheckEnv.resolveExplicitBaseMemberFunctionChecked
    (env : CheckEnv) (baseName member : Name)
    (args : List CheckedArgInfo) : Except TypeError FunctionSig := do
  let path := TypeContext.pathOfName baseName
  require (TypeContext.pathIn path env.ancestorPaths)
    (TypeError.invalidFunctionHeader
      "explicit base call target is not a base contract")
  let baseDecl ←
    match env.types.lookupContractDecl? path with
    | some decl => Except.ok decl
    | none => Except.error (TypeError.unknownType path)
  FunctionSigs.resolveChecked env.types
    (FunctionSigs.nonPrivate
      (ContractDecl.directFunctionSigsQualifiedLocalTypes baseDecl))
    member args

def literalTy? : Solidity.Literal -> Option Ty
  | Solidity.Literal.number text => do
      let _ ← Solidity.Executable.parseNumberRat? text
      some (Solidity.Ty.uint 256)
  | Solidity.Literal.unitNumber text unit => do
      -- A denominated literal may be fractional (`0.5 wei`); solc scales the
      -- rational and only later requires the *folded* result to be integral
      -- (`0.5 wei * 2 = 1`). Gate the literal on the rational parse, not the
      -- integer one, so fractional denominated literals are typeable (CE-5).
      let _ ← Solidity.Executable.parseUnitNumberRat? text unit
      some (Solidity.Ty.uint 256)
  | literal => Solidity.Executable.Literal.abiTy? literal

def CallOptions.names : List Solidity.CallOption -> List Name
  | [] => []
  | Solidity.CallOption.named name _ :: rest =>
      name :: CallOptions.names rest

def CallOptions.hasValue : List Solidity.CallOption -> Bool
  | [] => false
  | Solidity.CallOption.named name _ :: rest =>
      name == "value" || CallOptions.hasValue rest

def CallOptions.hasGas : List Solidity.CallOption -> Bool
  | [] => false
  | Solidity.CallOption.named name _ :: rest =>
      name == "gas" || CallOptions.hasGas rest

def CallOptions.hasSalt : List Solidity.CallOption -> Bool
  | [] => false
  | Solidity.CallOption.named name _ :: rest =>
      name == "salt" || CallOptions.hasSalt rest

def CallOptions.nameAllowed (allowed : List Name) (name : Name) : Bool :=
  Solidity.Executable.nameIn name allowed

def CallOptions.allNamesAllowed (allowed : List Name) :
    List Solidity.CallOption -> Bool
  | [] => true
  | Solidity.CallOption.named name _ :: rest =>
      CallOptions.nameAllowed allowed name &&
        CallOptions.allNamesAllowed allowed rest

def requireCallOptionsAllowedNames (allowed : List Name)
    (options : List Solidity.CallOption) :
    Except TypeError Unit :=
  require (CallOptions.allNamesAllowed allowed options)
    (TypeError.unsupported "call option is not allowed here")

def Ty.isAddressLike (types : TypeContext) : Ty -> Bool
  | Solidity.Ty.address _ => true
  | Solidity.Ty.user path => types.isContractPath path
  | _ => false

def Ty.isAddressBuiltinReceiver : Ty -> Bool
  | Solidity.Ty.address _ => true
  | _ => false

def Ty.isPayableAddress : Ty -> Bool
  | Solidity.Ty.address true => true
  | _ => false

def Ty.hasLengthMember : Ty -> Bool
  | Solidity.Ty.bytes => true
  | Solidity.Ty.bytesN _ => true
  | Solidity.Ty.fixedBytes _ => true
  | Solidity.Ty.array _ _ => true
  | _ => false

def Ty.hasArrayMutationMemberSurface : Ty -> Bool
  | Solidity.Ty.bytes => true
  | Solidity.Ty.array _ _ => true
  | _ => false

def Ty.dynamicStorageArrayElement? : Ty -> Option Ty
  | Solidity.Ty.bytes =>
      some (Solidity.Ty.bytesN 1)
  | Solidity.Ty.array element none => some element
  | _ => none

def lowLevelCallMember (member : Name) : Bool :=
  member == "call" || member == "staticcall" ||
    member == "delegatecall" || member == "send" || member == "transfer"

def lowLevelCallReturnTy : Ty :=
  Solidity.Ty.tuple
    [Solidity.Ty.bool, Solidity.Ty.bytes]

def checkCallTargetExpr (env : CheckEnv)
    (expr : Solidity.Expr) : Except TypeError CheckedExpr :=
  match expr with
  | Solidity.Expr.ident "this" => do
      requireStateReadAllowed env
      match env.currentContract with
      | some path =>
          Except.ok
            { source := expr
              ty := Solidity.Ty.user path
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unknownIdentifier "this")
  | Solidity.Expr.ident name =>
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          let isStorageRef := env.isLocalStorageRef name
          let isConstant := env.isConstantName name
          let isImmutable := env.isImmutableName name
          let dataLocation? :=
            if Ty.needsDataLocation env.types ty then
              if isState || isStorageRef then
                some Solidity.DataLocation.storage
              else
                env.lookupLocalDataLocation? name
            else
              none
          if isState then
            requireStateReadAllowed env
          else
            Except.ok ()
          env.types.requireNoFixedPointValue ty "read"
          Except.ok
            { source := expr
              ty := ty
              lvalue := !isConstant && (!isImmutable || env.inConstructor)
              stateLValue := isState || isStorageRef
              dataLocation? := dataLocation? }
      | none => Except.error (TypeError.unknownIdentifier name)
  | _ =>
      match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
      | none => Except.error (TypeError.unsupported "call target")

def requireValueOptionAllowed
    (mutability : Solidity.StateMutability)
    (options : List Solidity.CallOption) :
    Except TypeError Unit :=
  if CallOptions.hasValue options &&
      !(mutability == Solidity.StateMutability.payable) then
    Except.error TypeError.valueCallToNonpayable
  else
    Except.ok ()

def requireFunctionArgsAccept (expected actual : List Ty) :
    Except TypeError Unit :=
  require (FunctionSig.paramsAccept actual expected)
    (TypeError.arityMismatch "function call" expected.length actual.length)

def requireNoNamedArgs (what : String)
    (argInfos : List ArgInfo) : Except TypeError Unit :=
  require (!ArgInfos.anyNamed argInfos)
    (TypeError.invalidAbiCall (what ++ " does not accept named arguments"))

def CheckedExpr.expectAbiEncodable (types : TypeContext)
    (expr : CheckedExpr) :
    Except TypeError Unit := do
  require (TypeContext.isAbiEncodable types expr.ty)
    (TypeError.invalidAbiType expr.ty)
  require (TypeContext.abiCoderSupports types expr.ty)
    (TypeError.invalidAbiType expr.ty)

mutual

def Ty.isAbiEncodePackedArgShape (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.bool => true
  | _ + 1, Solidity.Ty.address _ => true
  | _ + 1, Solidity.Ty.uint _ => true
  | _ + 1, Solidity.Ty.int _ => true
  | _ + 1, Solidity.Ty.fixed _ _ => true
  | _ + 1, Solidity.Ty.ufixed _ _ => true
  | _ + 1, Solidity.Ty.bytesN _ => true
  | _ + 1, Solidity.Ty.fixedBytes _ => true
  | _ + 1, Solidity.Ty.bytes => true
  | _ + 1, Solidity.Ty.string => true
  | fuel + 1, Solidity.Ty.array element _ =>
      Ty.isAbiEncodePackedArrayElementShape types fuel element
  | fuel + 1, Solidity.Ty.user path =>
      if types.isContractPath path || types.isEnumPath path then
        true
      else
        match types.lookupUserValueType? path with
        | some underlying =>
            Ty.isAbiEncodePackedArgShape types fuel underlying
        | none => false
  | _ + 1, Solidity.Ty.functionWithLocations _ _ _ _ _ visibility =>
      visibility == Solidity.Visibility.external_
  | _ + 1, _ => false

def Ty.isAbiEncodePackedArrayElementShape (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Ty.bool => true
  | _ + 1, Solidity.Ty.address _ => true
  | _ + 1, Solidity.Ty.uint _ => true
  | _ + 1, Solidity.Ty.int _ => true
  | _ + 1, Solidity.Ty.fixed _ _ => true
  | _ + 1, Solidity.Ty.ufixed _ _ => true
  | _ + 1, Solidity.Ty.bytesN _ => true
  | _ + 1, Solidity.Ty.fixedBytes _ => true
  | fuel + 1, Solidity.Ty.array element size =>
      -- solc `typeSupportedByOldABIEncoder` (TypeChecker.cpp:61-67): an array is
      -- rejected only when its base type is unsupported OR the base is itself a
      -- dynamically-sized array. A nested array element is therefore allowed
      -- iff it is STATICALLY sized (`some _`) and its own element is a valid
      -- packed element shape. This keeps `uint[2][3]`/`uint[2][2][2]` accepted
      -- while rejecting `uint[][3]`/`uint[2][][2]` (dynamic inner dimension).
      match size with
      | some _ => Ty.isAbiEncodePackedArrayElementShape types fuel element
      | none => false
  | fuel + 1, Solidity.Ty.user path =>
      if types.isContractPath path || types.isEnumPath path then
        true
      else
        match types.lookupUserValueType? path with
        | some underlying =>
            Ty.isAbiEncodePackedArrayElementShape types fuel underlying
        | none => false
  | _ + 1, Solidity.Ty.functionWithLocations _ _ _ _ _ visibility =>
      visibility == Solidity.Visibility.external_
  | _ + 1, _ => false

end

def CheckedExpr.expectAbiEncodePackedEncodable (types : TypeContext)
    (expr : CheckedExpr) :
    Except TypeError Unit := do
  -- solc rejects a bare number/rational literal in *packed* encoding:
  -- "Cannot perform packed encoding for a literal. Please convert it to an
  -- explicit type first." A number literal (`1`, `1+1`, `-1`) has no packed
  -- byte width, so it must be given an explicit type (`uint8(1)`), a typed
  -- variable, etc. Note this is packed-specific: `abi.encode(1)` (non-packed)
  -- is fine, and bool/string/hex/address/enum literals are also accepted
  -- because they carry a definite packed width. The `Ty`-only shape gate below
  -- cannot see this — a number literal is typed `uint256` — so inspect the
  -- source expression, mirroring the `exprIsStringLiteral` precedent.
  require (!(exprIsUntypedNumberLiteralExpression expr.source && expr.ty.isNumeric))
    (TypeError.invalidAbiCall
      "Cannot perform packed encoding for a literal. Please convert it to an explicit type first.")
  expr.expectAbiEncodable types
  require (Ty.isAbiEncodePackedArgShape types 64 expr.ty)
    (TypeError.invalidAbiType expr.ty)

def CheckedExpr.expectBytesLike (expr : CheckedExpr) :
    Except TypeError Unit :=
  expr.expectAssignableTo Solidity.Ty.bytes

def CheckedExpr.expectStringLike (expr : CheckedExpr) :
    Except TypeError Unit :=
  expr.expectAssignableTo Solidity.Ty.string

def checkAbiEncodableArgs (types : TypeContext) :
    List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      expr.expectAbiEncodable types
      checkAbiEncodableArgs types rest

def checkAbiEncodePackedArgs (types : TypeContext) :
    List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      expr.expectAbiEncodePackedEncodable types
      checkAbiEncodePackedArgs types rest

/-- A syntactic string-literal expression (`"abc"` or `unicode"abc"`).
solc types these as `StringLiteralType`, which is implicitly convertible to
both `bytes32` and `bytes memory`, so they are valid `bytes.concat` arguments —
unlike `string`-typed *values* (variables / calldata / return values), which
solc rejects (Error 8015). This frontend types both forms as `Ty.string`, so a
`Ty`-only gate cannot tell them apart; inspect the argument expression. -/
def exprIsStringLiteral : Solidity.Expr -> Bool
  | Solidity.Expr.literal (Solidity.Literal.string _) => true
  | Solidity.Expr.literal (Solidity.Literal.unicodeString _) => true
  | _ => false

/-- A `bytes.concat` argument is valid when it is `bytes`, a `bytesN`/fixed-bytes
value (`N ≤ 32`), or a *string literal*. A `string`-typed non-literal value is
rejected, matching solc's `typeCheckBytesConcatFunction`. -/
def checkBytesConcatArgs : List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      let ok :=
        match expr.ty with
        | Solidity.Ty.string => exprIsStringLiteral expr.source
        | ty => Solidity.Executable.Ty.isBytesConcatArg ty
      require ok (TypeError.invalidAbiType expr.ty)
      checkBytesConcatArgs rest

def checkStringConcatArgs : List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      require (Solidity.Executable.Ty.isStringConcatArg expr.ty)
        (TypeError.invalidAbiType expr.ty)
      checkStringConcatArgs rest

def checkAbiDecodeTupleItems (types : TypeContext) :
    List Solidity.TupleItem -> Except TypeError (List Ty)
  | [] => Except.ok []
  | Solidity.TupleItem.value
      (Solidity.Expr.typeName ty) :: rest => do
      checkTy types ty
      require (TypeContext.isAbiEncodable types ty)
        (TypeError.invalidAbiType ty)
      require (TypeContext.abiCoderSupports types ty)
        (TypeError.invalidAbiType ty)
      let tail ← checkAbiDecodeTupleItems types rest
      Except.ok (ty :: tail)
  | _ :: _ =>
      Except.error
        (TypeError.invalidAbiCall "abi.decode expects type names")

def checkAbiDecodeTypesExpr (types : TypeContext) :
    Solidity.Expr -> Except TypeError (List Ty)
  | Solidity.Expr.typeName ty => do
      checkTy types ty
      require (TypeContext.isAbiEncodable types ty)
        (TypeError.invalidAbiType ty)
      require (TypeContext.abiCoderSupports types ty)
        (TypeError.invalidAbiType ty)
      Except.ok [ty]
  | Solidity.Expr.tuple items =>
      checkAbiDecodeTupleItems types items
  | _ =>
      Except.error
        (TypeError.invalidAbiCall "abi.decode expects a type expression")

def checkBuiltinIdentCall (env : CheckEnv) (name : Name)
    (argInfos : List ArgInfo) (checkedArgs : List CheckedExpr) :
    Except TypeError (Option Ty) :=
  if name == "gasleft" then do
    requireNoNamedArgs "gasleft" argInfos
    requireCallMutabilityAllowed env Solidity.StateMutability.view
    require (checkedArgs.length == 0)
      (TypeError.arityMismatch "gasleft" 0 checkedArgs.length)
    Except.ok (some (Solidity.Ty.uint 256))
  else if name == "blockhash" || name == "blobhash" then do
    requireNoNamedArgs name argInfos
    requireCallMutabilityAllowed env Solidity.StateMutability.view
    if name == "blobhash" then
      requireCancunOrLater env "blobhash"
    else
      Except.ok ()
    match checkedArgs with
    | [number] => do
        number.expectAssignableTo (Solidity.Ty.uint 256)
        Except.ok (some (Solidity.Ty.bytesN 32))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "addmod" || name == "mulmod" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [lhs, rhs, modulus] => do
        lhs.expectAssignableTo (Solidity.Ty.uint 256)
        rhs.expectAssignableTo (Solidity.Ty.uint 256)
        modulus.expectAssignableTo (Solidity.Ty.uint 256)
        -- solc's constant evaluator (ConstantEvaluator.cpp) folds the modulus
        -- argument and raises Error 4195 "Arithmetic modulo zero" whenever it
        -- folds to a constant zero — regardless of whether the other operands
        -- are constant. Mirror the div/mod mechanism: reject a modulus whose
        -- constant fold (`numberLiteralRat?`, catching `0`, `1-1`, `2*0`) is
        -- zero. A non-constant modulus (fold `none`) stays a runtime Panic 0x12.
        require
          (match Solidity.Executable.Expr.numberLiteralRat? modulus.source with
           | some value => value.num != 0
           | none => true)
          (TypeError.unsupported (name ++ " with constant zero modulus"))
        Except.ok (some (Solidity.Ty.uint 256))
    | _ => Except.error (TypeError.arityMismatch name 3 checkedArgs.length)
  else if name == "keccak256" || name == "sha256" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [payload] => do
        payload.expectBytesLike
        Except.ok (some (Solidity.Ty.bytesN 32))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "erc7201" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [id] => do
        id.expectStringLike
        Except.ok (some (Solidity.Ty.uint 256))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "ripemd160" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [payload] => do
        payload.expectBytesLike
        Except.ok (some (Solidity.Ty.bytesN 20))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "ecrecover" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [hash, v, r, s] => do
        hash.expectAssignableTo (Solidity.Ty.bytesN 32)
        v.expectAssignableTo (Solidity.Ty.uint 8)
        r.expectAssignableTo (Solidity.Ty.bytesN 32)
        s.expectAssignableTo (Solidity.Ty.bytesN 32)
        Except.ok (some (Solidity.Ty.address false))
    | _ => Except.error (TypeError.arityMismatch name 4 checkedArgs.length)
  else if name == "assert" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [cond] => do
        cond.expectBool
        Except.ok (some (Solidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "require" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [cond] => do
        cond.expectBool
        Except.ok (some (Solidity.Ty.tuple []))
    | [cond, reason] => do
        cond.expectBool
        reason.expectStringLike
        Except.ok (some (Solidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 2 checkedArgs.length)
  else if name == "revert" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [] => Except.ok (some (Solidity.Ty.tuple []))
    | [reason] => do
        reason.expectStringLike
        Except.ok (some (Solidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "selfdestruct" then do
    requireNoNamedArgs name argInfos
    requireLogOrCreateAllowed env "selfdestruct in view or pure function"
    match checkedArgs with
    | [recipient] => do
        recipient.expectAssignableToIn env.types
          (Solidity.Ty.address true)
        Except.ok (some (Solidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else
    Except.ok none

def checkedExprsAsPositionalArgInfos : List CheckedExpr -> List ArgInfo
  | [] => []
  | expr :: rest => (none, expr.ty) :: checkedExprsAsPositionalArgInfos rest

def checkedExprsAsPositionalCheckedArgInfos :
    List CheckedExpr -> List CheckedArgInfo
  | [] => []
  | expr :: rest =>
      (none, expr) :: checkedExprsAsPositionalCheckedArgInfos rest

def checkCheckedExprsAssignableToFor (types : TypeContext) (what : String) :
    List CheckedExpr -> List Ty ->
    Except TypeError Unit
  | [], [] => Except.ok ()
  | expr :: exprRest, ty :: tyRest => do
      expr.expectAssignableToIn types ty
      checkCheckedExprsAssignableToFor types what exprRest tyRest
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch what expected.length actual.length)

-- As `checkCheckedExprsAssignableToFor`, but applies the inline-array-literal
-- bottom-up widen check (`arrayLiteralFixedWidenCheck`) per element. Used at the
-- argument-position wrappers so a widened fixed-array argument (e.g. passing
-- `[1,2,3]` for a `uint256[3]` parameter) is rejected exactly as solc does,
-- while ordinary per-element array validation inside `checkExpr` keeps using the
-- plain `checkCheckedExprsAssignableToFor` above.
def checkCheckedArgsAssignableWidenFor (types : TypeContext) (what : String) :
    List CheckedExpr -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | expr :: exprRest, ty :: tyRest => do
      arrayLiteralFixedWidenCheck types expr ty
      checkCheckedArgsAssignableWidenFor types what exprRest tyRest
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch what expected.length actual.length)

def checkCheckedExprsAssignableTo (types : TypeContext) :
    List CheckedExpr -> List Ty ->
    Except TypeError Unit :=
  checkCheckedExprsAssignableToFor types "abi.encodeCall"

def checkCheckedExprsStorageRefsFor (what : String) :
    List CheckedExpr -> List Bool -> Except TypeError Unit
  | [], [] => Except.ok ()
  | expr :: exprRest, needsStorage :: storageRest => do
      require (!needsStorage || expr.stateLValue)
        (TypeError.unsupported
          (what ++ " expects an existing storage reference"))
      checkCheckedExprsStorageRefsFor what exprRest storageRest
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch what expected.length actual.length)

def checkCheckedExprsDataLocationsFor (what : String) :
    List CheckedExpr ->
    List (Option Solidity.DataLocation) ->
    Except TypeError Unit
  | _, [] => Except.ok ()
  | expr :: exprRest, expected :: expectedRest => do
      expr.expectLocationAssignableTo expr.ty expected
      checkCheckedExprsDataLocationsFor what exprRest expectedRest
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch what expected.length actual.length)

def checkCheckedExprsReferenceLocationsFor (what : String)
    (actual : List CheckedExpr) (storageRefs : List Bool)
    (locations : List (Option Solidity.DataLocation)) :
    Except TypeError Unit := do
  checkCheckedExprsStorageRefsFor what actual storageRefs
  checkCheckedExprsDataLocationsFor what actual locations

def checkCheckedArgsAssignableToSignature
    (types : TypeContext) (what : String)
    (paramNames : List (Option Name)) (params : List Ty)
    (args : List Solidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  match CheckedArgInfos.ordered? paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedArgsAssignableWidenFor types what ordered params
  | none =>
      Except.error
        (TypeError.arityMismatch what params.length checkedArgs.length)

def checkCheckedArgsAssignableToFunctionSig
    (types : TypeContext) (what : String) (sig : FunctionSig)
    (args : List Solidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered => do
      checkCheckedArgsAssignableWidenFor types what ordered sig.params
      checkCheckedExprsReferenceLocationsFor what ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch what sig.params.length checkedArgs.length)

def checkArrayMutationCall? (env : CheckEnv)
    (expr target : Solidity.Expr) (member : Name)
    (argInfos : List ArgInfo) (checkedArgs : List CheckedExpr)
    (targetChecked : CheckedExpr) :
    Except TypeError (Option CheckedExpr) := do
  if member == "push" || member == "pop" then
    if targetChecked.ty.hasArrayMutationMemberSurface then
      requireNoNamedArgs member argInfos
      targetChecked.expectStorageMutationTarget target
      requireStateWriteAllowed env
      match targetChecked.ty.dynamicStorageArrayElement? with
      | some element =>
          if member == "push" then
            match checkedArgs with
            | [] =>
                Except.ok
                  (some
                    { source := expr
                      ty := element
                      lvalue := true
                      stateLValue := targetChecked.stateLValue
                      dataLocation? :=
                        some Solidity.DataLocation.storage })
            | [value] => do
                value.expectAssignableToIn env.types element
                Except.ok
                  (some
                    { source := expr
                      ty := Solidity.Ty.tuple []
                      lvalue := false })
            | _ =>
                Except.error
                  (TypeError.arityMismatch "push" 1 checkedArgs.length)
          else
            match checkedArgs with
            | [] =>
                Except.ok
                  (some
                    { source := expr
                      ty := Solidity.Ty.tuple []
                      lvalue := false })
            | _ =>
                Except.error
                  (TypeError.arityMismatch "pop" 0 checkedArgs.length)
      | none =>
          Except.error (TypeError.unsupported ("member call " ++ member))
    else
      Except.ok none
  else
    Except.ok none

def StructDecl.fieldNames (decl : Solidity.StructDecl) :
    List (Option Name) :=
  decl.fields.map (fun field => some field.name)

def StructDecl.fieldTys (decl : Solidity.StructDecl) :
    List Ty :=
  decl.fields.map Solidity.StructField.ty

def checkStructConstructorArgs
    (types : TypeContext) (decl : Solidity.StructDecl)
    (args : List Solidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  let ordered? :=
    CheckedArgInfos.ordered? (StructDecl.fieldNames decl)
      (checkedArgInfosFull args checkedArgs)
  match ordered? with
  | some ordered =>
      checkCheckedArgsAssignableWidenFor
        types ("struct constructor " ++ decl.name) ordered
        (StructDecl.fieldTys decl)
  | none => Except.error (TypeError.invalidStructConstructor decl.name)

def functionPointerSig (name : Name) (params : List Ty)
    (paramLocations : List (Option Solidity.DataLocation))
    (returns : List Ty)
    (returnLocations : List (Option Solidity.DataLocation))
    (mutability : Solidity.StateMutability)
    (visibility : Solidity.Visibility) : FunctionSig :=
  { name := name
    params := params
    paramNames := List.replicate params.length none
    paramStorageRefs :=
      paramLocations.map (fun location =>
        location == some Solidity.DataLocation.storage)
    paramDataLocations := paramLocations
    returns := returns
    returnStorageRefs :=
      returnLocations.map (fun location =>
        location == some Solidity.DataLocation.storage)
    returnDataLocations := returnLocations
    visibility := some visibility
    mutability := mutability }

def functionPointerSig? (name : Name) : Ty -> Option FunctionSig
  | Solidity.Ty.functionWithLocations params paramLocations returns
      returnLocations mutability visibility =>
      some
        (functionPointerSig name params paramLocations returns returnLocations
          mutability visibility)
  | _ => none

def requireExternalEncodeCallPointer
    (sig : FunctionSig) : Except TypeError FunctionSig := do
  require (sig.visibility == some Solidity.Visibility.external_)
    (TypeError.invalidAbiCall
      "abi.encodeCall expects an external function pointer")
  Except.ok sig

def resolveEncodeCallFunction (env : CheckEnv)
    (pointer : Solidity.Expr)
    (argInfos : List CheckedArgInfo) :
    Except TypeError FunctionSig :=
  match pointer with
  | Solidity.Expr.member
      (Solidity.Expr.typeName (Solidity.Ty.user path))
      member => do
      require (env.types.isContractValuePath path)
        (TypeError.invalidAbiCall
          "abi.encodeCall cannot use a library function")
      let sig ←
        env.types.resolveContractMemberFunctionChecked path member argInfos
      require sig.externallyCallable
        (TypeError.invalidAbiCall
          "abi.encodeCall expects an external function")
      Except.ok sig
  | Solidity.Expr.member target member => do
      let targetChecked ← checkCallTargetExpr env target
      match targetChecked.ty with
      | Solidity.Ty.user path => do
          require (env.types.isContractValuePath path)
            (TypeError.invalidAbiCall
              "abi.encodeCall expects a contract function value")
          let sig ←
            env.types.resolveContractMemberFunctionChecked path member
              argInfos
          require sig.externallyCallable
            (TypeError.invalidAbiCall
              "abi.encodeCall expects an external function")
          Except.ok sig
      | other =>
          Except.error
            (TypeError.expectedType
              (Solidity.Ty.address false) other)
  | Solidity.Expr.ident name => do
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          if isState then
            requireStateReadAllowed env
          else
            Except.ok ()
          match functionPointerSig? name ty with
          | some sig => requireExternalEncodeCallPointer sig
          | none =>
              Except.error
                (TypeError.invalidAbiCall
                  "abi.encodeCall expects a function pointer")
      | none =>
          Except.error
            (TypeError.invalidAbiCall
              "abi.encodeCall expects a function pointer")
  | _ =>
      Except.error
        (TypeError.invalidAbiCall
          "abi.encodeCall expects a function pointer")

def requireCreatableContractDecl
    (decl : Solidity.ContractDecl) : Except TypeError Unit := do
  require (decl.kind == Solidity.ContractKind.contract)
    (TypeError.invalidContractHeader
      "contract creation target is not a contract")
  require (!decl.abstract)
    (TypeError.invalidContractHeader
      "contract creation target is abstract")

def checkInternalFunctionValueAssignable?
    (env : CheckEnv) (expr : Solidity.Expr) (expected : Ty) :
    Option (Except TypeError Unit) :=
  match expr, expected with
  | Solidity.Expr.ident name,
    Solidity.Ty.functionWithLocations _ _ _ _ _
      Solidity.Visibility.internal_ =>
      match env.lookupVar? name with
      | some _ => none
      | none =>
          some
            (do
              let _ ←
                FunctionSigs.resolveInternalFunctionValueAssignableTo
                  env.types env.functions name expected
              Except.ok ())
  | _, _ => none

def exprContextualTyFuel? (env : CheckEnv) :
    Nat -> Solidity.Expr -> Option Ty
  | 0, _ => none
  | fuel + 1, expr =>
      match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty => some (env.qualifyCurrentLocalUserTypes ty)
      | none =>
          match expr with
          | Solidity.Expr.unary
              Solidity.UnaryOp.bitNot inner
          | Solidity.Expr.unary
              Solidity.UnaryOp.neg inner
          | Solidity.Expr.unary
              Solidity.UnaryOp.preIncrement inner
          | Solidity.Expr.unary
              Solidity.UnaryOp.preDecrement inner
          | Solidity.Expr.unary
              Solidity.UnaryOp.postIncrement inner
          | Solidity.Expr.unary
              Solidity.UnaryOp.postDecrement inner =>
              exprContextualTyFuel? env fuel inner
          | Solidity.Expr.assign lhs _ _ =>
              exprContextualTyFuel? env fuel lhs
          | Solidity.Expr.binary op lhs _ =>
              match op with
              | Solidity.BinaryOp.lt
              | Solidity.BinaryOp.gt
              | Solidity.BinaryOp.le
              | Solidity.BinaryOp.ge
              | Solidity.BinaryOp.eq
              | Solidity.BinaryOp.ne
              | Solidity.BinaryOp.boolAnd
              | Solidity.BinaryOp.boolOr =>
                  some Solidity.Ty.bool
              | _ => exprContextualTyFuel? env fuel lhs
          | Solidity.Expr.ternary _ thenExpr _ =>
              exprContextualTyFuel? env fuel thenExpr
          | Solidity.Expr.member base "balance" =>
              match exprContextualTyFuel? env fuel base with
              | some _ => some (Solidity.Ty.uint 256)
              | none => none
          | Solidity.Expr.member base "code" =>
              match exprContextualTyFuel? env fuel base with
              | some _ => some Solidity.Ty.bytes
              | none => none
          | Solidity.Expr.member base "codehash" =>
              match exprContextualTyFuel? env fuel base with
              | some _ => some (Solidity.Ty.bytesN 32)
              | none => none
          | Solidity.Expr.member base "length" =>
              match exprContextualTyFuel? env fuel base with
              | some _ => some (Solidity.Ty.uint 256)
              | none => none
          | Solidity.Expr.member base member => do
              let baseTy ← exprContextualTyFuel? env fuel base
              match baseTy with
              | Solidity.Ty.user path =>
                  let structDecl ← env.types.lookupStruct? path
                  let field ←
                    structDecl.fields.find?
                      (fun field => field.name == member)
                  some (env.qualifyStructFieldTy path field.ty)
              | _ => none
          | Solidity.Expr.index base indexExpr => do
              let baseTy ← exprContextualTyFuel? env fuel base
              match Ty.fixedBytesSize? baseTy with
              | some _ => some (Solidity.Ty.bytesN 1)
              | none =>
                  match baseTy with
                  | Solidity.Ty.bytes =>
                      some (Solidity.Ty.bytesN 1)
                  | Solidity.Ty.array elementTy _ =>
                      some elementTy
                  | Solidity.Ty.mapping _ valueTy =>
                      some valueTy
                  | Solidity.Ty.tuple elements => do
                      let index ←
                        Solidity.Executable.Expr.numberLiteralNat?
                          indexExpr
                      Solidity.Executable.listGet? elements index
                  | _ => none
          | Solidity.Expr.slice base _ _ => do
              let baseTy ← exprContextualTyFuel? env fuel base
              match baseTy with
              | Solidity.Ty.bytes =>
                  some Solidity.Ty.bytes
              | Solidity.Ty.string =>
                  some Solidity.Ty.string
              | Solidity.Ty.array elementTy _ =>
                  some (Solidity.Ty.array elementTy none)
              | _ => none
          | _ => none

def exprContextualTy? (env : CheckEnv)
    (expr : Solidity.Expr) : Option Ty :=
  exprContextualTyFuel? env 128 expr

def exprContextuallyAssignableToFuel
    (env : CheckEnv) :
    Nat -> Solidity.Expr -> Ty -> Bool
  | 0, _, _ => false
  | fuel + 1, Solidity.Expr.array elements,
      Solidity.Ty.array elementTy (some size) =>
      -- solc types the inline array literal independently (bottom-up) and then
      -- requires an IDENTICAL element type for the fixed→fixed memory-array
      -- conversion (`ArrayType::isImplicitlyConvertibleTo`, non-copy branch): no
      -- implicit element widening. When every element is a bare number literal
      -- the bottom-up type is `inlineArrayBottomUpTy?`; accept iff it equals the
      -- target (which also admits `uint8[3] = [1,2,3]`). Arrays with a typed /
      -- variable element yield `none` here and are handled by the ordinary path.
      elements.length == size &&
        (match inlineArrayBottomUpTyFuel? fuel (Solidity.Expr.array elements) with
         | some (Solidity.Ty.array litElementTy (some litSize)) =>
             litSize == size &&
               env.qualifyCurrentLocalUserTypes litElementTy ==
                 env.qualifyCurrentLocalUserTypes elementTy
         | _ => false)
  | fuel + 1,
      Solidity.Expr.ternary cond thenExpr elseExpr,
      expected =>
      exprContextuallyAssignableToFuel env fuel cond
        Solidity.Ty.bool &&
        exprContextuallyAssignableToFuel env fuel thenExpr expected &&
          exprContextuallyAssignableToFuel env fuel elseExpr expected
  | _, expr, expected =>
      match checkInternalFunctionValueAssignable? env expr expected with
      | some (Except.ok _) => true
      | _ =>
          match exprContextualTy? env expr with
          | some actual =>
              let actual := env.qualifyCurrentLocalUserTypes actual
              let expected := env.qualifyCurrentLocalUserTypes expected
              actual == expected ||
                (exprIsUntypedImplicitLiteralExpression expr &&
                  implicitLiteralFits expected expr)
          | none => false

def exprContextuallyAssignableTo
    (env : CheckEnv) (expr : Solidity.Expr) (expected : Ty) :
    Bool :=
  exprContextuallyAssignableToFuel env 128 expr expected

def exprIsContextualFixedArrayExpr
    (env : CheckEnv) (expr : Solidity.Expr) (expected : Ty) :
    Bool :=
  match expr, expected with
  | Solidity.Expr.array _,
    Solidity.Ty.array _ (some _) =>
      exprContextuallyAssignableTo env expr expected
  | Solidity.Expr.ternary _ _ _,
    Solidity.Ty.array _ (some _) =>
      exprContextuallyAssignableTo env expr expected
  | _, _ => false

def exprHasStorageRefRoot (env : CheckEnv) :
    Solidity.Expr -> Bool
  | Solidity.Expr.ident name =>
      (env.isStateName name && !env.isLocalName name) ||
        env.isLocalStorageRef name
  | Solidity.Expr.member base _ =>
      exprHasStorageRefRoot env base
  | Solidity.Expr.index base _ =>
      exprHasStorageRefRoot env base
  | _ => false

def exprContextuallyStorageOk
    (env : CheckEnv) (expr : Solidity.Expr)
    (needsStorage : Bool) : Bool :=
  if needsStorage then
    exprHasStorageRefRoot env expr
  else
    true

def exprsContextuallyMatchParamTys (env : CheckEnv) :
    List Solidity.Expr -> List Ty -> Bool
  | [], [] => true
  | expr :: exprRest, ty :: tyRest =>
      exprContextuallyAssignableTo env expr ty &&
        exprsContextuallyMatchParamTys env exprRest tyRest
  | _, _ => false

def exprsContextuallyMatchParams (env : CheckEnv) :
    List Solidity.Expr -> List Ty -> List Bool -> Bool
  | [], [], [] => true
  | expr :: exprRest, ty :: tyRest, storage :: storageRest =>
      exprContextuallyAssignableTo env expr ty &&
        exprContextuallyStorageOk env expr storage &&
        exprsContextuallyMatchParams env exprRest tyRest storageRest
  | exprs, tys, [] =>
      exprsContextuallyMatchParamTys env exprs tys
  | _, _, _ => false

def FunctionSig.contextuallyMatchesArgs
    (env : CheckEnv) (sig : FunctionSig)
    (args : List Solidity.Arg) : Bool :=
  match
      Solidity.Executable.Args.toExprsForParamNames?
        sig.paramNames args with
  | some exprs =>
      exprsContextuallyMatchParams env exprs sig.params
        sig.paramStorageRefs
  | none => false

def ModifierSig.contextuallyMatchesArgs
    (env : CheckEnv) (sig : ModifierSig)
    (args : List Solidity.Arg) : Bool :=
  match
      Solidity.Executable.Args.toExprsForParamNames?
        sig.paramNames args with
  | some exprs =>
      exprsContextuallyMatchParams env exprs sig.params
        sig.paramStorageRefs
  | none => false

def EventSig.contextuallyMatchesArgs
    (env : CheckEnv) (sig : EventSig)
    (args : List Solidity.Arg) : Bool :=
  match
      Solidity.Executable.Args.toExprsForParamNames?
        sig.paramNames args with
  | some exprs => exprsContextuallyMatchParamTys env exprs sig.params
  | none => false

def ErrorSig.contextuallyMatchesArgs
    (env : CheckEnv) (sig : ErrorSig)
    (args : List Solidity.Arg) : Bool :=
  match
      Solidity.Executable.Args.toExprsForParamNames?
        sig.paramNames args with
  | some exprs => exprsContextuallyMatchParamTys env exprs sig.params
  | none => false

namespace FunctionSigs

def resolveContextualLoop (env : CheckEnv)
    (target : Name) (args : List Solidity.Arg) :
    Option FunctionSig -> List FunctionSig -> Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.contextuallyMatchesArgs env args then
        match found? with
        | none => resolveContextualLoop env target args (some sig) rest
        | some found =>
            if FunctionSig.sameResolutionTarget found sig then
              resolveContextualLoop env target args (some found) rest
            else
              Except.error (TypeError.ambiguousFunction target)
      else
        resolveContextualLoop env target args found? rest

def resolveContextual (env : CheckEnv)
    (functions : List FunctionSig) (target : Name)
    (args : List Solidity.Arg) : Except TypeError FunctionSig :=
  resolveContextualLoop env target args none functions

end FunctionSigs

def TypeContext.resolveContractMemberFunctionContextual
    (env : CheckEnv) (path : Path) (member : Name)
    (args : List Solidity.Arg) : Except TypeError FunctionSig :=
  match env.types.lookupContractExternalFunctionSigs? path with
  | some sigs => FunctionSigs.resolveContextual env sigs member args
  | none => Except.error (TypeError.unknownFunction member)

def tupleItemsAsPositionalArgs :
    List Solidity.TupleItem ->
    Except TypeError (List Solidity.Arg)
  | [] => Except.ok []
  | Solidity.TupleItem.hole :: _ =>
      Except.error
        (TypeError.invalidAbiCall
          "abi.encodeCall argument tuple cannot contain holes")
  | Solidity.TupleItem.value expr :: rest => do
      let tail ← tupleItemsAsPositionalArgs rest
      Except.ok (Solidity.Arg.positional expr :: tail)

def resolveEncodeCallFunctionContextual (env : CheckEnv)
    (pointer : Solidity.Expr)
    (args : List Solidity.Arg) :
    Except TypeError FunctionSig :=
  match pointer with
  | Solidity.Expr.member
      (Solidity.Expr.typeName (Solidity.Ty.user path))
      member => do
      require (env.types.isContractValuePath path)
        (TypeError.invalidAbiCall
          "abi.encodeCall cannot use a library function")
      let sig ←
        TypeContext.resolveContractMemberFunctionContextual env path member
          args
      require sig.externallyCallable
        (TypeError.invalidAbiCall
          "abi.encodeCall expects an external function")
      Except.ok sig
  | Solidity.Expr.member target member => do
      let targetChecked ← checkCallTargetExpr env target
      match targetChecked.ty with
      | Solidity.Ty.user path => do
          require (env.types.isContractValuePath path)
            (TypeError.invalidAbiCall
              "abi.encodeCall expects a contract function value")
          let sig ←
            TypeContext.resolveContractMemberFunctionContextual env path member
              args
          require sig.externallyCallable
            (TypeError.invalidAbiCall
              "abi.encodeCall expects an external function")
          Except.ok sig
      | other =>
          Except.error
            (TypeError.expectedType
              (Solidity.Ty.address false) other)
  | Solidity.Expr.ident name => do
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          if isState then
            requireStateReadAllowed env
          else
            Except.ok ()
          match functionPointerSig? name ty with
          | some sig => requireExternalEncodeCallPointer sig
          | none =>
              Except.error
                (TypeError.invalidAbiCall
                  "abi.encodeCall expects a function pointer")
      | none =>
          Except.error
            (TypeError.invalidAbiCall
              "abi.encodeCall expects a function pointer")
  | _ =>
      Except.error
        (TypeError.invalidAbiCall
          "abi.encodeCall expects a function pointer")

namespace ModifierSigs

def resolveContextualLoop (env : CheckEnv)
    (target : Name) (args : List Solidity.Arg) :
    Option ModifierSig -> List ModifierSig -> Except TypeError ModifierSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.contextuallyMatchesArgs env args then
        match found? with
        | none => resolveContextualLoop env target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveContextualLoop env target args found? rest

def resolveContextual (env : CheckEnv)
    (modifiers : List ModifierSig) (target : Name)
    (args : List Solidity.Arg) : Except TypeError ModifierSig :=
  resolveContextualLoop env target args none modifiers

end ModifierSigs

namespace EventSigs

def resolveContextualLoop (env : CheckEnv)
    (target : Name) (args : List Solidity.Arg) :
    Option EventSig -> List EventSig -> Except TypeError EventSig
  | none, [] => Except.error (TypeError.unknownEvent target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.contextuallyMatchesArgs env args then
        match found? with
        | none => resolveContextualLoop env target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveContextualLoop env target args found? rest

def resolveContextual (env : CheckEnv)
    (events : List EventSig) (target : Name)
    (args : List Solidity.Arg) : Except TypeError EventSig :=
  resolveContextualLoop env target args none events

end EventSigs

namespace ErrorSigs

def resolveContextualLoop (env : CheckEnv)
    (target : Name) (args : List Solidity.Arg) :
    Option ErrorSig -> List ErrorSig -> Except TypeError ErrorSig
  | none, [] => Except.error (TypeError.unknownError target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.contextuallyMatchesArgs env args then
        match found? with
        | none => resolveContextualLoop env target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveContextualLoop env target args found? rest

def resolveContextual (env : CheckEnv)
    (errors : List ErrorSig) (target : Name)
    (args : List Solidity.Arg) : Except TypeError ErrorSig :=
  resolveContextualLoop env target args none errors

end ErrorSigs

mutual

def checkExpr (env : CheckEnv) :
    Solidity.Expr -> Except TypeError CheckedExpr
  | expr@(Solidity.Expr.literal literal) =>
      match literalTy? literal with
      | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
      | none => Except.error (TypeError.unsupported "literal")
  | expr@(Solidity.Expr.ident "this") => do
      requireStateReadAllowed env
      match env.currentContract with
      | some path =>
          Except.ok
            { source := expr
              ty := Solidity.Ty.user path
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unknownIdentifier "this")
  | expr@(Solidity.Expr.ident name) =>
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          let isStorageRef := env.isLocalStorageRef name
          let isConstant := env.isConstantName name
          let isImmutable := env.isImmutableName name
          let dataLocation? :=
            if Ty.needsDataLocation env.types ty then
              if isState || isStorageRef then
                some Solidity.DataLocation.storage
              else
                env.lookupLocalDataLocation? name
            else
              none
          if isState then
            requireStateReadAllowed env
          else
            Except.ok ()
          env.types.requireNoFixedPointValue ty "read"
          Except.ok
            { source := expr
              ty := ty
              lvalue := !isConstant && (!isImmutable || env.inConstructor)
              stateLValue := isState || isStorageRef
              dataLocation? := dataLocation? }
      | none =>
          match FunctionSigs.resolveInternalFunctionValueByName
              env.functions name with
          | Except.ok sig =>
              match FunctionSig.internalFunctionValueTy? sig with
              | some ty =>
                  Except.ok
                    { source := expr
                      ty := ty
                      lvalue := false
                      stateLValue := false }
              | none => Except.error (TypeError.unknownIdentifier name)
          | Except.error _ => Except.error (TypeError.unknownIdentifier name)
  | expr@(Solidity.Expr.typeName ty) => do
      checkTy env.types ty
      Except.ok { source := expr, ty := ty, lvalue := false }
  | expr@(Solidity.Expr.member
      (Solidity.Expr.ident name) "selector") => do
      match ErrorSigs.resolveByName env.errors name with
      | Except.ok _ =>
          Except.ok
            { source := expr
              ty := Solidity.Ty.bytesN 4
              lvalue := false
              stateLValue := false }
      | Except.error _ => do
          match EventSigs.resolveByName env.events name with
          | Except.ok sig =>
              require (!sig.anonymous)
                (TypeError.unsupported "anonymous event selector")
              Except.ok
                { source := expr
                  ty := Solidity.Ty.bytesN 32
                  lvalue := false
                  stateLValue := false }
          | Except.error _ => do
              let baseChecked ←
                checkExpr env (Solidity.Expr.ident name)
              match baseChecked.ty with
              | Solidity.Ty.functionWithLocations _ _ _ _ _
                  Solidity.Visibility.external_ =>
                  Except.ok
                    { source := expr
                      ty := Solidity.Ty.bytesN 4
                      lvalue := false
                      stateLValue := false }
              | _ => Except.error (TypeError.unsupported "member selector")
  | expr@(Solidity.Expr.member
      (Solidity.Expr.member (Solidity.Expr.ident "this") member) "selector") =>
      -- solc `ViewPureChecker.cpp:357-370`: `this.f.selector` is special-cased
      -- as a compile-time constant — the `this` sub-expression is never visited,
      -- so it contributes NO state read and the expression stays Pure. Resolving
      -- the external-callable function value of the current contract here (rather
      -- than recursing into `this`, which would `requireStateReadAllowed`) both
      -- keeps `this.f.selector` pure and still rejects a private/internal `f`
      -- ("member not found") — matching pinned solc 0.8.35. Note this only covers
      -- `.selector`; `this.f()` still routes through the state-mutability call
      -- path and remains a view/pure violation.
      match env.currentContract with
      | some path => do
          let sig ←
            env.types.resolveContractExternalFunctionValue path member
          match FunctionSig.externalFunctionValueTy? sig with
          | some _ =>
              Except.ok
                { source := expr
                  ty := Solidity.Ty.bytesN 4
                  lvalue := false
                  stateLValue := false }
          | none => Except.error (TypeError.unsupported "member selector")
      | none => Except.error (TypeError.unknownIdentifier "this")
  | expr@(Solidity.Expr.member
      (Solidity.Expr.member base member) "selector") => do
      let baseChecked ← checkExpr env base
      match baseChecked.ty with
      | Solidity.Ty.user path =>
          let receiverAllowed :=
            match base with
            | Solidity.Expr.typeName
                (Solidity.Ty.user _) =>
                env.types.isContractPath path
            | _ => env.types.isContractValuePath path
          if receiverAllowed then do
            let sig ←
              env.types.resolveContractExternalFunctionValue path member
            match FunctionSig.externalFunctionValueTy? sig with
            | some _ =>
                Except.ok
                  { source := expr
                    ty := Solidity.Ty.bytesN 4
                    lvalue := false
                    stateLValue := false }
            | none => Except.error (TypeError.unsupported "member selector")
          else do
            let fnChecked ←
              checkExpr env (Solidity.Expr.member base member)
            match fnChecked.ty with
            | Solidity.Ty.functionWithLocations _ _ _ _ _
                Solidity.Visibility.external_ =>
                Except.ok
                  { source := expr
                    ty := Solidity.Ty.bytesN 4
                    lvalue := false
                    stateLValue := false }
            | _ => Except.error (TypeError.unsupported "member selector")
      | _ => do
          let fnChecked ←
            checkExpr env (Solidity.Expr.member base member)
          match fnChecked.ty with
          | Solidity.Ty.functionWithLocations _ _ _ _ _
              Solidity.Visibility.external_ =>
              Except.ok
                { source := expr
                  ty := Solidity.Ty.bytesN 4
                  lvalue := false
                  stateLValue := false }
          | _ => Except.error (TypeError.unsupported "member selector")
  | expr@(Solidity.Expr.member
      (Solidity.Expr.member base member) "address") => do
      let baseChecked ← checkExpr env base
      match baseChecked.ty with
      | Solidity.Ty.user path =>
          let receiverAllowed :=
            match base with
            | Solidity.Expr.typeName _ => false
            | _ => env.types.isContractValuePath path
          if receiverAllowed then do
            let sig ←
              env.types.resolveContractExternalFunctionValue path member
            match FunctionSig.externalFunctionValueTy? sig with
            | some _ =>
                Except.ok
                  { source := expr
                    ty := Solidity.Ty.address false
                    lvalue := false
                    stateLValue := false }
            | none => Except.error (TypeError.unsupported "member address")
          else do
            let fnChecked ←
              checkExpr env (Solidity.Expr.member base member)
            match fnChecked.ty with
            | Solidity.Ty.functionWithLocations _ _ _ _ _
                Solidity.Visibility.external_ =>
                Except.ok
                  { source := expr
                    ty := Solidity.Ty.address false
                    lvalue := false
                    stateLValue := false }
            | _ => Except.error (TypeError.unsupported "member address")
      | _ => do
          let fnChecked ←
            checkExpr env (Solidity.Expr.member base member)
          match fnChecked.ty with
          | Solidity.Ty.functionWithLocations _ _ _ _ _
              Solidity.Visibility.external_ =>
              Except.ok
                { source := expr
                  ty := Solidity.Ty.address false
                  lvalue := false
                  stateLValue := false }
          | _ => Except.error (TypeError.unsupported "member address")
  | expr@(Solidity.Expr.member
      (Solidity.Expr.ident "msg") member) => do
      if member == "data" || member == "sig" then
        -- G10: `msg.data` is forbidden inside a `receive` function (solc
        -- TypeError 7139); receive has empty calldata.
        require (!(member == "data" && env.inReceive))
          (TypeError.unsupported "msg.data in receive function")
      else
        requireStateReadAllowed env
      -- G2: `msg.value` sets payable mutability (ViewPureChecker.cpp:404-414). It
      -- may only appear in a payable function; solc errors 5887 otherwise, but
      -- exempts internal/private functions and library functions (they cannot be
      -- payable) — `reportMutability` only fires for `isConstructor() || isPublic()`
      -- and `!libraryFunction()` (ViewPureChecker.cpp:270-294).
      if member == "value" then
        let visiblePublic :=
          match env.currentVisibility with
          | some Solidity.Visibility.public_ => true
          | some Solidity.Visibility.external_ => true
          | _ => false
        if (visiblePublic || env.inConstructor) && !env.inLibrary then
          require
            (env.currentMutability == some Solidity.StateMutability.payable)
            (TypeError.mutabilityViolation
              "msg.value in a non-payable function")
        else
          Except.ok ()
      else
        Except.ok ()
      match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false
              dataLocation? :=
                if member == "data" then
                  some Solidity.DataLocation.calldata
                else
                  none }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(Solidity.Expr.member
      (Solidity.Expr.ident "block") member) => do
      requireStateReadAllowed env
      if member == "basefee" then
        requireLondonOrLater env "block.basefee"
      else if member == "blobbasefee" then
        requireCancunOrLater env "block.blobbasefee"
      else if member == "chainid" then
        requireIstanbulOrLater env "block.chainid"
      else
        Except.ok ()
      match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(Solidity.Expr.member
      (Solidity.Expr.ident "tx") member) => do
      requireStateReadAllowed env
      match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(Solidity.Expr.member
      (Solidity.Expr.typeName ty) member) => do
      -- Member-form internal-function VALUE (`Lib.f` / `Contract.f`, boundary
      -- completion arc, member-form residue): resolved BEFORE `checkTy` because
      -- a library type name is not itself a value type. `Contract.f` is only a
      -- value use for the current contract or an ancestor; an external-facing
      -- member (`this.f`, `addr.f`) is a DIFFERENT feature handled elsewhere.
      let memberFnValue? : Option CheckedExpr :=
        match ty with
        | Solidity.Ty.user path =>
            if env.types.isLibraryPath path ||
                (env.types.isContractPath path &&
                  env.isCurrentOrAncestorContract path) then
              match env.types.resolveInternalFunctionValueMember? path member with
              | some sig =>
                  (FunctionSig.internalFunctionValueTy? sig).map
                    (fun fnTy =>
                      { source := expr
                        ty := fnTy
                        lvalue := false
                        stateLValue := false })
              | none => none
            else none
        | _ => none
      if let some checked := memberFnValue? then
        return checked
      checkTy env.types ty
      let ty := env.qualifyCurrentLocalUserTypes ty
      match ty with
      | Solidity.Ty.uint _
      | Solidity.Ty.int _ =>
          if member == "min" || member == "max" then
            Except.ok
              { source := expr
                ty := ty
                lvalue := false
                stateLValue := false }
          else
            Except.error (TypeError.unsupported ("member " ++ member))
      | Solidity.Ty.user path =>
          match env.types.lookupEnum? path with
          | some enumDecl =>
              if member == "min" || member == "max" then
                Except.ok
                  { source := expr
                    ty := ty
                    lvalue := false
                    stateLValue := false }
              else
                require (EnumDecl.hasCase enumDecl member)
                  (TypeError.unsupported ("member " ++ member))
                Except.ok
                  { source := expr
                    ty := ty
                    lvalue := false
                    stateLValue := false }
          | none =>
              match env.types.lookupContractDecl? path with
              | some contractDecl =>
                  if member == "name" then
                    Except.ok
                      { source := expr
                        ty := Solidity.Ty.string
                        lvalue := false
                        stateLValue := false }
                  else if member == "creationCode" ||
                      member == "runtimeCode" then
                    require
                      (contractDecl.kind !=
                          Solidity.ContractKind.interface &&
                        !contractDecl.abstract)
                      (TypeError.unsupported ("member " ++ member))
                    require (!env.isCurrentOrAncestorContract path)
                      (TypeError.unsupported ("member " ++ member))
                    Except.ok
                      { source := expr
                        ty := Solidity.Ty.bytes
                        lvalue := false
                        stateLValue := false }
                  else if member == "interfaceId" then
                    -- solc (Types.cpp:4271-4285): a NON-deployable contract
                    -- (interface OR abstract) exposes `interfaceId`; a
                    -- deployable concrete contract does not.
                    require
                      (contractDecl.kind ==
                          Solidity.ContractKind.interface ||
                        contractDecl.abstract)
                      (TypeError.unsupported ("member " ++ member))
                    Except.ok
                      { source := expr
                        ty := Solidity.Ty.bytesN 4
                        lvalue := false
                        stateLValue := false }
                  else
                    Except.error
                      (TypeError.unsupported ("member " ++ member))
              | none =>
                  Except.error (TypeError.unsupported ("member " ++ member))
      | _ => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(Solidity.Expr.member base member) => do
      let baseChecked ← checkExpr env base
      if baseChecked.stateLValue then
        requireStateReadAllowed env
      else
        Except.ok ()
      require (!baseChecked.arraySlice)
        (TypeError.unsupported "member on array slice")
      let checkBoundExternalFunctionMember
          (path : Solidity.Path) :
          Except TypeError CheckedExpr := do
        require (env.types.isContractValuePath path)
          (TypeError.unsupported ("member " ++ member))
        let sig ←
          env.types.resolveContractExternalFunctionValue path member
        match FunctionSig.externalFunctionValueTy? sig with
        | some ty =>
            Except.ok
              { source := expr
                ty := ty
                lvalue := false
                stateLValue := false }
        | none => Except.error (TypeError.unsupported ("member " ++ member))
      let checkNonStructMember : Except TypeError CheckedExpr := do
        if member == "balance" then
          requireStateReadAllowed env
          require baseChecked.ty.isAddressBuiltinReceiver
            (TypeError.expectedType
              (Solidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := Solidity.Ty.uint 256
              lvalue := false
              stateLValue := false }
        else if member == "code" then
          requireStateReadAllowed env
          require baseChecked.ty.isAddressBuiltinReceiver
            (TypeError.expectedType
              (Solidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := Solidity.Ty.bytes
              lvalue := false
              stateLValue := false }
        else if member == "codehash" then
          requireStateReadAllowed env
          requireConstantinopleOrLater env "address.codehash"
          require baseChecked.ty.isAddressBuiltinReceiver
            (TypeError.expectedType
              (Solidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := Solidity.Ty.bytesN 32
              lvalue := false
              stateLValue := false }
        else if member == "length" then
          require baseChecked.ty.hasLengthMember
            (TypeError.unsupported "length member for non-array value")
          Except.ok
            { source := expr
              ty := Solidity.Ty.uint 256
              lvalue := false
              stateLValue := false }
        else
          match Solidity.Executable.Expr.abiTyWithEnv?
              env.vars expr with
          | some ty =>
              Except.ok
                { source := expr
                  ty := ty
                  lvalue := false
                  stateLValue := baseChecked.stateLValue
                  dataLocation? := baseChecked.dataLocation? }
          | none => Except.error (TypeError.unsupported ("member " ++ member))
      match baseChecked.ty with
      | Solidity.Ty.user path =>
          match env.types.lookupStruct? path with
          | some structDecl =>
              match structDecl.fields.find?
                  (fun field => field.name == member) with
              | some field =>
                  Except.ok
                    { source := expr
                      ty := env.qualifyStructFieldTy path field.ty
                      lvalue := baseChecked.lvalue || baseChecked.stateLValue
                      stateLValue := baseChecked.stateLValue
                      dataLocation? := baseChecked.dataLocation? }
              | none =>
                  Except.error (TypeError.unsupported ("member " ++ member))
          | none =>
              match checkBoundExternalFunctionMember path with
              | Except.ok checked => Except.ok checked
              | Except.error _ => checkNonStructMember
      | _ => checkNonStructMember
  | expr@(Solidity.Expr.index base index) => do
      let baseChecked ← checkExpr env base
      if baseChecked.stateLValue then
        requireStateReadAllowed env
      else
        Except.ok ()
      let indexChecked ← checkExpr env index
      match baseChecked.ty with
      | Solidity.Ty.bytes =>
          indexChecked.expectAssignableTo (Solidity.Ty.uint 256)
          Except.ok
            { source := expr, ty := Solidity.Ty.bytesN 1,
              lvalue := baseChecked.lvalue || baseChecked.stateLValue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | Solidity.Ty.bytesN size =>
          indexChecked.expectAssignableTo (Solidity.Ty.uint 256)
          -- G4: compile-time out-of-bounds index on `bytesN` (solc TypeError 1859).
          -- Only a *rational-literal*-typed index is checked: solc runs this OOB
          -- check solely when the index carries a rational-literal type. A bare
          -- literal or pure arithmetic (`b[9]`, `b[2+3]`) stays rational-literal
          -- and is checked; an explicit conversion (`b[uint(9)]`) or a typed
          -- named `constant` makes the index a plain `uint256`, which solc does
          -- NOT bounds-check (runtime Panic 0x32 instead). Use the *untyped*
          -- folder so `T(x)` conversions are not folded through.
          (match Solidity.Executable.Expr.untypedNumberLiteralNat? index with
            | some i =>
                require (i < size)
                  (TypeError.unsupported "constant index out of bounds")
            | none => Except.ok ())
          Except.ok
            { source := expr, ty := Solidity.Ty.bytesN 1,
              lvalue := false }
      | Solidity.Ty.array element len? =>
          indexChecked.expectAssignableTo (Solidity.Ty.uint 256)
          -- G4: compile-time out-of-bounds index on a fixed-size array
          -- (solc TypeError 3383). Dynamic arrays (`len? = none`) are unchecked.
          -- As with `bytesN` above, this check runs only for a rational-literal
          -- index. A bare literal / pure arithmetic (`a[5]`, `a[2+3]`) is
          -- checked; an explicit conversion (`a[uint(5)]`, `a[uint(2+3)]`) or a
          -- typed `constant` yields a plain `uint256` that solc does not
          -- bounds-check (runtime Panic 0x32). Use the *untyped* folder, which
          -- folds arithmetic but not `T(x)` conversions.
          (match len?, Solidity.Executable.Expr.untypedNumberLiteralNat? index with
            | some len, some i =>
                require (i < len)
                  (TypeError.unsupported "constant index out of bounds")
            | _, _ => Except.ok ())
          Except.ok
            { source := expr
              ty := env.qualifyCurrentLocalUserTypes element
              lvalue := baseChecked.lvalue || baseChecked.stateLValue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | Solidity.Ty.tuple tys => do
          Except.error (TypeError.unsupported "tuple index")
      | Solidity.Ty.mapping key value => do
          indexChecked.expectAssignableToIn env.types key
          Except.ok
            { source := expr
              ty := env.qualifyCurrentLocalUserTypes value
              lvalue := baseChecked.lvalue || baseChecked.stateLValue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | other => Except.error (TypeError.expectedType
          (Solidity.Ty.array other none) other)
  | expr@(Solidity.Expr.slice base start? stop?) => do
      let baseChecked ← checkExpr env base
      let sliceTy ←
        match baseChecked.ty with
        | Solidity.Ty.bytes => Except.ok baseChecked.ty
        | Solidity.Ty.string => Except.ok baseChecked.ty
        | Solidity.Ty.array element none =>
            -- Index-range (slice) access is only supported for *dynamic*
            -- calldata arrays; solc rejects slicing a fixed-size array
            -- ("Index range access is only supported for dynamic calldata
            -- arrays."). Requiring `len? = none` here (the calldata-location
            -- requirement below handles memory arrays) matches that.
            Except.ok (Solidity.Ty.array element none)
        | other =>
            Except.error
              (TypeError.expectedType
                (Solidity.Ty.array other none) other)
      require
        (baseChecked.dataLocation? ==
          some Solidity.DataLocation.calldata)
        (TypeError.invalidDataLocation baseChecked.ty
          baseChecked.dataLocation?)
      match start? with
      | some start =>
          let startChecked ← checkExpr env start
          startChecked.expectAssignableToIn env.types
            (Solidity.Ty.uint 256)
      | none => Except.ok ()
      match stop? with
      | some stop =>
          let stopChecked ← checkExpr env stop
          stopChecked.expectAssignableToIn env.types
            (Solidity.Ty.uint 256)
      | none => Except.ok ()
      Except.ok
        { source := expr
          ty := sliceTy
          lvalue := false
          dataLocation? := some Solidity.DataLocation.calldata
          arraySlice := true }
  | expr@(Solidity.Expr.call
      (Solidity.Expr.typeName targetTy) args) => do
      checkTy env.types targetTy
      let checkTypeConversion : Except TypeError CheckedExpr := do
        env.types.requireNoFixedPointValue targetTy "conversion to"
        let checkedArgs ← checkArgs env args
        let argInfos := checkedArgInfos args checkedArgs
        requireNoNamedArgs "type conversion" argInfos
        require (checkedArgs.length == 1)
          (TypeError.arityMismatch "type conversion" 1 checkedArgs.length)
        match checkedArgs with
        | [arg] =>
            env.types.requireNoFixedPointValue arg.ty "conversion from"
            require
              (Ty.canExplicitlyConvert env.types arg.source arg.ty targetTy)
              (TypeError.invalidConversion arg.ty targetTy)
        | _ => Except.ok ()
        Except.ok
          { source := expr
            ty := env.qualifyCurrentLocalUserTypes targetTy
            lvalue := false }
      match targetTy with
      | Solidity.Ty.user path =>
          match env.types.lookupStruct? path with
          | some structDecl => do
              match checkArgs env args with
              | Except.ok checkedArgs =>
                  match
                      checkStructConstructorArgs env.types structDecl args
                        checkedArgs with
                  | Except.ok _ => Except.ok ()
                  | Except.error checkedErr =>
                      match
                          (do
                            let contextualCheckedArgs ←
                              if Args.anyNamed args then
                                checkNamedArgsAssignableToParamsFor
                                  env ("struct constructor " ++
                                    structDecl.name)
                                  (StructDecl.fieldNames structDecl)
                                  (StructDecl.fieldTys structDecl) args
                              else
                                checkPositionalArgsAssignableToParamsFor
                                  env ("struct constructor " ++
                                    structDecl.name)
                                  args (StructDecl.fieldTys structDecl)
                            checkStructConstructorArgs env.types structDecl
                              args contextualCheckedArgs) with
                      | Except.ok _ => Except.ok ()
                      | Except.error _ => Except.error checkedErr
              | Except.error argErr =>
                  match
                      (do
                        let contextualCheckedArgs ←
                          if Args.anyNamed args then
                            checkNamedArgsAssignableToParamsFor
                              env ("struct constructor " ++ structDecl.name)
                              (StructDecl.fieldNames structDecl)
                              (StructDecl.fieldTys structDecl) args
                          else
                            checkPositionalArgsAssignableToParamsFor
                              env ("struct constructor " ++ structDecl.name)
                              args (StructDecl.fieldTys structDecl)
                        checkStructConstructorArgs env.types structDecl args
                          contextualCheckedArgs) with
                  | Except.ok _ => Except.ok ()
                  | Except.error _ => Except.error argErr
              Except.ok
                { source := expr
                  ty := env.qualifyCurrentLocalUserTypes targetTy
                  lvalue := false }
          | none => checkTypeConversion
      | _ => checkTypeConversion
  | expr@(Solidity.Expr.call
      (Solidity.Expr.ident name) args) => do
      match checkArgs env args with
      | Except.ok checkedArgs =>
          let argInfos := checkedArgInfos args checkedArgs
          let checkedInfos := checkedArgInfosFull args checkedArgs
          match env.lookupVar? name with
          | some (Solidity.Ty.functionWithLocations params
              paramLocations returns returnLocations mutability visibility) => do
              let sig :=
                functionPointerSig name params paramLocations returns
                  returnLocations mutability visibility
              require (!ArgInfos.anyNamed argInfos)
                (TypeError.unsupported
                  "named arguments for function-typed expression")
              let checkedArgs ←
                match
                    checkCheckedArgsAssignableWidenFor env.types
                      "function call" checkedArgs params with
                | Except.ok _ => Except.ok checkedArgs
                | Except.error checkedErr =>
                    match
                        checkPositionalArgsAssignableToParamsFor
                          env "function call" args params with
                    | Except.ok contextualCheckedArgs =>
                        Except.ok contextualCheckedArgs
                    | Except.error _ => Except.error checkedErr
              checkCheckedExprsReferenceLocationsFor "function call"
                checkedArgs sig.paramStorageRefs sig.paramDataLocations
              requireCallMutabilityAllowed env mutability
              Except.ok (sig.checkedResult expr)
          | _ =>
              match FunctionSigs.resolveChecked env.types env.functions name
                  checkedInfos with
              | Except.ok sig => do
                  require sig.internallyCallable
                    (TypeError.invalidFunctionHeader
                      "external function requires external call syntax")
                  requireCallMutabilityAllowed env sig.mutability
                  Except.ok
                    (sig.checkedResult expr)
              | Except.error _ =>
                  match
                      FunctionSigs.resolveContextual
                        env env.functions name args with
                  | Except.ok sig => do
                      let contextualCheckedArgs ←
                        if Args.anyNamed args then
                          checkNamedArgsAssignableToParamsFor
                            env "function call" sig.paramNames
                              sig.params args
                        else
                          checkPositionalArgsAssignableToParamsFor
                            env "function call" args sig.params
                      match CheckedArgInfos.ordered? sig.paramNames
                          (checkedArgInfosFull args
                            contextualCheckedArgs) with
                      | some ordered =>
                          checkCheckedExprsReferenceLocationsFor
                            "function call" ordered sig.paramStorageRefs
                            sig.paramDataLocations
                      | none =>
                          Except.error
                            (TypeError.arityMismatch
                              "function call" sig.params.length args.length)
                      require sig.internallyCallable
                        (TypeError.invalidFunctionHeader
                          "external function requires external call syntax")
                      requireCallMutabilityAllowed env sig.mutability
                      Except.ok
                        (sig.checkedResult expr)
                  | Except.error _ =>
                      match checkBuiltinIdentCall env name argInfos
                          checkedArgs with
                      | Except.ok (some ty) =>
                          Except.ok
                            { source := expr, ty := ty, lvalue := false }
                      | Except.ok none =>
                          match Solidity.Executable.Expr.abiTyWithEnv?
                              env.vars expr with
                          | some ty => do
                              requireBuiltinIdentCallAllowed env name
                              Except.ok
                                { source := expr, ty := ty, lvalue := false }
                          | none =>
                              Except.error (TypeError.unknownFunction name)
                      | Except.error err => Except.error err
      | Except.error argErr =>
          if Args.anyNamed args then
            Except.error argErr
          else
            match env.lookupVar? name with
            | some (Solidity.Ty.functionWithLocations params
                paramLocations returns returnLocations mutability visibility) =>
                let sig :=
                  functionPointerSig name params paramLocations returns
                    returnLocations mutability visibility
                match
                    checkPositionalArgsAssignableToParamsFor
                      env "function call" args params with
                | Except.ok contextualCheckedArgs => do
                    checkCheckedExprsReferenceLocationsFor "function call"
                      contextualCheckedArgs sig.paramStorageRefs
                        sig.paramDataLocations
                    requireCallMutabilityAllowed env mutability
                    Except.ok (sig.checkedResult expr)
                | Except.error _ => Except.error argErr
            | _ =>
                match
                    FunctionSigs.resolveContextual
                      env env.functions name args with
                | Except.ok sig => do
                    let contextualCheckedArgs ←
                      if Args.anyNamed args then
                        checkNamedArgsAssignableToParamsFor
                          env "function call" sig.paramNames sig.params args
                      else
                        checkPositionalArgsAssignableToParamsFor
                          env "function call" args sig.params
                    match CheckedArgInfos.ordered? sig.paramNames
                        (checkedArgInfosFull args contextualCheckedArgs) with
                    | some ordered =>
                        checkCheckedExprsReferenceLocationsFor
                          "function call" ordered sig.paramStorageRefs
                          sig.paramDataLocations
                    | none =>
                        Except.error
                          (TypeError.arityMismatch
                            "function call" sig.params.length args.length)
                    require sig.internallyCallable
                      (TypeError.invalidFunctionHeader
                        "external function requires external call syntax")
                    requireCallMutabilityAllowed env sig.mutability
                    Except.ok
                      (sig.checkedResult expr)
                | Except.error _ => Except.error argErr
  | expr@(Solidity.Expr.call
      (Solidity.Expr.member
        (Solidity.Expr.ident "abi") "encodeCall") args) => do
      match args with
      | [ Solidity.Arg.positional functionPointer
        , Solidity.Arg.positional argumentExpr ] => do
          let tupleArgs ←
            match argumentExpr with
            | Solidity.Expr.tuple items =>
                tupleItemsAsPositionalArgs items
            | scalar =>
                Except.ok [Solidity.Arg.positional scalar]
          let sig ←
            match functionPointer with
            | Solidity.Expr.member
                (Solidity.Expr.typeName
                  (Solidity.Ty.user path)) member => do
                require (env.types.isContractValuePath path)
                  (TypeError.invalidAbiCall
                    "abi.encodeCall cannot use a library function")
                -- EC1: an `abi.encodeCall` function pointer references a UNIQUE
                -- function; solc resolves it by name (not by argument type) and
                -- separately checks each argument implicitly convertible to its
                -- parameter (below). Resolve by name+arity here so an argument
                -- that is only implicitly convertible to its parameter (a
                -- narrower integer, a literal) is not spuriously rejected. The
                -- contextual (type-exact) resolver over-rejected those.
                let sig ←
                  env.types.resolveEncodeCallPointerSig
                    path member tupleArgs.length
                require sig.externallyCallable
                  (TypeError.invalidAbiCall
                    "abi.encodeCall expects an external function")
                Except.ok sig
            | Solidity.Expr.member target member => do
                let targetChecked ← checkExpr env target
                match targetChecked.ty with
                | Solidity.Ty.user path => do
                    require (env.types.isContractValuePath path)
                      (TypeError.invalidAbiCall
                        "abi.encodeCall expects a contract function value")
                    -- EC1: resolve by name+arity (see the typeName branch).
                    let sig ←
                      env.types.resolveEncodeCallPointerSig
                        path member tupleArgs.length
                    require sig.externallyCallable
                      (TypeError.invalidAbiCall
                        "abi.encodeCall expects an external function")
                    Except.ok sig
                | other =>
                    Except.error
                      (TypeError.expectedType
                        (Solidity.Ty.address false) other)
            | Solidity.Expr.ident name => do
                let checked ← checkExpr env functionPointer
                match functionPointerSig? name checked.ty with
                | some sig => requireExternalEncodeCallPointer sig
                | none =>
                    Except.error
                      (TypeError.invalidAbiCall
                        "abi.encodeCall expects a function pointer")
            | _ => do
                let checked ← checkExpr env functionPointer
                match functionPointerSig? "" checked.ty with
                | some sig => requireExternalEncodeCallPointer sig
                | none =>
                    Except.error
                      (TypeError.invalidAbiCall
                        "abi.encodeCall expects a function pointer")
          match argumentExpr with
          | Solidity.Expr.tuple items =>
              let _ ←
                checkEncodeCallTupleItemsAssignableTo env items sig.params
              Except.ok ()
          | scalar =>
              match sig.params with
              | [ty] =>
                  let _ ←
                    checkArgAssignableToParam env ty
                      (Solidity.Arg.positional scalar)
                  Except.ok ()
              | expected =>
                  Except.error
                    (TypeError.arityMismatch
                      "abi.encodeCall" expected.length 1)
          Except.ok
            { source := expr
              ty := Solidity.Ty.bytes
              lvalue := false }
      | _ =>
          Except.error
            (TypeError.invalidAbiCall
              "abi.encodeCall expects a function pointer and arguments")
  | expr@(Solidity.Expr.call
      (Solidity.Expr.member
        (Solidity.Expr.typeName targetTy) member) args) => do
      checkTy env.types targetTy
      let targetTy := env.qualifyCurrentLocalUserTypes targetTy
      match targetTy with
      | Solidity.Ty.user path =>
          match env.types.lookupUserValueType? path with
          | some underlying =>
              let checkedArgs ← checkArgs env args
              let argInfos := checkedArgInfos args checkedArgs
              requireNoNamedArgs ("user-value-type " ++ member) argInfos
              if member == "wrap" then
                match checkedArgs with
                | [arg] => do
                    arg.expectAssignableToIn env.types underlying
                    Except.ok
                      { source := expr
                        ty := targetTy
                        lvalue := false }
                | _ =>
                    Except.error
                      (TypeError.arityMismatch
                        "user value type wrap" 1 checkedArgs.length)
              else if member == "unwrap" then
                match checkedArgs with
                | [arg] => do
                    arg.expectAssignableToIn env.types targetTy
                    Except.ok
                      { source := expr
                        ty := underlying
                        lvalue := false }
                | _ =>
                    Except.error
                      (TypeError.arityMismatch
                        "user value type unwrap" 1 checkedArgs.length)
              else
                Except.error (TypeError.unsupported ("member call " ++ member))
          | none =>
              match env.types.lookupContractDecl? path with
              | some libraryDecl =>
                  if libraryDecl.kind ==
                      Solidity.ContractKind.library then
                    let checkedArgs ← checkArgs env args
                    let sig ←
                      match
                          FunctionSigs.resolveChecked env.types
                            (FunctionSigs.nonPrivate
                              (FunctionSigs.atLibraryCallBoundary env.types
                                (ContractDecl.directFunctionSigsQualifiedLocalTypes
                                  libraryDecl)))
                            member (checkedArgInfosFull args checkedArgs) with
                      | Except.ok sig => Except.ok sig
                      | Except.error checkedErr =>
                          match
                              FunctionSigs.resolveContextual env
                                (FunctionSigs.nonPrivate
                                    (FunctionSigs.atLibraryCallBoundary env.types
                                      (ContractDecl.directFunctionSigsQualifiedLocalTypes
                                        libraryDecl)))
                                member args with
                          | Except.ok sig => do
                              let checkedArgs ←
                                if Args.anyNamed args then
                                  checkNamedArgsAssignableToParamsFor
                                    env "member call" sig.paramNames
                                    sig.params args
                                else
                                  checkPositionalArgsAssignableToParamsFor
                                    env "member call" args sig.params
                              match CheckedArgInfos.ordered? sig.paramNames
                                  (checkedArgInfosFull args checkedArgs) with
                              | some ordered =>
                                  checkCheckedExprsReferenceLocationsFor
                                    "member call" ordered sig.paramStorageRefs
                                    sig.paramDataLocations
                              | none =>
                                  Except.error
                                    (TypeError.arityMismatch "member call"
                                      sig.params.length checkedArgs.length)
                              Except.ok sig
                          | Except.error _ => Except.error checkedErr
                    requireCallMutabilityAllowed env sig.mutability
                    Except.ok (sig.checkedResult expr)
                  else if TypeContext.pathIn path env.ancestorPaths then
                    -- Explicit base-qualified call `Base.f()`: the solc importer
                    -- renders the base contract as `Expr.typeName (Ty.user path)`
                    -- rather than `Expr.ident`.  When the path names a base
                    -- contract in the current linearization, dispatch statically
                    -- to that base's implementation (bypassing any override),
                    -- mirroring the `Expr.ident baseName` branch below.
                    match path.segments with
                    | [baseName] =>
                        let checkedArgs ← checkArgs env args
                        let checkedInfos := checkedArgInfosFull args checkedArgs
                        let sig ←
                          match
                              env.resolveExplicitBaseMemberFunctionChecked
                                baseName member checkedInfos with
                          | Except.ok sig => Except.ok sig
                          | Except.error checkedErr =>
                              match
                                  checkExplicitBaseMemberCallArgsContextual
                                    env baseName member args with
                              | Except.ok (sig, _) => Except.ok sig
                              | Except.error _ => Except.error checkedErr
                        requireCallMutabilityAllowed env sig.mutability
                        Except.ok (sig.checkedResult expr)
                    | _ =>
                        Except.error
                          (TypeError.unsupported ("member call " ++ member))
                  else
                    Except.error
                      (TypeError.unsupported ("member call " ++ member))
              | none =>
                  Except.error (TypeError.unsupported ("member call " ++ member))
      | Solidity.Ty.bytes =>
          require (member == "concat")
            (TypeError.unsupported ("member call " ++ member))
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs "bytes.concat" argInfos
          checkBytesConcatArgs checkedArgs
          Except.ok
            { source := expr
              ty := Solidity.Ty.bytes
              lvalue := false }
      | Solidity.Ty.string =>
          require (member == "concat")
            (TypeError.unsupported ("member call " ++ member))
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs "string.concat" argInfos
          checkStringConcatArgs checkedArgs
          Except.ok
            { source := expr
              ty := Solidity.Ty.string
              lvalue := false }
      | _ =>
          Except.error (TypeError.unsupported ("member call " ++ member))
  | expr@(Solidity.Expr.call
      (Solidity.Expr.member
        (Solidity.Expr.member
          (Solidity.Expr.typeName
            (Solidity.Ty.user parentPath)) typeName) member)
      args) => do
      let targetPath : Path :=
        { segments := parentPath.segments ++ [typeName] }
      let targetTy := Solidity.Ty.user targetPath
      checkTy env.types targetTy
      match env.types.lookupUserValueType? targetPath with
      | some underlying =>
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs ("user-value-type " ++ member) argInfos
          if member == "wrap" then
            match checkedArgs with
            | [arg] => do
                arg.expectAssignableToIn env.types underlying
                Except.ok
                  { source := expr
                    ty := targetTy
                    lvalue := false }
            | _ =>
                Except.error
                  (TypeError.arityMismatch
                    "user value type wrap" 1 checkedArgs.length)
          else if member == "unwrap" then
            match checkedArgs with
            | [arg] => do
                arg.expectAssignableToIn env.types targetTy
                Except.ok
                  { source := expr
                    ty := underlying
                    lvalue := false }
            | _ =>
                Except.error
                  (TypeError.arityMismatch
                    "user value type unwrap" 1 checkedArgs.length)
          else
            Except.error (TypeError.unsupported ("member call " ++ member))
      | none =>
          Except.error (TypeError.unsupported ("member call " ++ member))
  | Solidity.Expr.call
      (Solidity.Expr.member target member) args => do
      let expr :=
        Solidity.Expr.call
          (Solidity.Expr.member target member) args
      let checkedArgs ←
        match checkArgs env args with
        | Except.ok checkedArgs => Except.ok checkedArgs
        | Except.error argErr =>
            match checkMemberCallArgsContextual env target member args with
            | Except.ok checkedArgs => Except.ok checkedArgs
            | Except.error _ => Except.error argErr
      let argInfos := checkedArgInfos args checkedArgs
      let checkedInfos := checkedArgInfosFull args checkedArgs
      let checkLowLevelCallWithTarget
          (targetChecked : CheckedExpr) : Except TypeError CheckedExpr := do
        require (!ArgInfos.anyNamed argInfos)
          (TypeError.unsupported "named arguments for low-level call")
        require (targetChecked.ty.isAddressLike env.types)
          (TypeError.expectedType
            (Solidity.Ty.address false) targetChecked.ty)
        if member == "staticcall" then
          requireCallMutabilityAllowed env
            Solidity.StateMutability.view
        else
          requireCallMutabilityAllowed env
            Solidity.StateMutability.nonpayable
        if member == "call" || member == "staticcall" ||
            member == "delegatecall" then
          match checkedArgs with
          | [data] => do
              data.expectAssignableTo Solidity.Ty.bytes
              Except.ok { source := expr, ty := lowLevelCallReturnTy }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  ("low-level " ++ member) 1 checkedArgs.length)
        else if member == "send" then
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (Solidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok
                { source := expr, ty := Solidity.Ty.bool }
          | _ =>
              Except.error
                (TypeError.arityMismatch "send" 1 checkedArgs.length)
        else
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (Solidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok
                { source := expr
                  ty := Solidity.Ty.tuple [] }
          | _ =>
              Except.error
                (TypeError.arityMismatch "transfer" 1 checkedArgs.length)
      match target with
        | Solidity.Expr.ident "abi" =>
            requireNoNamedArgs ("abi." ++ member) argInfos
            if member == "encode" then
              checkAbiEncodableArgs env.types checkedArgs
              Except.ok
                { source := expr
                  ty := Solidity.Ty.bytes
                  lvalue := false }
            else if member == "encodePacked" then
              checkAbiEncodePackedArgs env.types checkedArgs
              Except.ok
                { source := expr
                  ty := Solidity.Ty.bytes
                  lvalue := false }
            else if member == "decode" then
              match args, checkedArgs with
              | [ Solidity.Arg.positional _,
                  Solidity.Arg.positional typesExpr ],
                [data, _] => do
                  data.expectBytesLike
                  let tys ← checkAbiDecodeTypesExpr env.types typesExpr
                  require (tys.length > 0)
                    (TypeError.invalidAbiCall
                      "abi.decode expects at least one target type")
                  Except.ok
                    { source := expr
                      ty := resultTyFromReturns tys
                      lvalue := false }
              | _, _ =>
                  Except.error
                    (TypeError.arityMismatch
                      "abi.decode" 2 checkedArgs.length)
            else if member == "encodeWithSelector" then
              match checkedArgs with
              | selector :: rest => do
                  selector.expectAssignableTo (Solidity.Ty.bytesN 4)
                  checkAbiEncodableArgs env.types rest
                  Except.ok
                    { source := expr
                      ty := Solidity.Ty.bytes
                      lvalue := false }
              | [] =>
                  Except.error
                    (TypeError.arityMismatch
                      "abi.encodeWithSelector" 1 0)
            else if member == "encodeWithSignature" then
              match checkedArgs with
              | signature :: rest => do
                  signature.expectStringLike
                  checkAbiEncodableArgs env.types rest
                  Except.ok
                    { source := expr
                      ty := Solidity.Ty.bytes
                      lvalue := false }
              | [] =>
                  Except.error
                    (TypeError.arityMismatch
                      "abi.encodeWithSignature" 1 0)
            else
              Except.error (TypeError.unsupported ("member " ++ member))
        | Solidity.Expr.ident "bytes" =>
            require (member == "concat")
              (TypeError.unsupported ("member " ++ member))
            requireNoNamedArgs "bytes.concat" argInfos
            checkBytesConcatArgs checkedArgs
            Except.ok
              { source := expr
                ty := Solidity.Ty.bytes
                lvalue := false }
        | Solidity.Expr.ident "string" =>
            require (member == "concat")
              (TypeError.unsupported ("member " ++ member))
            requireNoNamedArgs "string.concat" argInfos
            checkStringConcatArgs checkedArgs
            Except.ok
              { source := expr
                ty := Solidity.Ty.string
                lvalue := false }
        | Solidity.Expr.ident "super" => do
            let sig ←
              match
                  FunctionSigs.resolveChecked env.types env.superFunctions
                    member checkedInfos with
              | Except.ok sig => Except.ok sig
              | Except.error checkedErr =>
                  match
                      checkSuperMemberCallArgsContextual env member args with
                  | Except.ok (sig, _) => Except.ok sig
                  | Except.error _ => Except.error checkedErr
            requireCallMutabilityAllowed env sig.mutability
            Except.ok
              (sig.checkedResult expr)
        | targetExpr => do
            let checkUsingOrFallback : Except TypeError CheckedExpr := do
              let targetChecked ← checkExpr env targetExpr
              require (!targetChecked.arraySlice)
                (TypeError.unsupported "member call on array slice")
              if lowLevelCallMember member &&
                  targetChecked.ty.isAddressBuiltinReceiver then
                checkLowLevelCallWithTarget targetChecked
              else
                let mutation? ←
                  checkArrayMutationCall? env expr targetExpr member
                    argInfos checkedArgs targetChecked
                match mutation? with
                | some checked => Except.ok checked
                | none =>
                    let checkUsingCall : Except TypeError CheckedExpr := do
                      let sig ←
                        match
                            env.resolveUsingMemberFunctionChecked targetChecked
                              member checkedInfos with
                        | Except.ok sig => Except.ok sig
                        | Except.error checkedErr =>
                            match
                                checkMemberCallArgsContextual env targetExpr
                                  member args with
                            | Except.ok contextualCheckedArgs =>
                                env.resolveUsingMemberFunctionChecked
                                  targetChecked member
                                    (checkedArgInfosFull args
                                      contextualCheckedArgs)
                            | Except.error _ => Except.error checkedErr
                      requireCallMutabilityAllowed env sig.mutability
                      Except.ok
                        (sig.checkedResult expr)
                    match targetChecked.ty with
                    | Solidity.Ty.user path =>
                        if env.types.isContractValuePath path then
                          match env.types.resolveContractMemberFunctionChecked path
                              member checkedInfos with
                          | Except.ok sig => do
                              requireCallMutabilityAllowed env sig.mutability
                              Except.ok
                                (sig.checkedResult expr)
                          | Except.error _ =>
                              match
                                  checkContractMemberCallArgsContextualForPath
                                    env path member args with
                              | Except.ok (sig, _) => do
                                  requireCallMutabilityAllowed env sig.mutability
                                  Except.ok
                                    (sig.checkedResult expr)
                              | Except.error _ => checkUsingCall
                        else
                          checkUsingCall
                    | _ =>
                        match Solidity.Executable.Expr.abiTyWithEnv?
                            env.vars expr with
                        | some ty =>
                            Except.ok
                              { source := expr, ty := ty, lvalue := false }
                        | none => checkUsingCall
            match targetExpr with
            | Solidity.Expr.typeName
                (Solidity.Ty.user libraryPath) =>
                match env.types.lookupContractDecl? libraryPath with
                | some libraryDecl =>
                    if libraryDecl.kind ==
                        Solidity.ContractKind.library then
                      let sig ←
                        match
                            FunctionSigs.resolveChecked env.types
                              (FunctionSigs.nonPrivate
                                (FunctionSigs.atLibraryCallBoundary env.types
                                  (ContractDecl.directFunctionSigsQualifiedLocalTypes
                                    libraryDecl)))
                              member checkedInfos with
                        | Except.ok sig => Except.ok sig
                        | Except.error checkedErr =>
                            match
                                FunctionSigs.resolveContextual env
                                  (FunctionSigs.nonPrivate
                                    (FunctionSigs.atLibraryCallBoundary env.types
                                      (ContractDecl.directFunctionSigsQualifiedLocalTypes
                                        libraryDecl)))
                                  member args with
                            | Except.ok sig => do
                                let checkedArgs ←
                                  if Args.anyNamed args then
                                    checkNamedArgsAssignableToParamsFor
                                      env "member call" sig.paramNames
                                      sig.params args
                                  else
                                    checkPositionalArgsAssignableToParamsFor
                                      env "member call" args sig.params
                                match CheckedArgInfos.ordered? sig.paramNames
                                    (checkedArgInfosFull args checkedArgs) with
                                | some ordered =>
                                    checkCheckedExprsReferenceLocationsFor
                                      "member call" ordered
                                      sig.paramStorageRefs
                                      sig.paramDataLocations
                                | none =>
                                    Except.error
                                      (TypeError.arityMismatch "member call"
                                        sig.params.length checkedArgs.length)
                                Except.ok sig
                            | Except.error _ => Except.error checkedErr
                      requireCallMutabilityAllowed env sig.mutability
                      Except.ok (sig.checkedResult expr)
                    else
                      checkUsingOrFallback
                | none => checkUsingOrFallback
            | Solidity.Expr.ident libraryName =>
                if (env.lookupVar? libraryName).isNone &&
                    TypeContext.pathIn
                      (TypeContext.pathOfName libraryName)
                      env.ancestorPaths then
                  let sig ←
                    match
                        env.resolveExplicitBaseMemberFunctionChecked
                          libraryName member checkedInfos with
                    | Except.ok sig => Except.ok sig
                    | Except.error checkedErr =>
                        match
                            checkExplicitBaseMemberCallArgsContextual
                              env libraryName member args with
                        | Except.ok (sig, _) => Except.ok sig
                        | Except.error _ => Except.error checkedErr
                  requireCallMutabilityAllowed env sig.mutability
                  Except.ok
                    (sig.checkedResult expr)
                else
                  match env.lookupVar? libraryName,
                      env.types.lookupContractDecl?
                        (TypeContext.pathOfName libraryName) with
                  | none, some libraryDecl =>
                      if libraryDecl.kind ==
                          Solidity.ContractKind.library then
                        let sig ←
                          match
                              env.types.resolveLibraryFunctionChecked
                                libraryName member checkedInfos with
                          | Except.ok sig => Except.ok sig
                          | Except.error checkedErr =>
                              match
                                  checkLibraryMemberCallArgsContextual
                                    env libraryName member args with
                              | Except.ok (sig, _) => Except.ok sig
                              | Except.error _ => Except.error checkedErr
                        requireCallMutabilityAllowed env sig.mutability
                        Except.ok
                          (sig.checkedResult expr)
                      else
                        checkUsingOrFallback
                  | _, _ => checkUsingOrFallback
            | _ => checkUsingOrFallback
  | expr@(Solidity.Expr.call fn args) => do
      let fnChecked ← checkExpr env fn
      match fnChecked.ty with
      | Solidity.Ty.functionWithLocations params paramLocations
          returns returnLocations mutability visibility => do
          let sig :=
            functionPointerSig "<expression>" params paramLocations returns
              returnLocations mutability visibility
          let checkedArgs ←
            match checkArgs env args with
            | Except.ok checkedArgs =>
                let argInfos := checkedArgInfos args checkedArgs
                require (!ArgInfos.anyNamed argInfos)
                  (TypeError.unsupported
                    "named arguments for function-typed expression")
                match
                    checkCheckedArgsAssignableWidenFor env.types
                      "function call" checkedArgs params with
                | Except.ok _ => Except.ok checkedArgs
                | Except.error checkedErr =>
                    match
                        checkPositionalArgsAssignableToParamsFor
                          env "function call" args params with
                    | Except.ok contextualCheckedArgs =>
                        Except.ok contextualCheckedArgs
                    | Except.error _ => Except.error checkedErr
            | Except.error argErr =>
                if Args.anyNamed args then
                  Except.error argErr
                else
                  match
                      checkPositionalArgsAssignableToParamsFor
                        env "function call" args params with
                  | Except.ok contextualCheckedArgs =>
                      Except.ok contextualCheckedArgs
                  | Except.error _ => Except.error argErr
          checkCheckedExprsReferenceLocationsFor "function call" checkedArgs
            sig.paramStorageRefs sig.paramDataLocations
          requireCallMutabilityAllowed env mutability
          Except.ok (sig.checkedResult expr)
      | _ =>
          let checkedArgs ← checkArgs env args
          requireCallExprMutabilityAllowed env fn
          match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
          | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
          | none =>
              Except.error
                (TypeError.unsupported
                  ("call with " ++ toString checkedArgs.length ++ " arguments"))
  | expr@(Solidity.Expr.callWithOptions
      (Solidity.Expr.newExpr ty []) options args) => do
      checkTy env.types ty
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      requireCallOptionsAllowedNames ["value", "salt"] options
      if CallOptions.hasSalt options then
        requireConstantinopleOrLater env "contract creation salt"
      else
        Except.ok ()
      match ty with
      | Solidity.Ty.user path =>
          let contractDecl ←
            match env.types.lookupContractDecl? path with
            | some decl => Except.ok decl
            | none => Except.error (TypeError.invalidType ty)
          requireCreatableContractDecl contractDecl
          requireLogOrCreateAllowed env
            "contract creation in view or pure function"
          let constructorSig := ContractDecl.constructorSignature contractDecl
          match checkArgs env args with
          | Except.ok checkedArgs =>
              match
                  checkCheckedArgsAssignableToFunctionSig env.types
                    ("constructor " ++ contractDecl.name) constructorSig
                    args checkedArgs with
              | Except.ok _ => Except.ok ()
              | Except.error checkedErr =>
                  match
                      (do
                        let contextualCheckedArgs ←
                          if Args.anyNamed args then
                            checkNamedArgsAssignableToParamsFor
                              env ("constructor " ++ contractDecl.name)
                              constructorSig.paramNames constructorSig.params
                              args
                          else
                            checkPositionalArgsAssignableToParamsFor
                              env ("constructor " ++ contractDecl.name) args
                              constructorSig.params
                        match CheckedArgInfos.ordered?
                            constructorSig.paramNames
                            (checkedArgInfosFull args
                              contextualCheckedArgs) with
                        | some ordered =>
                            checkCheckedExprsReferenceLocationsFor
                              ("constructor " ++ contractDecl.name)
                              ordered constructorSig.paramStorageRefs
                              constructorSig.paramDataLocations
                        | none =>
                            Except.error
                              (TypeError.arityMismatch
                                ("constructor " ++ contractDecl.name)
                                constructorSig.params.length
                                contextualCheckedArgs.length)) with
                  | Except.ok _ => Except.ok ()
                  | Except.error _ => Except.error checkedErr
          | Except.error argErr =>
              match
                  (do
                    let contextualCheckedArgs ←
                      if Args.anyNamed args then
                        checkNamedArgsAssignableToParamsFor
                          env ("constructor " ++ contractDecl.name)
                          constructorSig.paramNames constructorSig.params args
                      else
                        checkPositionalArgsAssignableToParamsFor
                          env ("constructor " ++ contractDecl.name) args
                          constructorSig.params
                    match CheckedArgInfos.ordered?
                        constructorSig.paramNames
                        (checkedArgInfosFull args contextualCheckedArgs) with
                    | some ordered =>
                        checkCheckedExprsReferenceLocationsFor
                          ("constructor " ++ contractDecl.name) ordered
                          constructorSig.paramStorageRefs
                          constructorSig.paramDataLocations
                    | none =>
                        Except.error
                          (TypeError.arityMismatch
                            ("constructor " ++ contractDecl.name)
                            constructorSig.params.length
                            contextualCheckedArgs.length)) with
              | Except.ok _ => Except.ok ()
              | Except.error _ => Except.error argErr
          requireValueOptionAllowed constructorSig.mutability options
          Except.ok { source := expr, ty := ty, lvalue := false }
      | _ => Except.error (TypeError.invalidType ty)
  | expr@(Solidity.Expr.callWithOptions
      (Solidity.Expr.ident name) options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      match env.lookupVar? name with
      | some (Solidity.Ty.functionWithLocations params
          paramLocations returns returnLocations mutability visibility) => do
          let sig :=
            functionPointerSig name params paramLocations returns
              returnLocations mutability visibility
          let checkedArgs ←
            match checkArgs env args with
            | Except.ok checkedArgs =>
                let argInfos := checkedArgInfos args checkedArgs
                require (!ArgInfos.anyNamed argInfos)
                  (TypeError.unsupported
                    "named arguments for function-typed expression")
                match
                    checkCheckedArgsAssignableWidenFor env.types
                      "function call" checkedArgs params with
                | Except.ok _ => Except.ok checkedArgs
                | Except.error checkedErr =>
                    match
                        checkPositionalArgsAssignableToParamsFor
                          env "function call" args params with
                    | Except.ok contextualCheckedArgs =>
                        Except.ok contextualCheckedArgs
                    | Except.error _ => Except.error checkedErr
            | Except.error argErr =>
                if Args.anyNamed args then
                  Except.error argErr
                else
                  match
                      checkPositionalArgsAssignableToParamsFor
                        env "function call" args params with
                  | Except.ok contextualCheckedArgs =>
                      Except.ok contextualCheckedArgs
                  | Except.error _ => Except.error argErr
          checkCheckedExprsReferenceLocationsFor "function call" checkedArgs
            sig.paramStorageRefs sig.paramDataLocations
          if options.isEmpty then
            Except.ok ()
          else
            require (visibility == Solidity.Visibility.external_)
              (TypeError.unsupported
                "call options on internal function value")
          requireCallOptionsAllowedNames ["gas", "value"] options
          requireCallMutabilityAllowed env mutability
          requireValueOptionAllowed mutability options
          Except.ok (sig.checkedResult expr)
      | _ => do
          let checkedArgs ← checkArgs env args
          let checkedInfos := checkedArgInfosFull args checkedArgs
          let sig ← FunctionSigs.resolveChecked env.types env.functions name
            checkedInfos
          require options.isEmpty
            (TypeError.unsupported
              "call options on internal identifier call")
          require sig.internallyCallable
            (TypeError.invalidFunctionHeader
              "external function requires external call syntax")
          requireCallMutabilityAllowed env sig.mutability
          Except.ok
            (sig.checkedResult expr)
  | expr@(Solidity.Expr.callWithOptions
      (Solidity.Expr.member
        (Solidity.Expr.ident "super") member) options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      require options.isEmpty
        (TypeError.unsupported "call options on super call")
      let checkedArgs ←
        match checkArgs env args with
        | Except.ok checkedArgs => Except.ok checkedArgs
        | Except.error argErr =>
            match checkSuperMemberCallArgsContextual env member args with
            | Except.ok (_, checkedArgs) => Except.ok checkedArgs
            | Except.error _ => Except.error argErr
      let checkedInfos := checkedArgInfosFull args checkedArgs
      let sig ←
        match
            FunctionSigs.resolveChecked env.types env.superFunctions member
              checkedInfos with
        | Except.ok sig => Except.ok sig
        | Except.error checkedErr =>
            match checkSuperMemberCallArgsContextual env member args with
            | Except.ok (sig, _) => Except.ok sig
            | Except.error _ => Except.error checkedErr
      requireCallMutabilityAllowed env sig.mutability
      Except.ok
        (sig.checkedResult expr)
  | Solidity.Expr.callWithOptions
      (Solidity.Expr.member target member) options args => do
      let expr :=
        Solidity.Expr.callWithOptions
          (Solidity.Expr.member target member) options args
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      let checkedInfos := checkedArgInfosFull args checkedArgs
      let targetChecked ← checkExpr env target
      if lowLevelCallMember member &&
          targetChecked.ty.isAddressBuiltinReceiver then
        require (!ArgInfos.anyNamed argInfos)
          (TypeError.unsupported "named arguments for low-level call")
        require (targetChecked.ty.isAddressLike env.types)
          (TypeError.expectedType
            (Solidity.Ty.address false) targetChecked.ty)
        if member == "call" then
          requireCallOptionsAllowedNames ["gas", "value"] options
        else if member == "staticcall" || member == "delegatecall" then
          requireCallOptionsAllowedNames ["gas"] options
        else
          requireCallOptionsAllowedNames [] options
        if member == "staticcall" then
          requireCallMutabilityAllowed env
            Solidity.StateMutability.view
        else
          requireCallMutabilityAllowed env
            Solidity.StateMutability.nonpayable
        if member == "call" || member == "staticcall" ||
            member == "delegatecall" then
          match checkedArgs with
          | [data] => do
              data.expectAssignableTo Solidity.Ty.bytes
              Except.ok { source := expr, ty := lowLevelCallReturnTy }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  ("low-level " ++ member) 1 checkedArgs.length)
        else if member == "send" then
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (Solidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok
                { source := expr, ty := Solidity.Ty.bool }
          | _ =>
              Except.error
                (TypeError.arityMismatch "send" 1 checkedArgs.length)
        else
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (Solidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok
                { source := expr
                  ty := Solidity.Ty.tuple [] }
          | _ =>
              Except.error
                (TypeError.arityMismatch "transfer" 1 checkedArgs.length)
      else
        require (!targetChecked.arraySlice)
          (TypeError.unsupported "member call on array slice")
        let mutation? ←
          checkArrayMutationCall? env expr target member argInfos
            checkedArgs targetChecked
        match mutation? with
        | some checked => do
            require options.isEmpty
              (TypeError.unsupported "call options on array member")
            Except.ok checked
        | none =>
            requireCallOptionsAllowedNames ["gas", "value"] options
            match targetChecked.ty with
            | Solidity.Ty.user path => do
                require (env.types.isContractValuePath path)
                  (TypeError.unsupported
                    "member call on a transient library value")
                let sig ←
                  match env.types.resolveContractMemberFunctionChecked path
                      member checkedInfos with
                  | Except.ok sig => Except.ok sig
                  | Except.error checkedErr =>
                      match
                          checkContractMemberCallArgsContextualForPath
                            env path member args with
                      | Except.ok (sig, _) => Except.ok sig
                      | Except.error _ => Except.error checkedErr
                requireCallMutabilityAllowed env sig.mutability
                requireValueOptionAllowed sig.mutability options
                Except.ok
                  (sig.checkedResult expr)
            | _ =>
                match Solidity.Executable.Expr.abiTyWithEnv?
                    env.vars expr with
                | some ty =>
                    Except.ok { source := expr, ty := ty, lvalue := false }
                | none =>
                    Except.error
                      (TypeError.unsupported ("member call " ++ member))
  | expr@(Solidity.Expr.callWithOptions fn options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      let fnChecked ← checkExpr env fn
      match fnChecked.ty with
      | Solidity.Ty.functionWithLocations params paramLocations
          returns returnLocations mutability visibility => do
          let sig :=
            functionPointerSig "<expression>" params paramLocations returns
              returnLocations mutability visibility
          let checkedArgs ←
            match checkArgs env args with
            | Except.ok checkedArgs =>
                let argInfos := checkedArgInfos args checkedArgs
                require (!ArgInfos.anyNamed argInfos)
                  (TypeError.unsupported
                    "named arguments for function-typed expression")
                match
                    checkCheckedArgsAssignableWidenFor env.types
                      "function call" checkedArgs params with
                | Except.ok _ => Except.ok checkedArgs
                | Except.error checkedErr =>
                    match
                        checkPositionalArgsAssignableToParamsFor
                          env "function call" args params with
                    | Except.ok contextualCheckedArgs =>
                        Except.ok contextualCheckedArgs
                    | Except.error _ => Except.error checkedErr
            | Except.error argErr =>
                if Args.anyNamed args then
                  Except.error argErr
                else
                  match
                      checkPositionalArgsAssignableToParamsFor
                        env "function call" args params with
                  | Except.ok contextualCheckedArgs =>
                      Except.ok contextualCheckedArgs
                  | Except.error _ => Except.error argErr
          checkCheckedExprsReferenceLocationsFor "function call" checkedArgs
            sig.paramStorageRefs sig.paramDataLocations
          if options.isEmpty then
            Except.ok ()
          else
            require (visibility == Solidity.Visibility.external_)
              (TypeError.unsupported
                "call options on internal function value")
          requireCallOptionsAllowedNames ["gas", "value"] options
          requireCallMutabilityAllowed env mutability
          requireValueOptionAllowed mutability options
          Except.ok (sig.checkedResult expr)
      | _ =>
          let checkedArgs ← checkArgs env args
          requireCallExprMutabilityAllowed env fn
          match Solidity.Executable.Expr.abiTyWithEnv? env.vars expr with
          | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
          | none =>
              Except.error
                (TypeError.unsupported
                  ("call with " ++ toString checkedArgs.length ++ " arguments"))
  | expr@(Solidity.Expr.newExpr ty args) => do
      checkTy env.types ty
      match ty with
      | Solidity.Ty.bytes =>
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs "new bytes" argInfos
          match checkedArgs with
          | [length] => do
              length.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok { source := expr, ty := ty, lvalue := false }
          | _ =>
              Except.error
                (TypeError.arityMismatch "new bytes" 1 checkedArgs.length)
      | Solidity.Ty.string =>
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs "new string" argInfos
          match checkedArgs with
          | [length] => do
              length.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok { source := expr, ty := ty, lvalue := false }
          | _ =>
              Except.error
                (TypeError.arityMismatch "new string" 1 checkedArgs.length)
      | Solidity.Ty.array _ none =>
          let checkedArgs ← checkArgs env args
          let argInfos := checkedArgInfos args checkedArgs
          requireNoNamedArgs "new dynamic array" argInfos
          match checkedArgs with
          | [length] => do
              length.expectAssignableTo (Solidity.Ty.uint 256)
              Except.ok { source := expr, ty := ty, lvalue := false }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  "new dynamic array" 1 checkedArgs.length)
      | Solidity.Ty.user path =>
          let contractDecl ←
            match env.types.lookupContractDecl? path with
            | some decl => Except.ok decl
            | none => Except.error (TypeError.invalidType ty)
          requireCreatableContractDecl contractDecl
          requireLogOrCreateAllowed env
            "contract creation in view or pure function"
          let constructorSig := ContractDecl.constructorSignature contractDecl
          match checkArgs env args with
          | Except.ok checkedArgs =>
              match
                  checkCheckedArgsAssignableToFunctionSig env.types
                    ("constructor " ++ contractDecl.name) constructorSig
                    args checkedArgs with
              | Except.ok _ => Except.ok ()
              | Except.error checkedErr =>
                  match
                      (do
                        let contextualCheckedArgs ←
                          if Args.anyNamed args then
                            checkNamedArgsAssignableToParamsFor
                              env ("constructor " ++ contractDecl.name)
                              constructorSig.paramNames constructorSig.params
                              args
                          else
                            checkPositionalArgsAssignableToParamsFor
                              env ("constructor " ++ contractDecl.name) args
                              constructorSig.params
                        match CheckedArgInfos.ordered?
                            constructorSig.paramNames
                            (checkedArgInfosFull args
                              contextualCheckedArgs) with
                        | some ordered =>
                            checkCheckedExprsReferenceLocationsFor
                              ("constructor " ++ contractDecl.name)
                              ordered constructorSig.paramStorageRefs
                              constructorSig.paramDataLocations
                        | none =>
                            Except.error
                              (TypeError.arityMismatch
                                ("constructor " ++ contractDecl.name)
                                constructorSig.params.length
                                contextualCheckedArgs.length)) with
                  | Except.ok _ => Except.ok ()
                  | Except.error _ => Except.error checkedErr
          | Except.error argErr =>
              match
                  (do
                    let contextualCheckedArgs ←
                      if Args.anyNamed args then
                        checkNamedArgsAssignableToParamsFor
                          env ("constructor " ++ contractDecl.name)
                          constructorSig.paramNames constructorSig.params args
                      else
                        checkPositionalArgsAssignableToParamsFor
                          env ("constructor " ++ contractDecl.name) args
                          constructorSig.params
                    match CheckedArgInfos.ordered?
                        constructorSig.paramNames
                        (checkedArgInfosFull args contextualCheckedArgs) with
                    | some ordered =>
                        checkCheckedExprsReferenceLocationsFor
                          ("constructor " ++ contractDecl.name) ordered
                          constructorSig.paramStorageRefs
                          constructorSig.paramDataLocations
                    | none =>
                        Except.error
                          (TypeError.arityMismatch
                            ("constructor " ++ contractDecl.name)
                            constructorSig.params.length
                            contextualCheckedArgs.length)) with
              | Except.ok _ => Except.ok ()
              | Except.error _ => Except.error argErr
          Except.ok { source := expr, ty := ty, lvalue := false }
      | _ => Except.error (TypeError.invalidType ty)
  | expr@(Solidity.Expr.tuple items) => do
      let tys ← checkTupleItems env items
      Except.ok
        { source := expr, ty := Solidity.Ty.tuple tys,
          lvalue := false }
  | Solidity.Expr.array [] =>
      Except.error (TypeError.unsupported "empty array literal")
  | expr@(Solidity.Expr.array (head :: rest)) => do
      let checkedElements ← checkExprList env (head :: rest)
      let elementTy ←
        match CheckedExprs.commonArrayElementTy? checkedElements with
        | some ty => Except.ok ty
        | none =>
            Except.error
              (TypeError.unsupported "array literal common type")
      -- G9: an inline array literal yields a memory array; a mapping element
      -- type is only valid in storage, so solc rejects `[m]` (TypeError, "Type
      -- mapping … is only valid in storage").
      require
        (match elementTy with
          | Solidity.Ty.mapping _ _ => false
          | _ => true)
        (TypeError.unsupported "inline array of mapping type")
      checkCheckedExprsAssignableToFor env.types "array literal" checkedElements
        (List.replicate checkedElements.length elementTy)
      Except.ok
        { source := expr
          ty := Solidity.Ty.array elementTy
            (some (head :: rest).length)
          lvalue := false }
  | expr@(Solidity.Expr.enumFromUInt _ inner) => do
      let checkedInner ← checkExpr env inner
      checkedInner.expectInteger
      Except.ok
        { source := expr
          ty := Solidity.Ty.uint 8
          lvalue := false }
  | expr@(Solidity.Expr.unary op inner) => do
      let checked ← checkExpr env inner
      let usingOperator? ←
        CheckEnv.resolveUsingUnaryOperator? env op checked
      match usingOperator? with
      | some sig =>
          match sig.returns with
          | [ty] => Except.ok { source := expr, ty := ty }
          | _ => Except.error (TypeError.unknownFunction "operator")
      | none =>
      match op with
      | Solidity.UnaryOp.logicalNot =>
          checked.expectBool
          Except.ok { source := expr, ty := Solidity.Ty.bool }
      | Solidity.UnaryOp.bitNot =>
          checked.expectShiftLeftOperand
          Except.ok { source := expr, ty := checked.ty }
      | Solidity.UnaryOp.neg =>
          match Solidity.Executable.Expr.toCoreNumericLiteralAs?
              (Solidity.Ty.int 256) expr with
          | some _ =>
              Except.ok
                { source := expr
                  ty := Solidity.Ty.int 256 }
          | none => do
              require checked.ty.isSignedArithmeticOperand
                (TypeError.expectedInteger checked.ty)
              Except.ok { source := expr, ty := checked.ty }
      | Solidity.UnaryOp.delete =>
          require checked.lvalue (TypeError.expectedLValue inner)
          checked.expectWritableLocation inner
          require (!checked.locationIsCalldata)
            (TypeError.invalidDataLocation checked.ty
              (some Solidity.DataLocation.calldata))
          match checked.ty with
          | Solidity.Ty.mapping _ _ =>
              Except.error
                (TypeError.unsupported "delete on mapping lvalue")
          | _ => Except.ok ()
          match Expr.directIdentName? inner with
          | some name =>
              require (!env.isLocalStorageRef name)
                (TypeError.invalidDataLocation checked.ty
                  (some Solidity.DataLocation.storage))
          | none => Except.ok ()
          if checked.stateLValue then
            requireStateWriteAllowed env
          else
            Except.ok ()
          Except.ok { source := expr, ty := checked.ty, lvalue := false }
      | Solidity.UnaryOp.preIncrement
      | Solidity.UnaryOp.preDecrement
      | Solidity.UnaryOp.postIncrement
      | Solidity.UnaryOp.postDecrement =>
          require checked.lvalue (TypeError.expectedLValue inner)
          checked.expectWritableLocation inner
          if checked.stateLValue then
            requireStateWriteAllowed env
          else
            Except.ok ()
          checked.expectInteger
          Except.ok { source := expr, ty := checked.ty, lvalue := false }
  | expr@(Solidity.Expr.binary op lhs rhs) => do
      let lhsChecked ← checkExpr env lhs
      let rhsChecked ← checkExpr env rhs
      let usingOperator? ←
        CheckEnv.resolveUsingBinaryOperator? env op lhsChecked rhsChecked
      match usingOperator? with
      | some sig =>
          match sig.returns with
          | [ty] => Except.ok { source := expr, ty := ty }
          | _ => Except.error (TypeError.unknownFunction "operator")
      | none =>
      match op with
      | Solidity.BinaryOp.boolAnd
      | Solidity.BinaryOp.boolOr =>
          lhsChecked.expectBool
          rhsChecked.expectBool
          Except.ok { source := expr, ty := Solidity.Ty.bool }
      | Solidity.BinaryOp.lt
      | Solidity.BinaryOp.gt
      | Solidity.BinaryOp.le
      | Solidity.BinaryOp.ge =>
          -- solc compares constant literals via their mobile types; a pair with
          -- no common mobile type (`2**300 < 2**301`, `1/2 < 1`) is a type error
          -- rather than a folded bool (CE-6a comparison cap).
          require
            (Solidity.Executable.Expr.numberComparisonFoldable? lhs rhs)
            (TypeError.expectedType lhsChecked.ty rhsChecked.ty)
          let _ ← CheckedExprs.relationalTy env.types lhsChecked rhsChecked
          Except.ok { source := expr, ty := Solidity.Ty.bool }
      | Solidity.BinaryOp.eq
      | Solidity.BinaryOp.ne =>
          require
            (Solidity.Executable.Expr.numberComparisonFoldable? lhs rhs)
            (TypeError.expectedType lhsChecked.ty rhsChecked.ty)
          require
            ((TypeContext.canImplicitlyConvert env.types
                rhsChecked.ty lhsChecked.ty ||
              implicitLiteralFits lhsChecked.ty rhsChecked.source) ||
            (TypeContext.canImplicitlyConvert env.types
                lhsChecked.ty rhsChecked.ty ||
              implicitLiteralFits rhsChecked.ty lhsChecked.source))
            (TypeError.expectedType lhsChecked.ty rhsChecked.ty)
          -- G3: reject `==`/`!=` on reference types (no builtin equality).
          require
            (Ty.isEqualityComparable env.types lhsChecked.ty &&
              Ty.isEqualityComparable env.types rhsChecked.ty)
            (TypeError.unsupported "equality on non-value type")
          Except.ok { source := expr, ty := Solidity.Ty.bool }
      | Solidity.BinaryOp.add
      | Solidity.BinaryOp.sub
      | Solidity.BinaryOp.mul
      | Solidity.BinaryOp.div
      | Solidity.BinaryOp.mod =>
          let ty ← CheckedExprs.arithmeticTy lhsChecked rhsChecked
          Except.ok { source := expr, ty := ty }
      | Solidity.BinaryOp.exp =>
          -- A `**` whose base and exponent are both constant number literals is
          -- folded by solc in the rational domain, where the exponent's type is
          -- `int_const` (not a signed integer *type*) — so solc imposes no
          -- unsigned-exponent restriction and even inverts negative exponents
          -- (`4 * 2**-1 = 2`, `0**-1 = 0`). Only the non-constant case carries the
          -- `expectUnsignedInteger` rule (CE-1).
          if (Solidity.Executable.Expr.numberLiteralRat? expr).isSome then
            Except.ok { source := expr, ty := lhsChecked.ty }
          else do
            lhsChecked.expectInteger
            rhsChecked.expectUnsignedInteger
            Except.ok { source := expr, ty := lhsChecked.ty }
      | Solidity.BinaryOp.bitAnd
      | Solidity.BinaryOp.bitOr
      | Solidity.BinaryOp.bitXor =>
          let ty ← CheckedExprs.bitwiseTy lhsChecked rhsChecked
          Except.ok { source := expr, ty := ty }
      | Solidity.BinaryOp.shl
      | Solidity.BinaryOp.shr =>
          lhsChecked.expectShiftLeftOperand
          rhsChecked.expectUnsignedInteger
          Except.ok { source := expr, ty := lhsChecked.ty }
      | Solidity.BinaryOp.sar =>
          lhsChecked.expectSignedInteger
          rhsChecked.expectUnsignedInteger
          Except.ok { source := expr, ty := lhsChecked.ty }
  | expr@(Solidity.Expr.ternary cond thenExpr elseExpr) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let thenChecked ← checkExpr env thenExpr
      let elseChecked ← checkExpr env elseExpr
      require (TypeContext.canImplicitlyConvert env.types
          elseChecked.ty thenChecked.ty ||
          TypeContext.canImplicitlyConvert env.types
            thenChecked.ty elseChecked.ty)
        (TypeError.expectedType thenChecked.ty elseChecked.ty)
      let resultTy :=
        -- A conditional of two untyped number literals adopts the ternary's
        -- COMMON (mobile) type (solc `TypeChecker::visit(Conditional)`), e.g.
        -- `(t ? 63 : 255) : uint8`, so narrowing/arithmetic use that width.
        match Solidity.Executable.Expr.untypedLiteralMobileTy? expr with
        | some mobileTy => mobileTy
        | none =>
            if TypeContext.canImplicitlyConvert env.types
                elseChecked.ty thenChecked.ty then
              thenChecked.ty
            else
              elseChecked.ty
      let resultLocation :=
        if thenChecked.dataLocation? == elseChecked.dataLocation? then
          thenChecked.dataLocation?
        else
          none
      Except.ok
        { source := expr
          ty := resultTy
          dataLocation? := resultLocation }
  | expr@(Solidity.Expr.assign lhs _ rhs) => do
      match lhs with
      | Solidity.Expr.tuple lhsItems =>
          match expr with
          | Solidity.Expr.assign _
              Solidity.AssignOp.assign _ =>
              if Solidity.Executable.TupleItems.hasNestedTuple lhsItems then
                -- Nested LHS `((a, b), c) = …` (G13): solc accepts these; the
                -- structure is checked recursively against a nested tuple RHS
                -- (`checkNestedTupleItems`), matching solc's left-to-right
                -- component semantics. The result type of a nested tuple
                -- assignment statement is unobservable, so it is left coarse.
                do
                  checkNestedTupleItems env lhsItems rhs
                  Except.ok
                    { source := expr
                      ty := Solidity.Ty.tuple []
                      lvalue := false }
              else do
                let targets ← checkTupleAssignmentTargets env lhsItems
                let resultTys ←
                  match rhs with
                  | Solidity.Expr.tuple _ =>
                      checkTupleAssignmentTargetsWithTupleExprAssignableTo env
                        targets rhs
                  | _ => do
                      let rhsChecked ← checkExpr env rhs
                      match rhsChecked.ty with
                      | Solidity.Ty.tuple tys =>
                          checkTupleAssignmentTargetsWithTys env targets tys
                            rhsChecked.storageRefs rhsChecked.dataLocations
                      | _ =>
                          Except.error
                            (TypeError.arityMismatch
                              "tuple assignment" lhsItems.length 1)
                Except.ok
                  { source := expr
                    ty := Solidity.Ty.tuple resultTys
                    lvalue := false }
          | _ => Except.error (TypeError.expectedLValue lhs)
      | _ => do
          let lhsChecked ← checkExpr env lhs
          require lhsChecked.lvalue (TypeError.expectedLValue lhs)
          lhsChecked.expectWritableLocation lhs
          let rebindsStoragePointer :=
            match expr, Expr.directIdentName? lhs with
            | Solidity.Expr.assign _
                Solidity.AssignOp.assign _, some name =>
                env.isPointerReturnName name || env.isLocalStorageRef name
            | _, _ => false
          if lhsChecked.stateLValue && !rebindsStoragePointer then
            requireStateWriteAllowed env
          else
            Except.ok ()
          let checkOrdinaryRhs : Except TypeError CheckedExpr := do
            let rhsChecked ← checkExpr env rhs
            match Expr.directIdentName? lhs with
            | some name =>
                require (!env.isLocalStorageRef name || rhsChecked.stateLValue)
                  (TypeError.invalidDataLocation lhsChecked.ty
                    (some Solidity.DataLocation.storage))
            | none => Except.ok ()
            if lhsChecked.locationIsCalldata then
              rhsChecked.expectLocationAssignableTo lhsChecked.ty
                lhsChecked.dataLocation?
            else
              Except.ok ()
            let opResultTy ←
              match expr with
              | Solidity.Expr.assign _
                  Solidity.AssignOp.assign _ => do
                  env.requireNoMappingStorageCopy lhs lhsChecked
                    rhsChecked.stateLValue
                  -- G14: a copy into a genuine storage-array variable accepts a
                  -- base-convertible / shorter source (solc's less-restrictive
                  -- storage-copy rule); the strict rule still governs pointer
                  -- rebinds and non-storage targets.
                  if lhsChecked.stateLValue && !rebindsStoragePointer &&
                      Ty.storageArrayCopyAssignable? lhsChecked.ty
                        rhsChecked.ty then
                    Except.ok ()
                  else
                    rhsChecked.expectAssignableToIn env.types lhsChecked.ty
                  Except.ok lhsChecked.ty
              | Solidity.Expr.assign _
                  Solidity.AssignOp.addAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.subAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.mulAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.divAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.modAssign _ =>
                  CheckedExprs.arithmeticTy lhsChecked rhsChecked
              | Solidity.Expr.assign _
                  Solidity.AssignOp.bitAndAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.bitOrAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.bitXorAssign _ =>
                  CheckedExprs.bitwiseTy lhsChecked rhsChecked
              | Solidity.Expr.assign _
                  Solidity.AssignOp.shlAssign _
              | Solidity.Expr.assign _
                  Solidity.AssignOp.shrAssign _ => do
                  lhsChecked.expectShiftLeftOperand
                  rhsChecked.expectUnsignedInteger
                  Except.ok lhsChecked.ty
              | Solidity.Expr.assign _
                  Solidity.AssignOp.sarAssign _ => do
                  lhsChecked.expectSignedInteger
                  rhsChecked.expectUnsignedInteger
                  Except.ok lhsChecked.ty
              | _ => Except.ok lhsChecked.ty
            require (TypeContext.canImplicitlyConvert env.types opResultTy
                lhsChecked.ty ||
                opResultTy == lhsChecked.ty)
              (TypeError.expectedType lhsChecked.ty opResultTy)
            Except.ok
              { source := expr, ty := lhsChecked.ty, lvalue := false }
          match expr with
          | Solidity.Expr.assign _
              Solidity.AssignOp.assign _ =>
              match
                  checkInternalFunctionValueAssignable?
                    env rhs lhsChecked.ty with
              | some result => do
                  result
                  Except.ok
                    { source := expr
                      ty := lhsChecked.ty
                      lvalue := false }
              | none =>
                  if exprIsContextualFixedArrayExpr env rhs lhsChecked.ty then
                    match Expr.directIdentName? lhs with
                    | some name => do
                        require (!env.isLocalStorageRef name)
                          (TypeError.invalidDataLocation lhsChecked.ty
                            (some Solidity.DataLocation.storage))
                        let rhsChecked ← checkExpr env rhs
                        if lhsChecked.locationIsCalldata then
                          rhsChecked.expectLocationAssignableTo lhsChecked.ty
                            lhsChecked.dataLocation?
                        else
                          Except.ok ()
                        Except.ok
                          { source := expr
                            ty := lhsChecked.ty
                            lvalue := false }
                    | none => do
                        let _ ← checkExpr env rhs
                        Except.ok
                          { source := expr
                            ty := lhsChecked.ty
                            lvalue := false }
                  else
                    checkOrdinaryRhs
          | _ => checkOrdinaryRhs
  | expr@(Solidity.Expr.payableConversion inner) => do
      let checked ← checkExpr env inner
      match checked.ty with
      | Solidity.Ty.address _ =>
          Except.ok
            { source := expr, ty := Solidity.Ty.address true,
              lvalue := false }
      | Solidity.Ty.user path =>
          require (env.types.contractCanReceiveEther path)
            (TypeError.expectedType
              (Solidity.Ty.address false) checked.ty)
          Except.ok
            { source := expr, ty := Solidity.Ty.address true,
              lvalue := false }
      | other =>
          match Solidity.Executable.Expr.toCorePayableLiteral?
              inner with
          | some _ =>
              Except.ok
                { source := expr, ty := Solidity.Ty.address true,
                  lvalue := false }
          | none =>
              Except.error
                (TypeError.expectedType
                  (Solidity.Ty.address false) other)
termination_by expr => sizeOf expr
decreasing_by
  all_goals
    try subst expr
    try subst rhs
    try subst lhs
    simp_wf
    try simp_all
    try simp_all [sizeOf]
    try omega
    try
      cases rhs <;> simp_all [sizeOf] <;> omega
    try
      cases target <;> simp_wf <;> try simp_all <;> omega
    try
      cases fn <;> simp_wf <;> try simp_all [sizeOf] <;> omega

def checkArg (env : CheckEnv) : Solidity.Arg ->
    Except TypeError CheckedExpr
  | Solidity.Arg.positional expr => checkExpr env expr
  | Solidity.Arg.named _ expr => checkExpr env expr
termination_by arg => sizeOf arg
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkArgs (env : CheckEnv) : List Solidity.Arg ->
    Except TypeError (List CheckedExpr)
  | [] => Except.ok []
  | arg :: rest => do
      let checked ← checkArg env arg
      let tail ← checkArgs env rest
      Except.ok (checked :: tail)
termination_by args => sizeOf args
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkArgAssignableToParam (env : CheckEnv) (expected : Ty) :
    Solidity.Arg -> Except TypeError CheckedExpr
  | Solidity.Arg.positional expr
  | Solidity.Arg.named _ expr =>
      let expected := env.qualifyCurrentLocalUserTypes expected
      match checkInternalFunctionValueAssignable? env expr expected with
      | some (Except.ok _) =>
          Except.ok
            { source := expr
              ty := expected
              lvalue := false
              stateLValue := false }
      | some (Except.error err) => Except.error err
      | none => do
          if exprIsContextualFixedArrayExpr env expr expected then
            let _ ← checkExpr env expr
            Except.ok
              { source := expr
                ty := expected
                lvalue := false
                stateLValue := false }
          else
            let checked ← checkExpr env expr
            let _ ← arrayLiteralFixedWidenCheck env.types checked expected
            Except.ok checked
termination_by arg => sizeOf arg
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkPositionalArgsAssignableToParamsFor
    (env : CheckEnv) (what : String) :
    List Solidity.Arg -> List Ty ->
    Except TypeError (List CheckedExpr)
  | [], [] => Except.ok []
  | arg :: argRest, ty :: tyRest => do
      let checked ← checkArgAssignableToParam env ty arg
      let tail ←
        checkPositionalArgsAssignableToParamsFor env what argRest tyRest
      Except.ok (checked :: tail)
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch what expected.length actual.length)
termination_by args _tys => sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkNamedArgsAssignableToParamsFor
    (env : CheckEnv) (what : String)
    (paramNames : List (Option Name)) (params : List Ty) :
    List Solidity.Arg -> Except TypeError (List CheckedExpr)
  | [] => Except.ok []
  | Solidity.Arg.named name expr :: rest => do
      let expected ←
        match FunctionSig.lookupParamTyByName? paramNames params name with
        | some ty => Except.ok ty
        | none =>
            Except.error
              (TypeError.arityMismatch what params.length (rest.length + 1))
      let checked ←
        checkArgAssignableToParam env expected
          (Solidity.Arg.named name expr)
      let tail ←
        checkNamedArgsAssignableToParamsFor env what paramNames params rest
      Except.ok (checked :: tail)
  | Solidity.Arg.positional _ :: rest =>
      Except.error
        (TypeError.arityMismatch what params.length (rest.length + 1))
termination_by args => sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkContractMemberCallArgsContextualForPath
    (env : CheckEnv) (path : Path) (member : Name)
    (args : List Solidity.Arg) :
    Except TypeError (FunctionSig × List CheckedExpr) := do
  let sig ←
    TypeContext.resolveContractMemberFunctionContextual env path member args
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor
        env "member call" sig.paramNames sig.params args
    else
      checkPositionalArgsAssignableToParamsFor
        env "member call" args sig.params
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsReferenceLocationsFor "member call" ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch "member call" sig.params.length
          checkedArgs.length)
  Except.ok (sig, checkedArgs)
termination_by 1 + sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkLibraryMemberCallArgsContextual
    (env : CheckEnv) (libraryName member : Name)
    (args : List Solidity.Arg) :
    Except TypeError (FunctionSig × List CheckedExpr) := do
  let path := TypeContext.pathOfName libraryName
  let libraryDecl ←
    match env.types.lookupContractDecl? path with
    | some libraryDecl => Except.ok libraryDecl
    | none => Except.error (TypeError.unknownType path)
  require (libraryDecl.kind == Solidity.ContractKind.library)
    (TypeError.invalidContractHeader "library call target is not a library")
  let sig ←
    FunctionSigs.resolveContextual env
      (FunctionSigs.nonPrivate
        (FunctionSigs.atLibraryCallBoundary env.types
          (ContractDecl.directFunctionSigsQualifiedLocalTypes libraryDecl)))
      member args
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor
        env "member call" sig.paramNames sig.params args
    else
      checkPositionalArgsAssignableToParamsFor
        env "member call" args sig.params
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsReferenceLocationsFor "member call" ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch "member call" sig.params.length
          checkedArgs.length)
  Except.ok (sig, checkedArgs)
termination_by 1 + sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkExplicitBaseMemberCallArgsContextual
    (env : CheckEnv) (baseName member : Name)
    (args : List Solidity.Arg) :
    Except TypeError (FunctionSig × List CheckedExpr) := do
  let path := TypeContext.pathOfName baseName
  require (TypeContext.pathIn path env.ancestorPaths)
    (TypeError.invalidFunctionHeader
      "explicit base call target is not a base contract")
  let baseDecl ←
    match env.types.lookupContractDecl? path with
    | some decl => Except.ok decl
    | none => Except.error (TypeError.unknownType path)
  let sig ←
    FunctionSigs.resolveContextual env
      (FunctionSigs.nonPrivate
        (ContractDecl.directFunctionSigsQualifiedLocalTypes baseDecl))
      member args
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor
        env "member call" sig.paramNames sig.params args
    else
      checkPositionalArgsAssignableToParamsFor
        env "member call" args sig.params
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsReferenceLocationsFor "member call" ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch "member call" sig.params.length
          checkedArgs.length)
  Except.ok (sig, checkedArgs)
termination_by 1 + sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkSuperMemberCallArgsContextual
    (env : CheckEnv) (member : Name)
    (args : List Solidity.Arg) :
    Except TypeError (FunctionSig × List CheckedExpr) := do
  let sig ←
    FunctionSigs.resolveContextual env env.superFunctions member args
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor
        env "super call" sig.paramNames sig.params args
    else
      checkPositionalArgsAssignableToParamsFor
        env "super call" args sig.params
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsReferenceLocationsFor "super call" ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch "super call" sig.params.length
          checkedArgs.length)
  Except.ok (sig, checkedArgs)
termination_by 1 + sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkMemberCallArgsContextual
    (env : CheckEnv) (target : Solidity.Expr)
    (member : Name) (args : List Solidity.Arg) :
    Except TypeError (List CheckedExpr) := do
  let targetChecked ← checkExpr env target
  if lowLevelCallMember member then
    match targetChecked.ty with
    | Solidity.Ty.user path =>
        require (env.types.isContractPath path)
          (TypeError.unsupported "contextual low-level member call")
    | _ =>
        Except.error (TypeError.unsupported "contextual low-level member call")
  require (!targetChecked.arraySlice)
    (TypeError.unsupported "member call on array slice")
  let candidates ←
    match target with
    | Solidity.Expr.ident libraryName =>
        if (env.lookupVar? libraryName).isNone &&
            TypeContext.pathIn
              (TypeContext.pathOfName libraryName) env.ancestorPaths then
          let baseDecl ←
            match env.types.lookupContractDecl?
                (TypeContext.pathOfName libraryName) with
            | some decl => Except.ok decl
            | none =>
                Except.error
                  (TypeError.unknownType
                    (TypeContext.pathOfName libraryName))
          Except.ok
            (FunctionSigs.nonPrivate
              (ContractDecl.directFunctionSigsQualifiedLocalTypes baseDecl))
        else
          match env.lookupVar? libraryName,
              env.types.lookupContractDecl?
                (TypeContext.pathOfName libraryName) with
          | none, some libraryDecl =>
              if libraryDecl.kind ==
                  Solidity.ContractKind.library then
                Except.ok
                  (FunctionSigs.nonPrivate
                    (FunctionSigs.atLibraryCallBoundary env.types
                      (ContractDecl.directFunctionSigsQualifiedLocalTypes
                        libraryDecl)))
              else
                UsingDecls.memberCandidates env targetChecked member
                  env.usingDecls
          | _, _ =>
              UsingDecls.memberCandidates env targetChecked member
                env.usingDecls
    | _ =>
        UsingDecls.memberCandidates env targetChecked member
          env.usingDecls
  let sig ← FunctionSigs.resolveContextual env candidates member args
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor
        env "member call" sig.paramNames sig.params args
    else
      checkPositionalArgsAssignableToParamsFor
        env "member call" args sig.params
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsReferenceLocationsFor "member call" ordered
        sig.paramStorageRefs sig.paramDataLocations
  | none =>
      Except.error
        (TypeError.arityMismatch "member call" sig.params.length
          checkedArgs.length)
  Except.ok checkedArgs
termination_by 1 + sizeOf target + sizeOf args
decreasing_by
  all_goals
    simp_wf
    try omega

def checkCallOption (env : CheckEnv) :
    Solidity.CallOption -> Except TypeError Unit
  | Solidity.CallOption.named name expr => do
      let checked ← checkExpr env expr
      if name == "gas" || name == "value" then
        checked.expectAssignableTo (Solidity.Ty.uint 256)
      else if name == "salt" then
        requireEqTy (Solidity.Ty.bytesN 32) checked.ty
      else
        Except.error (TypeError.unsupported ("call option " ++ name))
termination_by option => sizeOf option
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkCallOptionsLoop (env : CheckEnv) :
    List Solidity.CallOption -> Except TypeError Unit
  | [] => Except.ok ()
  | option :: rest => do
      checkCallOption env option
      checkCallOptionsLoop env rest
termination_by options => sizeOf options
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkTupleItems (env : CheckEnv) :
    List Solidity.TupleItem -> Except TypeError (List Ty)
  | [] => Except.ok []
  | Solidity.TupleItem.hole :: rest => do
      let tail ← checkTupleItems env rest
      Except.ok tail
  | Solidity.TupleItem.value expr :: rest => do
      let checked ← checkExpr env expr
      let tail ← checkTupleItems env rest
      Except.ok (checked.ty :: tail)
termination_by items => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkTupleAssignmentTargets (env : CheckEnv) :
    List Solidity.TupleItem ->
    Except TypeError (List TupleAssignmentTarget)
  | [] => Except.ok []
  | Solidity.TupleItem.hole :: rest => do
      let tail ← checkTupleAssignmentTargets env rest
      Except.ok (none :: tail)
  | Solidity.TupleItem.value target :: rest => do
      let targetChecked ← checkExpr env target
      require targetChecked.lvalue (TypeError.expectedLValue target)
      targetChecked.expectWritableLocation target
      if targetChecked.stateLValue then
        requireStateWriteAllowed env
      else
        Except.ok ()
      let tail ← checkTupleAssignmentTargets env rest
      Except.ok (some (target, targetChecked) :: tail)
termination_by items => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkTupleAssignmentTargetsWithTupleExprAssignableTo (env : CheckEnv) :
    List TupleAssignmentTarget -> Solidity.Expr ->
    Except TypeError (List Ty)
  | [], Solidity.Expr.tuple [] => Except.ok []
  | none :: targetRest,
      Solidity.Expr.tuple
        (Solidity.TupleItem.value expr :: itemRest) => do
      let _ ← checkExpr env expr
      checkTupleAssignmentTargetsWithTupleExprAssignableTo env targetRest
        (Solidity.Expr.tuple itemRest)
  | some (target, targetChecked) :: targetRest,
      Solidity.Expr.tuple
        (Solidity.TupleItem.value expr :: itemRest) => do
      let checked ←
        checkArgAssignableToParam env targetChecked.ty
          (Solidity.Arg.positional expr)
      match Expr.directIdentName? target with
      | some name =>
          require (!env.isLocalStorageRef name || checked.stateLValue)
            (TypeError.invalidDataLocation targetChecked.ty
              (some Solidity.DataLocation.storage))
      | none => Except.ok ()
      env.requireNoMappingStorageCopy target targetChecked
        checked.stateLValue
      if targetChecked.locationIsCalldata then
        checked.expectLocationAssignableTo targetChecked.ty
          targetChecked.dataLocation?
      else
        Except.ok ()
      let tail ←
        checkTupleAssignmentTargetsWithTupleExprAssignableTo env targetRest
          (Solidity.Expr.tuple itemRest)
      Except.ok (targetChecked.ty :: tail)
  | _ :: _, Solidity.Expr.tuple
      (Solidity.TupleItem.hole :: _) =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | targets, Solidity.Expr.tuple items =>
      Except.error
        (TypeError.arityMismatch
          "tuple assignment" targets.length items.length)
  | targets, _ =>
      Except.error
        (TypeError.arityMismatch
          "tuple assignment" targets.length 1)
termination_by _ rhs => sizeOf rhs
decreasing_by
  all_goals
    simp_wf
    try simp_all [sizeOf]
    try omega

-- R1 (residue-cleanup): type-check a nested tuple-assignment LHS against the
-- ELEMENT TYPES of a value whose type is a tuple (e.g. a multi-return internal
-- call filling a nested target: `((a, b), c) = (foo(), bar())`, `foo` returning
-- `(uint, uint)`). Each leaf target reproduces the flat leaf discipline
-- (lvalue / writable / state-write / assignability); a nested target recurses
-- into the matching tuple element type; a hole skips.
def checkNestedTupleTargetsAgainstTys (env : CheckEnv) :
    List Solidity.TupleItem -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | Solidity.TupleItem.hole :: lhsRest, _ :: tyRest =>
      checkNestedTupleTargetsAgainstTys env lhsRest tyRest
  | Solidity.TupleItem.value (Solidity.Expr.tuple lhsInner) :: lhsRest,
      ty :: tyRest => do
      (match ty with
       | Ty.tuple innerTys =>
           checkNestedTupleTargetsAgainstTys env lhsInner innerTys
       | _ =>
           Except.error
             (TypeError.unsupported
               "nested tuple assignment target needs a tuple-typed value"))
      checkNestedTupleTargetsAgainstTys env lhsRest tyRest
  | Solidity.TupleItem.value target :: lhsRest, ty :: tyRest => do
      let targetChecked ← checkExpr env target
      require targetChecked.lvalue (TypeError.expectedLValue target)
      targetChecked.expectWritableLocation target
      if targetChecked.stateLValue then
        requireStateWriteAllowed env
      else
        Except.ok ()
      let _ ←
        checkTupleAssignmentTargetAgainstTy env false none
          target targetChecked ty
      checkNestedTupleTargetsAgainstTys env lhsRest tyRest
  | lhsItems, tys =>
      Except.error
        (TypeError.arityMismatch
          "nested tuple assignment" lhsItems.length tys.length)
termination_by lhsItems _ => sizeOf lhsItems
decreasing_by
  all_goals
    simp_wf
    try simp_all [sizeOf]
    try omega

-- Type-check a (possibly nested) tuple-assignment LHS against a nested tuple
-- RHS, in lockstep left-to-right (G13). A parenthesized sub-tuple target
-- recurses into the matching sub-tuple value; a leaf target reproduces the flat
-- path's lvalue / writable-location / state-write / assignability /
-- mapping-copy / calldata-location discipline inline (on syntactic subterms, so
-- termination stays structural); a hole still type-checks its RHS component.
-- R1: a nested target whose RHS component is NOT a tuple literal but has a
-- tuple TYPE (a multi-return internal call) is checked via
-- `checkNestedTupleTargetsAgainstTys`.
def checkNestedTupleItems (env : CheckEnv) :
    List Solidity.TupleItem -> Solidity.Expr -> Except TypeError Unit
  | [], Solidity.Expr.tuple [] => Except.ok ()
  | Solidity.TupleItem.value (Solidity.Expr.tuple lhsInner) :: lhsRest,
      Solidity.Expr.tuple
        (Solidity.TupleItem.value (Solidity.Expr.tuple rhsInner) :: rhsRest) =>
      do
      checkNestedTupleItems env lhsInner (Solidity.Expr.tuple rhsInner)
      checkNestedTupleItems env lhsRest (Solidity.Expr.tuple rhsRest)
  | Solidity.TupleItem.value (Solidity.Expr.tuple lhsInner) :: lhsRest,
      Solidity.Expr.tuple (Solidity.TupleItem.value rhsExpr :: rhsRest) => do
      -- R1: nested LHS target aligned with a NON-tuple-literal RHS component
      -- whose type is a tuple (a multi-return internal call). The tuple-literal
      -- RHS subcase was already handled by the earlier pattern; this evaluates
      -- the component's type and destructures the nested target against it.
      let checked ← checkExpr env rhsExpr
      (match checked.ty with
       | Ty.tuple innerTys =>
           checkNestedTupleTargetsAgainstTys env lhsInner innerTys
       | _ =>
           Except.error
             (TypeError.unsupported
               "nested tuple assignment target needs a tuple-typed value"))
      checkNestedTupleItems env lhsRest (Solidity.Expr.tuple rhsRest)
  | Solidity.TupleItem.value (Solidity.Expr.tuple _) :: _, _ =>
      Except.error
        (TypeError.unsupported
          "nested tuple assignment target needs a nested tuple value")
  | Solidity.TupleItem.hole :: lhsRest,
      Solidity.Expr.tuple (Solidity.TupleItem.value rhsExpr :: rhsRest) => do
      let _ ← checkExpr env rhsExpr
      checkNestedTupleItems env lhsRest (Solidity.Expr.tuple rhsRest)
  | Solidity.TupleItem.value target :: lhsRest,
      Solidity.Expr.tuple (Solidity.TupleItem.value rhsExpr :: rhsRest) => do
      let targetChecked ← checkExpr env target
      require targetChecked.lvalue (TypeError.expectedLValue target)
      targetChecked.expectWritableLocation target
      if targetChecked.stateLValue then
        requireStateWriteAllowed env
      else
        Except.ok ()
      let checked ←
        checkArgAssignableToParam env targetChecked.ty
          (Solidity.Arg.positional rhsExpr)
      (match Expr.directIdentName? target with
       | some name =>
           require (!env.isLocalStorageRef name || checked.stateLValue)
             (TypeError.invalidDataLocation targetChecked.ty
               (some Solidity.DataLocation.storage))
       | none => Except.ok ())
      env.requireNoMappingStorageCopy target targetChecked checked.stateLValue
      if targetChecked.locationIsCalldata then
        checked.expectLocationAssignableTo targetChecked.ty
          targetChecked.dataLocation?
      else
        Except.ok ()
      checkNestedTupleItems env lhsRest (Solidity.Expr.tuple rhsRest)
  | _ :: _, Solidity.Expr.tuple (Solidity.TupleItem.hole :: _) =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | lhsItems, Solidity.Expr.tuple rhsItems =>
      Except.error
        (TypeError.arityMismatch
          "nested tuple assignment" lhsItems.length rhsItems.length)
  | lhsItems, _ =>
      Except.error
        (TypeError.arityMismatch
          "nested tuple assignment" lhsItems.length 1)
termination_by lhsItems rhs => sizeOf lhsItems + sizeOf rhs
decreasing_by
  all_goals
    simp_wf
    try simp_all [sizeOf]
    try omega

def checkTupleItemValuesAssignableTo (env : CheckEnv) :
    List Solidity.TupleItem -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | Solidity.TupleItem.value expr :: rest, ty :: tyRest => do
      let checked ← checkExpr env expr
      checked.expectAssignableToIn env.types ty
      checkTupleItemValuesAssignableTo env rest tyRest
  | Solidity.TupleItem.hole :: _, _ =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)
termination_by items _ => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkEncodeCallTupleItemsAssignableTo (env : CheckEnv) :
    List Solidity.TupleItem -> List Ty ->
    Except TypeError (List CheckedExpr)
  | [], [] => Except.ok []
  | Solidity.TupleItem.hole :: _, _ =>
      Except.error
        (TypeError.invalidAbiCall
          "abi.encodeCall argument tuple cannot contain holes")
  | Solidity.TupleItem.value expr :: rest, ty :: tyRest => do
      let checked ←
        checkArgAssignableToParam env ty
          (Solidity.Arg.positional expr)
      let tail ← checkEncodeCallTupleItemsAssignableTo env rest tyRest
      Except.ok (checked :: tail)
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch
          "abi.encodeCall" expected.length actual.length)
termination_by items _ => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkArrayElements (env : CheckEnv) (expected : Ty) :
    List Solidity.Expr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      let checked ← checkExpr env expr
      checked.expectAssignableToIn env.types expected
      checkArrayElements env expected rest
termination_by exprs => sizeOf exprs
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkExprList (env : CheckEnv) :
    List Solidity.Expr -> Except TypeError (List CheckedExpr)
  | [] => Except.ok []
  | expr :: rest => do
      let checked ← checkExpr env expr
      let tail ← checkExprList env rest
      Except.ok (checked :: tail)
termination_by exprs => sizeOf exprs
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

end

def checkContextualArgsAssignableToParamsFor
    (env : CheckEnv) (what : String)
    (paramNames : List (Option Name)) (params : List Ty)
    (args : List Solidity.Arg) :
    Except TypeError (List CheckedExpr) := do
  let checkedArgs ←
    if Args.anyNamed args then
      checkNamedArgsAssignableToParamsFor env what paramNames params args
    else
      checkPositionalArgsAssignableToParamsFor env what args params
  match CheckedArgInfos.ordered? paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some _ => Except.ok checkedArgs
  | none =>
      Except.error
        (TypeError.arityMismatch what params.length checkedArgs.length)

def checkContextualArgsAssignableToParamsWithStorageRefsFor
    (env : CheckEnv) (what : String)
    (paramNames : List (Option Name)) (params : List Ty)
    (paramStorageRefs : List Bool)
    (paramDataLocations :
      List (Option Solidity.DataLocation))
    (args : List Solidity.Arg) :
    Except TypeError (List CheckedExpr) := do
  let checkedArgs ←
    checkContextualArgsAssignableToParamsFor env what paramNames params args
  match CheckedArgInfos.ordered? paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered => do
      checkCheckedExprsReferenceLocationsFor what ordered paramStorageRefs
        paramDataLocations
      Except.ok checkedArgs
  | none =>
      Except.error
        (TypeError.arityMismatch what params.length checkedArgs.length)

def checkModifierArgs (env : CheckEnv)
    (name : Name) (args : List Solidity.Arg) :
    Except TypeError Unit := do
  match checkArgs env args with
  | Except.ok checkedArgs =>
      let argInfos := checkedArgInfosFull args checkedArgs
      match ModifierSigs.resolveChecked env.types env.modifiers name argInfos with
      | Except.ok _ => Except.ok ()
      | Except.error checkedErr =>
          match ModifierSigs.resolveContextual env env.modifiers name args with
          | Except.ok sig => do
              let _ ←
                checkContextualArgsAssignableToParamsWithStorageRefsFor
                  env "modifier invocation" sig.paramNames sig.params
                  sig.paramStorageRefs sig.paramDataLocations args
              Except.ok ()
          | Except.error _ => Except.error checkedErr
  | Except.error argErr =>
      match ModifierSigs.resolveContextual env env.modifiers name args with
      | Except.ok sig => do
          let _ ←
            checkContextualArgsAssignableToParamsWithStorageRefsFor
              env "modifier invocation" sig.paramNames sig.params
              sig.paramStorageRefs sig.paramDataLocations args
          Except.ok ()
      | Except.error _ => Except.error argErr

def checkEventArgs (env : CheckEnv)
    (name : Name) (args : List Solidity.Arg) :
    Except TypeError Unit := do
  match checkArgs env args with
  | Except.ok checkedArgs =>
      let argInfos := checkedArgInfosFull args checkedArgs
      match EventSigs.resolveChecked env.types env.events name argInfos with
      | Except.ok _ => Except.ok ()
      | Except.error checkedErr =>
          match EventSigs.resolveContextual env env.events name args with
          | Except.ok sig => do
              let _ ←
                checkContextualArgsAssignableToParamsFor
                  env "event emission" sig.paramNames sig.params args
              Except.ok ()
          | Except.error _ => Except.error checkedErr
  | Except.error argErr =>
      match EventSigs.resolveContextual env env.events name args with
      | Except.ok sig => do
          let _ ←
            checkContextualArgsAssignableToParamsFor
              env "event emission" sig.paramNames sig.params args
          Except.ok ()
      | Except.error _ => Except.error argErr

def checkCustomErrorArgs (env : CheckEnv)
    (name : Name) (args : List Solidity.Arg) :
    Except TypeError Unit := do
  -- G8: `revert E(...)` where `E`'s innermost declaration is NOT an error —
  -- a local variable, or a contract-level non-error member (function / state
  -- var / modifier / event) shadowing a free error — is rejected by solc
  -- (TypeError 1885). A contract-level error `E` never has a same-name
  -- contract member, and free functions are excluded from
  -- `contractNonErrorMemberNames`, so a valid error revert still proceeds.
  if env.isLocalName name ||
      Solidity.Executable.nameIn name env.contractNonErrorMemberNames then
    Except.error
      (TypeError.unsupported ("revert target is not an error: " ++ name))
  else
  match checkArgs env args with
  | Except.ok checkedArgs =>
      let argInfos := checkedArgInfosFull args checkedArgs
      match ErrorSigs.resolveChecked env.types env.errors name argInfos with
      | Except.ok _ => Except.ok ()
      | Except.error checkedErr =>
          match ErrorSigs.resolveContextual env env.errors name args with
          | Except.ok sig => do
              let _ ←
                checkContextualArgsAssignableToParamsFor
                  env "custom error" sig.paramNames sig.params args
              Except.ok ()
          | Except.error _ => Except.error checkedErr
  | Except.error argErr =>
      match ErrorSigs.resolveContextual env env.errors name args with
      | Except.ok sig => do
          let _ ←
            checkContextualArgsAssignableToParamsFor
              env "custom error" sig.paramNames sig.params args
          Except.ok ()
      | Except.error _ => Except.error argErr

mutual

def checkExprAssignableTo (env : CheckEnv) :
    Solidity.Expr -> Ty -> Except TypeError Unit
  | expr@(Solidity.Expr.array elements),
    expected@(Solidity.Ty.array _ (some size)) => do
      require (elements.length == size)
        (TypeError.arityMismatch "array literal" size elements.length)
      if exprContextuallyAssignableTo env expr expected then
        let _ ← checkExpr env expr
        Except.ok ()
      else
        let checked ← checkExpr env expr
        arrayLiteralFixedWidenCheck env.types checked expected
  | Solidity.Expr.ternary cond thenExpr elseExpr,
    expected@(Solidity.Ty.array _ (some _)) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      checkExprAssignableTo env thenExpr expected
      checkExprAssignableTo env elseExpr expected
  | expr, expected =>
      match checkInternalFunctionValueAssignable? env expr expected with
      | some result => result
      | none => do
          let checked ← checkExpr env expr
          checked.expectAssignableToIn env.types expected
termination_by expr _ => sizeOf expr
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try simp_all [sizeOf]
    try omega

end

def checkTupleItemValuesContextuallyAssignableTo (env : CheckEnv) :
    List Solidity.TupleItem -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | Solidity.TupleItem.value expr :: rest, ty :: tyRest => do
      checkExprAssignableTo env expr ty
      checkTupleItemValuesContextuallyAssignableTo env rest tyRest
  | Solidity.TupleItem.hole :: _, _ =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)

def checkExprAssignableToReferenceLocation (env : CheckEnv)
    (expr : Solidity.Expr) (expected : Ty)
    (needsStorageRef : Bool)
    (expectedLocation : Option Solidity.DataLocation) :
    Except TypeError Unit := do
  checkExprAssignableTo env expr expected
  let checked ← checkExpr env expr
  if needsStorageRef then
    require checked.stateLValue
      (TypeError.invalidDataLocation expected
        (some Solidity.DataLocation.storage))
  else
    Except.ok ()
  checked.expectLocationAssignableTo expected expectedLocation

def checkTupleItemValuesContextuallyAssignableToWithStorageRefs
    (env : CheckEnv) :
    List Solidity.TupleItem -> List Ty -> List Bool ->
    List (Option Solidity.DataLocation) ->
    Except TypeError Unit
  | [], [], _, _ => Except.ok ()
  | Solidity.TupleItem.value expr :: rest,
      ty :: tyRest, storageRef :: storageRest,
      location :: locationRest => do
      checkExprAssignableToReferenceLocation env expr ty storageRef location
      checkTupleItemValuesContextuallyAssignableToWithStorageRefs env rest
        tyRest storageRest locationRest
  | Solidity.TupleItem.value expr :: rest,
      ty :: tyRest, storageRef :: storageRest, [] => do
      checkExprAssignableToReferenceLocation env expr ty storageRef none
      checkTupleItemValuesContextuallyAssignableToWithStorageRefs env rest
        tyRest storageRest []
  | Solidity.TupleItem.value expr :: rest,
      ty :: tyRest, [], location :: locationRest => do
      checkExprAssignableToReferenceLocation env expr ty false location
      checkTupleItemValuesContextuallyAssignableToWithStorageRefs env rest
        tyRest [] locationRest
  | Solidity.TupleItem.value expr :: rest,
      ty :: tyRest, [], [] => do
      checkExprAssignableToReferenceLocation env expr ty false none
      checkTupleItemValuesContextuallyAssignableToWithStorageRefs env rest
        tyRest [] []
  | Solidity.TupleItem.hole :: _, _, _, _ =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | actual, expected, _, _ =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)

def constantBuiltinIdentCallAllowed (name : Name) : Bool :=
  name == "keccak256" || name == "sha256" || name == "ripemd160" ||
    name == "ecrecover" || name == "addmod" || name == "mulmod" ||
    name == "erc7201"

def constantAbiMemberCallAllowed (member : Name) : Bool :=
  member == "encode" || member == "encodePacked" ||
    member == "encodeWithSelector" || member == "encodeWithSignature" ||
    member == "decode"

def exprIsCompileTimeConstantCallTarget
    (fn : Solidity.Expr) : Bool :=
  match fn with
  | Solidity.Expr.typeName _ => true
  | Solidity.Expr.ident name =>
      constantBuiltinIdentCallAllowed name
  | Solidity.Expr.member
      (Solidity.Expr.ident "abi") member =>
      constantAbiMemberCallAllowed member
  | Solidity.Expr.member
      (Solidity.Expr.ident "bytes") "concat" => true
  | Solidity.Expr.member
      (Solidity.Expr.ident "string") "concat" => true
  | Solidity.Expr.member
      (Solidity.Expr.typeName Solidity.Ty.bytes)
      "concat" => true
  | Solidity.Expr.member
      (Solidity.Expr.typeName Solidity.Ty.string)
      "concat" => true
  | Solidity.Expr.member
      (Solidity.Expr.typeName _) member =>
      member == "wrap" || member == "unwrap"
  | _ => false

mutual

def exprIsCompileTimeConstant (env : CheckEnv) :
    Solidity.Expr -> Bool
  | Solidity.Expr.literal _ => true
  | Solidity.Expr.ident name => env.isConstantName name
  | Solidity.Expr.typeName _ => true
  | Solidity.Expr.member
      (Solidity.Expr.typeName _) _ => true
  | Solidity.Expr.member _ _ => false
  | Solidity.Expr.index base index =>
      exprIsCompileTimeConstant env base &&
        exprIsCompileTimeConstant env index
  | Solidity.Expr.slice base start? stop? =>
      let startOk :=
        match start? with
        | none => true
        | some start => exprIsCompileTimeConstant env start
      let stopOk :=
        match stop? with
        | none => true
        | some stop => exprIsCompileTimeConstant env stop
      exprIsCompileTimeConstant env base &&
        startOk && stopOk
  | Solidity.Expr.call fn args =>
      exprIsCompileTimeConstantCallTarget fn &&
        argsAllCompileTimeConstant env args
  | Solidity.Expr.callWithOptions _ _ _ => false
  | Solidity.Expr.newExpr _ args =>
      argsAllCompileTimeConstant env args
  | Solidity.Expr.tuple items =>
      tupleItemsAllCompileTimeConstant env items
  | Solidity.Expr.array exprs =>
      exprsAllCompileTimeConstant env exprs
  | Solidity.Expr.enumFromUInt _ inner =>
      exprIsCompileTimeConstant env inner
  | Solidity.Expr.unary op inner =>
      match op with
      | Solidity.UnaryOp.logicalNot
      | Solidity.UnaryOp.bitNot
      | Solidity.UnaryOp.neg =>
          exprIsCompileTimeConstant env inner
      | Solidity.UnaryOp.delete
      | Solidity.UnaryOp.preIncrement
      | Solidity.UnaryOp.preDecrement
      | Solidity.UnaryOp.postIncrement
      | Solidity.UnaryOp.postDecrement => false
  | Solidity.Expr.binary _ lhs rhs =>
      exprIsCompileTimeConstant env lhs &&
        exprIsCompileTimeConstant env rhs
  | Solidity.Expr.ternary cond thenExpr elseExpr =>
      exprIsCompileTimeConstant env cond &&
        exprIsCompileTimeConstant env thenExpr &&
          exprIsCompileTimeConstant env elseExpr
  | Solidity.Expr.assign _ _ _ => false
  | Solidity.Expr.payableConversion inner =>
      exprIsCompileTimeConstant env inner

def exprsAllCompileTimeConstant (env : CheckEnv) :
    List Solidity.Expr -> Bool
  | [] => true
  | expr :: rest =>
      exprIsCompileTimeConstant env expr &&
        exprsAllCompileTimeConstant env rest

def argIsCompileTimeConstant (env : CheckEnv) :
    Solidity.Arg -> Bool
  | Solidity.Arg.positional expr =>
      exprIsCompileTimeConstant env expr
  | Solidity.Arg.named _ expr =>
      exprIsCompileTimeConstant env expr

def argsAllCompileTimeConstant (env : CheckEnv) :
    List Solidity.Arg -> Bool
  | [] => true
  | arg :: rest =>
      argIsCompileTimeConstant env arg &&
        argsAllCompileTimeConstant env rest

def tupleItemIsCompileTimeConstant (env : CheckEnv) :
    Solidity.TupleItem -> Bool
  | Solidity.TupleItem.hole => true
  | Solidity.TupleItem.value expr =>
      exprIsCompileTimeConstant env expr

def tupleItemsAllCompileTimeConstant (env : CheckEnv) :
    List Solidity.TupleItem -> Bool
  | [] => true
  | item :: rest =>
      tupleItemIsCompileTimeConstant env item &&
        tupleItemsAllCompileTimeConstant env rest

end

def Expr.isCompileTimeConstant (env : CheckEnv)
    (expr : Solidity.Expr) : Bool :=
  exprIsCompileTimeConstant env expr

def exprIsStorageLayoutBaseErc7201Id (env : CheckEnv) :
    Solidity.Expr -> Bool
  | Solidity.Expr.literal
      (Solidity.Literal.string _) => true
  | Solidity.Expr.literal
      (Solidity.Literal.unicodeString _) => true
  | Solidity.Expr.ident name => env.isConstantName name
  | _ => false

def exprIsStorageLayoutBaseComptime (env : CheckEnv) :
    Solidity.Expr -> Bool
  | Solidity.Expr.literal (Solidity.Literal.number _) =>
      true
  | Solidity.Expr.literal
      (Solidity.Literal.unitNumber _ _) => true
  | Solidity.Expr.ident name => env.isConstantName name
  | Solidity.Expr.call (Solidity.Expr.ident "erc7201")
      [Solidity.Arg.positional id] =>
      exprIsStorageLayoutBaseErc7201Id env id
  | Solidity.Expr.unary Solidity.UnaryOp.neg inner =>
      exprIsStorageLayoutBaseComptime env inner
  | Solidity.Expr.binary op lhs rhs =>
      Solidity.Executable.BinaryOp.storageLayoutBaseEvalAllowed op &&
        exprIsStorageLayoutBaseComptime env lhs &&
        exprIsStorageLayoutBaseComptime env rhs
  | _ => false

def Expr.isStorageLayoutBaseComptime (env : CheckEnv)
    (expr : Solidity.Expr) : Bool :=
  exprIsStorageLayoutBaseComptime env expr

def Exprs.allCompileTimeConstant (env : CheckEnv)
    (exprs : List Solidity.Expr) : Bool :=
  exprsAllCompileTimeConstant env exprs

/-- solc `ViewPureChecker.cpp:194-199`: an immutable read is `Pure` **only if**
the initializer's type category is `RationalNumber` (a pure numeric-literal
constant / constant arithmetic thereof). Any other initializer
(`keccak256(...)`, a `constant` reference, a `bool`/`string` literal, an
explicit conversion like `uint(5)`, `abi.*`, `type().wrap`, …) makes the read
`View`. This predicate models exactly the `RationalNumber` category: numeric
(`number`/`unitNumber`) literals, unary `-`/`~` over a rational, and the
arithmetic/bitwise/shift binary operators over rationals (comparison and logical
operators yield `bool`, not `RationalNumber`, and ternaries are not folded to a
rational). Probed against pinned solc 0.8.35 (`5`, `2+3`, `1 ether`, `-3`, `~1`,
`1<<4` ACCEPT in `pure`; `keccak256("x")`, a `constant` ref, `true`, `uint(5)`,
`3<5`, `true?1:2` REJECT with error 2527). -/
def exprIsRationalConstant : Solidity.Expr -> Bool
  | Solidity.Expr.literal (Solidity.Literal.number _) => true
  | Solidity.Expr.literal (Solidity.Literal.unitNumber _ _) => true
  | Solidity.Expr.unary op inner =>
      match op with
      | Solidity.UnaryOp.neg
      | Solidity.UnaryOp.bitNot => exprIsRationalConstant inner
      | _ => false
  | Solidity.Expr.binary op lhs rhs =>
      Solidity.Executable.BinaryOp.storageLayoutBaseEvalAllowed op &&
        exprIsRationalConstant lhs &&
        exprIsRationalConstant rhs
  | _ => false

/- Collect every identifier name syntactically referenced by an expression.
Used only to build the `constant`-value dependency graph for solc's
`ConstStateVarCircularReferenceChecker` (`PostTypeChecker.cpp:154-245`, error
6161). Over-collection is harmless: the cycle detector intersects the result
with the set of declared `constant` names, so non-constant idents (builtins,
types, functions) drop out. -/
mutual

def collectExprIdents : Solidity.Expr -> List Name
  | Solidity.Expr.literal _ => []
  | Solidity.Expr.ident name => [name]
  | Solidity.Expr.typeName _ => []
  | Solidity.Expr.member base _ => collectExprIdents base
  | Solidity.Expr.index base idx =>
      collectExprIdents base ++ collectExprIdents idx
  | Solidity.Expr.slice base start? stop? =>
      collectExprIdents base ++
        (match start? with | some e => collectExprIdents e | none => []) ++
        (match stop? with | some e => collectExprIdents e | none => [])
  | Solidity.Expr.call fn args =>
      collectExprIdents fn ++ collectArgIdents args
  | Solidity.Expr.callWithOptions fn opts args =>
      collectExprIdents fn ++ collectOptionIdents opts ++ collectArgIdents args
  | Solidity.Expr.newExpr _ args => collectArgIdents args
  | Solidity.Expr.tuple items => collectTupleItemIdents items
  | Solidity.Expr.array exprs => collectExprListIdents exprs
  | Solidity.Expr.enumFromUInt _ inner => collectExprIdents inner
  | Solidity.Expr.unary _ inner => collectExprIdents inner
  | Solidity.Expr.binary _ lhs rhs =>
      collectExprIdents lhs ++ collectExprIdents rhs
  | Solidity.Expr.ternary cond thenExpr elseExpr =>
      collectExprIdents cond ++ collectExprIdents thenExpr ++
        collectExprIdents elseExpr
  | Solidity.Expr.assign lhs _ rhs =>
      collectExprIdents lhs ++ collectExprIdents rhs
  | Solidity.Expr.payableConversion inner => collectExprIdents inner

def collectExprListIdents : List Solidity.Expr -> List Name
  | [] => []
  | e :: rest => collectExprIdents e ++ collectExprListIdents rest

def collectArgIdents : List Solidity.Arg -> List Name
  | [] => []
  | Solidity.Arg.positional e :: rest =>
      collectExprIdents e ++ collectArgIdents rest
  | Solidity.Arg.named _ e :: rest =>
      collectExprIdents e ++ collectArgIdents rest

def collectOptionIdents : List Solidity.CallOption -> List Name
  | [] => []
  | Solidity.CallOption.named _ e :: rest =>
      collectExprIdents e ++ collectOptionIdents rest

def collectTupleItemIdents : List Solidity.TupleItem -> List Name
  | [] => []
  | Solidity.TupleItem.hole :: rest => collectTupleItemIdents rest
  | Solidity.TupleItem.value e :: rest =>
      collectExprIdents e ++ collectTupleItemIdents rest

end

/-- Direct `constant`→`constant` dependency edges: the declared constant names
referenced in `decl`'s initializer. -/
def StateVarDecl.constantDeps (constNames : List Name)
    (decl : Solidity.StateVarDecl) : List Name :=
  match decl.init with
  | some init => (collectExprIdents init).filter (fun n => constNames.contains n)
  | none => []

/-- One BFS/closure step: successors of the current reached set. -/
def constantDepStep (adj : List (Name × List Name))
    (reached : List Name) : List Name :=
  reached.foldl
    (fun acc n =>
      match adj.find? (fun p => p.fst == n) with
      | some p => acc ++ p.snd
      | none => acc)
    []

/-- Whether `start` can reach itself through the `constant`-dependency graph
`adj` (i.e. lies on a cycle). Fuel-bounded by the node count. -/
partial def constantReachesSelf (adj : List (Name × List Name))
    (start : Name) : Bool :=
  let rec go (fuel : Nat) (reached : List Name) : Bool :=
    if reached.contains start then true
    else match fuel with
      | 0 => false
      | fuel + 1 =>
          let next :=
            (reached ++ constantDepStep adj reached).eraseDups
          if next.length == reached.length then false
          else go fuel next
  go adj.length (constantDepStep adj [start])

/-- solc `ConstStateVarCircularReferenceChecker` (`PostTypeChecker.cpp:154-245`,
error 6161): a `constant` state variable whose value expression cyclically
depends on itself (directly or via other constants) is rejected. Detects a cycle
among the `constant` declarations in `decls` (probed against pinned solc 0.8.35:
`uint constant A = A;` and `uint constant A = B; uint constant B = A;` REJECT;
`uint constant A = 5; uint constant B = A + 1;` ACCEPTS). -/
def StateVarDecls.constantsHaveCycle
    (decls : List Solidity.StateVarDecl) : Bool :=
  let consts :=
    decls.filter (fun d => d.mutability == Solidity.VarMutability.constant)
  let names := consts.map Solidity.StateVarDecl.name
  let adj : List (Name × List Name) :=
    consts.map (fun d => (d.name, StateVarDecl.constantDeps names d))
  names.any (fun start => constantReachesSelf adj start)

def StateVarDecl.hasCompileTimeImmutableInit
    (_constantBindings : List (Name × Bool))
    (decl : Solidity.StateVarDecl) : Bool :=
  decl.mutability == Solidity.VarMutability.immutable &&
    match decl.init with
    | some init => exprIsRationalConstant init
    | none => false

def StateVarDecl.runtimeStateNameWith?
    (constantBindings : List (Name × Bool))
    (decl : Solidity.StateVarDecl) : Option Name :=
  if decl.mutability == Solidity.VarMutability.mutable ||
      decl.mutability == Solidity.VarMutability.transient ||
      (decl.mutability == Solidity.VarMutability.immutable &&
        !StateVarDecl.hasCompileTimeImmutableInit constantBindings decl) then
    some decl.name
  else
    none

def StateVarDecls.runtimeStateNamesWith
    (constantBindings : List (Name × Bool)) :
    List Solidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.runtimeStateNameWith? constantBindings decl with
      | some name =>
          name :: StateVarDecls.runtimeStateNamesWith constantBindings rest
      | none => StateVarDecls.runtimeStateNamesWith constantBindings rest

def checkTysAssignableWithReferenceLocations (types : TypeContext) :
    List Ty -> List Bool ->
    List (Option Solidity.DataLocation) ->
    List Ty -> List Bool ->
    List (Option Solidity.DataLocation) ->
    Except TypeError Unit
  | [], _, _, [], _, _ => Except.ok ()
  | actualTy :: actualRest, actualStorageRefs, actualLocations,
      expectedTy :: expectedRest, expectedStorageRefs,
      expectedLocations => do
      types.requireNoFixedPointAssignment actualTy expectedTy
      require (TypeContext.canImplicitlyConvert types actualTy expectedTy)
        (TypeError.expectedType expectedTy actualTy)
      let actualStorage := actualStorageRefs.head?.getD false
      let expectedStorage := expectedStorageRefs.head?.getD false
      let actualLocation := actualLocations.head?.join
      let expectedLocation := expectedLocations.head?.join
      require (!expectedStorage || actualStorage)
        (TypeError.invalidDataLocation expectedTy
          (some Solidity.DataLocation.storage))
      match expectedLocation with
      | some Solidity.DataLocation.calldata =>
          require
            (actualLocation ==
              some Solidity.DataLocation.calldata)
            (TypeError.invalidDataLocation expectedTy expectedLocation)
      | _ => Except.ok ()
      checkTysAssignableWithReferenceLocations types actualRest
        actualStorageRefs.tail actualLocations.tail expectedRest
        expectedStorageRefs.tail expectedLocations.tail
  | actual, _, _, expected, _, _ =>
      Except.error
        (TypeError.returnArityMismatch expected.length actual.length)

def checkReturnExprs (env : CheckEnv)
    (expr? : Option Solidity.Expr) : Except TypeError Unit :=
  match expr?, env.returnTys with
  | none, [] => Except.ok ()
  | none, expected =>
      -- G5: a bare `return;` is rejected whenever the function has a non-empty
      -- return-parameter list, even when every return is named (solc TypeError
      -- 6777 "Return arguments required.", TypeChecker.cpp:1138).
      Except.error (TypeError.returnArityMismatch expected.length 0)
  | some expr, [] =>
      if env.inModifier then
        -- A modifier has no `functionReturnParameters` (nullptr in solc), so
        -- ANY `return` carrying an expression is rejected — even a void-typed
        -- one like `return delete x;` or `return require(true);` (solc
        -- TypeError 7552 "Return arguments not allowed",
        -- TypeChecker::endVisit(Return), TypeChecker.cpp:1133-1146). This is
        -- distinct from a zero-return FUNCTION, whose empty-but-non-null
        -- return list still permits a void-typed return expression (handled
        -- by the branch below). A bare `return;` in a modifier stays allowed
        -- (the `none, []` case above).
        Except.error (TypeError.returnArityMismatch 0 1)
      else
      match expr with
      | Solidity.Expr.call
          (Solidity.Expr.ident "require")
          [ Solidity.Arg.positional cond
          , Solidity.Arg.positional
              (Solidity.Expr.call
                (Solidity.Expr.ident errorName) errorArgs) ] => do
          let condChecked ← checkExpr env cond
          condChecked.expectBool
          match checkCustomErrorArgs env errorName errorArgs with
          | Except.ok _ => Except.ok ()
          | Except.error err =>
              if env.errors.any (fun sig => sig.name == errorName) then
                Except.error err
              else do
                let checked ← checkExpr env expr
                requireEqTy (Solidity.Ty.tuple []) checked.ty
      | Solidity.Expr.unary Solidity.UnaryOp.delete _ => do
          let _ ← checkExpr env expr
          Except.ok ()
      | _ => do
          let checked ← checkExpr env expr
          requireEqTy (Solidity.Ty.tuple []) checked.ty
  | some expr@(Solidity.Expr.ternary _ _ _), [expected] =>
      checkExprAssignableToReferenceLocation env expr expected
        (returnStorageRefsSingle [expected] env.returnStorageRefs)
        (returnDataLocationSingle? [expected] env.returnDataLocations)
  | some (Solidity.Expr.ternary cond thenExpr elseExpr), _ => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      checkReturnExprs env (some thenExpr)
      checkReturnExprs env (some elseExpr)
  | some expr, [expected] =>
      checkExprAssignableToReferenceLocation env expr expected
        (returnStorageRefsSingle [expected] env.returnStorageRefs)
        (returnDataLocationSingle? [expected] env.returnDataLocations)
  | some (Solidity.Expr.tuple items), expected =>
      checkTupleItemValuesContextuallyAssignableToWithStorageRefs env items
        expected env.returnStorageRefs env.returnDataLocations
  | some expr, expected => do
      let checked ← checkExpr env expr
      match checked.ty with
      | Solidity.Ty.tuple actual =>
          require (sameLength actual expected)
            (TypeError.returnArityMismatch expected.length actual.length)
          checkTysAssignableWithReferenceLocations env.types actual
            checked.storageRefs checked.dataLocations expected
            env.returnStorageRefs env.returnDataLocations
      | _ =>
          Except.error (TypeError.returnArityMismatch expected.length 1)
termination_by sizeOf expr?
decreasing_by
  all_goals
    simp_wf
    unfold wfParam
    omega

def checkTysAssignableTo (types : TypeContext) :
    List Ty -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | actualTy :: actualRest, expectedTy :: expectedRest => do
      types.requireNoFixedPointAssignment actualTy expectedTy
      require (TypeContext.canImplicitlyConvert types actualTy expectedTy)
        (TypeError.expectedType expectedTy actualTy)
      checkTysAssignableTo types actualRest expectedRest
  | actual, expected =>
      Except.error (TypeError.returnArityMismatch
        expected.length actual.length)

def CheckedExpr.expectAssignableToTys (types : TypeContext)
    (checked : CheckedExpr) (expected : List Ty) :
    Except TypeError Unit :=
  match expected with
  | [] => requireEqTy (Solidity.Ty.tuple []) checked.ty
  | [ty] => checked.expectAssignableToIn types ty
  | tys =>
      match checked.ty with
      | Solidity.Ty.tuple actual =>
          checkTysAssignableTo types actual tys
      | _ => Except.error (TypeError.returnArityMismatch tys.length 1)

def Ty.isExternalFunction : Ty -> Bool
  | Solidity.Ty.functionWithLocations _ _ _ _ _
      Solidity.Visibility.external_ => true
  | _ => false

def isKnownContractCreationTryTarget (env : CheckEnv) :
    Solidity.Expr -> Bool
  | Solidity.Expr.newExpr
      (Solidity.Ty.user path) _ =>
      env.types.isContractPath path
  | Solidity.Expr.callWithOptions
      (Solidity.Expr.newExpr
        (Solidity.Ty.user path) _) _ _ =>
      env.types.isContractPath path
  | _ => false

def checkTryExternalMemberCallTarget (env : CheckEnv)
    (target : Solidity.Expr) (member : Name)
    (args : List Solidity.Arg) : Except TypeError Unit := do
  let targetChecked ← checkExpr env target
  match targetChecked.ty with
  | Solidity.Ty.user path =>
      require (env.types.isContractValuePath path)
        (TypeError.invalidTryCatch
          "try target is not a contract function value")
      let sig ←
        match checkArgs env args with
        | Except.ok checkedArgs =>
            let checkedInfos := checkedArgInfosFull args checkedArgs
            match env.types.resolveContractMemberFunctionChecked path member
                checkedInfos with
            | Except.ok sig => Except.ok sig
            | Except.error checkedErr =>
                match
                    checkContractMemberCallArgsContextualForPath
                      env path member args with
                | Except.ok (sig, _) => Except.ok sig
                | Except.error _ => Except.error checkedErr
        | Except.error argErr =>
            match
                checkContractMemberCallArgsContextualForPath
                  env path member args with
            | Except.ok (sig, _) => Except.ok sig
            | Except.error _ => Except.error argErr
      require sig.externallyCallable
        (TypeError.invalidTryCatch
          "try target is not an external function call")
  | _ =>
      Except.error
        (TypeError.invalidTryCatch
          "try target is not an external function call")

def checkTryTargetKind (env : CheckEnv)
    (expr : Solidity.Expr) : Except TypeError Unit :=
  match expr with
  | Solidity.Expr.call
      (Solidity.Expr.member target member) args =>
      checkTryExternalMemberCallTarget env target member args
  | Solidity.Expr.callWithOptions
      (Solidity.Expr.member target member) _ args =>
      checkTryExternalMemberCallTarget env target member args
  | Solidity.Expr.call
      (Solidity.Expr.ident name) _ =>
      match env.lookupVar? name with
      | some ty =>
          require ty.isExternalFunction
            (TypeError.invalidTryCatch
              "try target is not an external function call")
      | none =>
          Except.error
            (TypeError.invalidTryCatch
              "try target is not an external function call")
  | Solidity.Expr.call fn _ => do
      let fnChecked ← checkExpr env fn
      require fnChecked.ty.isExternalFunction
        (TypeError.invalidTryCatch
          "try target is not an external function call")
  | Solidity.Expr.callWithOptions fn _ _ => do
      if isKnownContractCreationTryTarget env expr then
        Except.ok ()
      else
        let fnChecked ← checkExpr env fn
        require fnChecked.ty.isExternalFunction
          (TypeError.invalidTryCatch
            "try target is not an external function call")
  | _ =>
      require (isKnownContractCreationTryTarget env expr)
        (TypeError.invalidTryCatch
          "try target is not an external call or contract creation")

def checkTryTarget (env : CheckEnv)
    (expr : Solidity.Expr) : Except TypeError CheckedExpr := do
  checkTryTargetKind env expr
  checkExpr env expr

def checkEventEmission (env : CheckEnv)
    (expr : Solidity.Expr) : Except TypeError Unit :=
  match expr with
  | Solidity.Expr.call (Solidity.Expr.ident name) args => do
      checkEventArgs env name args
  -- G7: a qualified `emit A.E(...)` must still resolve its member to an event;
  -- solc rejects a non-event member callee with TypeError 9292 ("Expression has
  -- to be an event invocation"). Resolve the member name against in-scope events
  -- (inherited events are flattened into `env.events`).
  | Solidity.Expr.call (Solidity.Expr.member _ name) args => do
      checkEventArgs env name args
  | other =>
      Except.error
        (TypeError.unsupported "emit target is not an event invocation")

def checkRevertCall (env : CheckEnv)
    (expr : Solidity.Expr) : Except TypeError Unit :=
  match expr with
  | Solidity.Expr.call (Solidity.Expr.ident "revert") _ => do
      let _ ← checkExpr env expr
      Except.ok ()
  | Solidity.Expr.call (Solidity.Expr.ident name) args => do
      checkCustomErrorArgs env name args
  | other => do
      let _ ← checkExpr env other
      Except.ok ()

def VarBinding.checkType (env : CheckEnv)
    (binding : Solidity.VarBinding) :
    Except TypeError Ty :=
  match binding.ty, binding.name with
  | some ty, _ => do
      checkLocationForTy env.types ty binding.location
      Except.ok (env.qualifyCurrentLocalUserTypes ty)
  | none, some name => Except.error (TypeError.missingTypeAnnotation name)
  | none, none => Except.error (TypeError.unsupported "anonymous untyped binding")

def VarBinding.isAnonymousUntyped
    (binding : Solidity.VarBinding) : Bool :=
  binding.ty.isNone && binding.name.isNone

def VarBinding.namedType? (env : CheckEnv)
    (binding : Solidity.VarBinding) :
    Except TypeError (Option (Name × Ty)) := do
  if VarBinding.isAnonymousUntyped binding then
    Except.ok none
  else
    let ty ← VarBinding.checkType env binding
    match binding.name with
    | some name => Except.ok (some (name, ty))
    | none => Except.ok none

def VarBinding.isStorageRef (types : TypeContext)
    (binding : Solidity.VarBinding) : Bool :=
  match binding.ty with
  | some ty =>
      Ty.needsDataLocation types ty &&
        binding.location == some Solidity.DataLocation.storage
  | none => false

def VarBinding.namedTypeStorageRef? (env : CheckEnv)
    (binding : Solidity.VarBinding) :
    Except TypeError (Option (Name × Ty × Bool)) := do
  if VarBinding.isAnonymousUntyped binding then
    Except.ok none
  else
    let ty ← VarBinding.checkType env binding
    match binding.name with
    | some name =>
        Except.ok
          (some (name, ty, VarBinding.isStorageRef env.types binding))
    | none => Except.ok none

def VarBinding.namedDataLocation? (env : CheckEnv)
    (binding : Solidity.VarBinding) :
    Except TypeError (Option (Name × Solidity.DataLocation)) := do
  if VarBinding.isAnonymousUntyped binding then
    Except.ok none
  else
    let ty ← VarBinding.checkType env binding
    match binding.name, binding.location with
    | some name, some location =>
        if Ty.needsDataLocation env.types ty then
          Except.ok (some (name, location))
        else
          Except.ok none
    | _, _ => Except.ok none

def VarBinding.checkStorageRefInitializer (env : CheckEnv)
    (binding : Solidity.VarBinding) (checked : CheckedExpr) :
    Except TypeError Unit := do
  let ty ← VarBinding.checkType env binding
  if VarBinding.isStorageRef env.types binding then
    checked.expectAssignableToIn env.types ty
    require checked.stateLValue
      (TypeError.invalidDataLocation ty binding.location)
  else if binding.location ==
      some Solidity.DataLocation.calldata then
    checked.expectLocationAssignableTo ty binding.location
  else
    Except.ok ()

def VarBindings.namedTypes (env : CheckEnv) :
    List Solidity.VarBinding ->
    Except TypeError (List (Name × Ty))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedType? env binding
      let tail ← VarBindings.namedTypes env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.namedTypeStorageRefs (env : CheckEnv) :
    List Solidity.VarBinding ->
    Except TypeError (List (Name × Ty × Bool))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedTypeStorageRef? env binding
      let tail ← VarBindings.namedTypeStorageRefs env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.namedDataLocations (env : CheckEnv) :
    List Solidity.VarBinding ->
    Except TypeError (List (Name × Solidity.DataLocation))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedDataLocation? env binding
      let tail ← VarBindings.namedDataLocations env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.anyStorageRef (types : TypeContext) :
    List Solidity.VarBinding -> Bool
  | [] => false
  | binding :: rest =>
      VarBinding.isStorageRef types binding ||
        VarBindings.anyStorageRef types rest

def VarBindings.anyAnonymousUntyped :
    List Solidity.VarBinding -> Bool
  | [] => false
  | binding :: rest =>
      VarBinding.isAnonymousUntyped binding ||
        VarBindings.anyAnonymousUntyped rest

def VarBindings.ensureAnonymousUntypedAllowed
    (bindings : List Solidity.VarBinding)
    (init? : Option Solidity.Expr) :
    Except TypeError Unit := do
  if VarBindings.anyAnonymousUntyped bindings then do
    require (bindings.length > 1)
      (TypeError.unsupported "anonymous untyped binding")
    match init? with
    | some _ => Except.ok ()
    | none =>
        Except.error (TypeError.unsupported "anonymous untyped binding")
  else
    Except.ok ()

def checkVarBindingsAssignableToTys (env : CheckEnv) :
    List Solidity.VarBinding -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | binding :: bindingRest, actualTy :: actualRest => do
      if VarBinding.isAnonymousUntyped binding then
        checkVarBindingsAssignableToTys env bindingRest actualRest
      else
        let expectedTy ← VarBinding.checkType env binding
        env.types.requireNoFixedPointAssignment actualTy expectedTy
        require (TypeContext.canImplicitlyConvert env.types actualTy expectedTy)
          (TypeError.expectedType expectedTy actualTy)
        checkVarBindingsAssignableToTys env bindingRest actualRest
  | expected, actual =>
      Except.error
        (TypeError.returnArityMismatch expected.length actual.length)

def checkVarBindingsAssignableToTysWithStorageRefs (env : CheckEnv) :
    List Solidity.VarBinding -> List Ty -> List Bool ->
    List (Option Solidity.DataLocation) ->
    Except TypeError Unit
  | [], [], _, _ => Except.ok ()
  | binding :: bindingRest, actualTy :: actualRest, storageRefs,
      locations => do
      if VarBinding.isAnonymousUntyped binding then
        checkVarBindingsAssignableToTysWithStorageRefs env bindingRest
          actualRest storageRefs.tail locations.tail
      else
        let expectedTy ← VarBinding.checkType env binding
        env.types.requireNoFixedPointAssignment actualTy expectedTy
        require (TypeContext.canImplicitlyConvert env.types actualTy expectedTy)
          (TypeError.expectedType expectedTy actualTy)
        require
          (!VarBinding.isStorageRef env.types binding ||
            storageRefs.head?.getD false)
          (TypeError.invalidDataLocation expectedTy binding.location)
        if binding.location ==
            some Solidity.DataLocation.calldata then
          require
            (locations.head?.join ==
              some Solidity.DataLocation.calldata)
            (TypeError.invalidDataLocation expectedTy binding.location)
        else
          Except.ok ()
        checkVarBindingsAssignableToTysWithStorageRefs env bindingRest
          actualRest storageRefs.tail locations.tail
  | expected, actual, _, _ =>
      Except.error
        (TypeError.returnArityMismatch expected.length actual.length)

def checkVarBindingsAssignableToChecked (env : CheckEnv)
    (bindings : List Solidity.VarBinding)
    (checked : CheckedExpr) : Except TypeError Unit :=
  match checked.ty with
  | Solidity.Ty.tuple actual =>
      checkVarBindingsAssignableToTysWithStorageRefs env bindings actual
        checked.storageRefs checked.dataLocations
  | _ =>
      Except.error
        (TypeError.returnArityMismatch bindings.length 1)

def checkVarBindingTupleItemsAssignableTo (env : CheckEnv) :
    List Solidity.VarBinding ->
    List Solidity.TupleItem -> Except TypeError Unit
  | [], [] => Except.ok ()
  | binding :: bindingRest,
      Solidity.TupleItem.value expr :: itemRest => do
      if VarBinding.isAnonymousUntyped binding then
        checkVarBindingTupleItemsAssignableTo env bindingRest itemRest
      else
        let expectedTy ← VarBinding.checkType env binding
        checkExprAssignableTo env expr expectedTy
        checkVarBindingTupleItemsAssignableTo env bindingRest itemRest
  | _ :: _, Solidity.TupleItem.hole :: _ =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | expected, actual =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)

def VarBindings.checkStorageRefTupleInitializers (env : CheckEnv) :
    List Solidity.VarBinding ->
    List Solidity.TupleItem -> Except TypeError Unit
  | [], [] => Except.ok ()
  | binding :: bindingRest,
      Solidity.TupleItem.value expr :: itemRest => do
      if VarBinding.isAnonymousUntyped binding then
        Except.ok ()
      else
        let checked ← checkExpr env expr
        VarBinding.checkStorageRefInitializer env binding checked
      VarBindings.checkStorageRefTupleInitializers env bindingRest itemRest
  | binding :: _, Solidity.TupleItem.hole :: _ => do
      if VarBinding.isStorageRef env.types binding then
        Except.error (TypeError.invalidDataLocation
          (binding.ty.getD (Solidity.Ty.tuple []))
          binding.location)
      else
        Except.error (TypeError.unsupported "tuple hole in value position")
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)

def VarBindings.tys (env : CheckEnv) :
    List Solidity.VarBinding -> Except TypeError (List Ty)
  | [] => Except.ok []
  | binding :: rest => do
      let ty ← VarBinding.checkType env binding
      let tail ← VarBindings.tys env rest
      Except.ok (ty :: tail)

def Parameter.isStringMemory (param : Solidity.Parameter) : Bool :=
  param.ty == Solidity.Ty.string &&
    param.location == some Solidity.DataLocation.memory

def Parameter.isBytesMemory (param : Solidity.Parameter) : Bool :=
  param.ty == Solidity.Ty.bytes &&
    param.location == some Solidity.DataLocation.memory

def Parameter.isBytesCalldata (param : Solidity.Parameter) : Bool :=
  param.ty == Solidity.Ty.bytes &&
    param.location == some Solidity.DataLocation.calldata

def Parameter.isPanicCode (param : Solidity.Parameter) : Bool :=
  param.ty == Solidity.Ty.uint 256 && param.location.isNone

def Parameter.checkTryReturnParam (types : TypeContext)
    (param : Solidity.Parameter) : Except TypeError Unit := do
  checkTy types param.ty
  require (!Ty.containsLibraryType types 64 param.ty)
    (TypeError.invalidType param.ty)
  if Ty.needsDataLocation types param.ty then
    require (param.location ==
        some Solidity.DataLocation.memory)
      (TypeError.invalidDataLocation param.ty param.location)
  else
    require param.location.isNone
      (TypeError.invalidDataLocation param.ty param.location)
  require (!Ty.containsMapping types 64 param.ty)
    (TypeError.invalidDataLocation param.ty param.location)

def Parameters.checkTryReturnParams (types : TypeContext) :
    List Solidity.Parameter -> Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      Parameter.checkTryReturnParam types param
      Parameters.checkTryReturnParams types rest

def checkCatchClauseHeader (env : CheckEnv)
    (name? : Option Name) (params : List Solidity.Parameter) :
    Except TypeError Unit := do
  Parameters.check env.types params
  match name?, params with
  | some "Error", [param] =>
      require (Parameter.isStringMemory param)
        (TypeError.invalidTryCatch
          "catch Error expects string memory")
  | some "Panic", [param] =>
      require (Parameter.isPanicCode param)
        (TypeError.invalidTryCatch "catch Panic expects uint256")
  | some _, _ =>
      Except.error
        (TypeError.invalidTryCatch
          "catch name is not Error or Panic")
  | none, [] => Except.ok ()
  | none, [param] =>
      require (Parameter.isBytesMemory param)
        (TypeError.invalidTryCatch
          "unnamed catch parameter expects bytes memory")
  | none, _ =>
      Except.error
        (TypeError.invalidTryCatch
          "unnamed catch expects zero parameters or bytes memory")

inductive CatchKind where
  | error
  | panic
  | lowLevel
  deriving BEq, Repr

def CatchKind.label : CatchKind -> String
  | CatchKind.error => "Error"
  | CatchKind.panic => "Panic"
  | CatchKind.lowLevel => "low-level"

def catchClauseKind? :
    Solidity.CatchClause -> Option CatchKind
  | Solidity.CatchClause.clause (some "Error") _ _ =>
      some CatchKind.error
  | Solidity.CatchClause.clause (some "Panic") _ _ =>
      some CatchKind.panic
  | Solidity.CatchClause.clause none _ _ =>
      some CatchKind.lowLevel
  | _ => none

def checkCatchClauseKindsUniqueFrom (seen : List CatchKind) :
    List Solidity.CatchClause -> Except TypeError Unit
  | [] => Except.ok ()
  | clause :: rest =>
      match catchClauseKind? clause with
      | some kind => do
          require (!seen.contains kind)
            (TypeError.invalidTryCatch
              ("duplicate " ++ kind.label ++ " catch clause"))
          checkCatchClauseKindsUniqueFrom (kind :: seen) rest
      | none => checkCatchClauseKindsUniqueFrom seen rest

def checkCatchClauseKindsUnique :
    List Solidity.CatchClause -> Except TypeError Unit :=
  checkCatchClauseKindsUniqueFrom []

def requireCatchClausesNonempty
    (clauses : List Solidity.CatchClause) :
    Except TypeError Unit :=
  require (!clauses.isEmpty)
    (TypeError.invalidTryCatch "try statement requires a catch clause")

structure CheckedStmt where
  source : Solidity.Stmt
  deriving Repr

mutual

def checkStmt (env : CheckEnv) :
    Solidity.Stmt -> Except TypeError CheckedStmt
  | stmt@Solidity.Stmt.empty => Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.block body) => do
      let _ ← checkStmtSeq { env with blockScopeNames := [] } body
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.varDecl bindings init?) => do
      VarBindings.ensureAnonymousUntypedAllowed bindings init?
      let named ← VarBindings.namedTypes env bindings
      ensureUniqueNames "local" (named.map Prod.fst)
      match init? with
      | none => Except.ok ()
      | some init =>
          match bindings with
          | [binding] =>
              let ty ← VarBinding.checkType env binding
              match checkInternalFunctionValueAssignable? env init ty with
              | some result => result
              | none => do
                  checkExprAssignableTo env init ty
                  let checked ← checkExpr env init
                  VarBinding.checkStorageRefInitializer env binding checked
          | _ =>
              match init with
              | Solidity.Expr.tuple items => do
                  checkVarBindingTupleItemsAssignableTo env bindings items
                  VarBindings.checkStorageRefTupleInitializers env bindings
                    items
              | _ =>
                  let checked ← checkExpr env init
                  checkVarBindingsAssignableToChecked env bindings checked
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.expr
      (Solidity.Expr.call
        (Solidity.Expr.ident "require")
        [ Solidity.Arg.positional cond
        , Solidity.Arg.positional
            (Solidity.Expr.call
              (Solidity.Expr.ident errorName) errorArgs) ])) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      match checkCustomErrorArgs env errorName errorArgs with
      | Except.ok _ => Except.ok { source := stmt }
      | Except.error err =>
          if env.errors.any (fun sig => sig.name == errorName) then
            Except.error err
          else
            let _ ← checkExpr env
              (Solidity.Expr.call
                (Solidity.Expr.ident "require")
                [ Solidity.Arg.positional cond
                , Solidity.Arg.positional
                    (Solidity.Expr.call
                      (Solidity.Expr.ident errorName)
                      errorArgs) ])
            Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.expr expr) => do
      let _ ← checkExpr env expr
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.ifElse cond thenBranch elseBranch?) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let _ ← checkStmt env thenBranch
      match elseBranch? with
      | some elseBranch => let _ ← checkStmt env elseBranch; Except.ok ()
      | none => Except.ok ()
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.whileLoop cond body) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let _ ← checkStmt env.enterLoop body
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.doWhile body cond) => do
      let _ ← checkStmt env.enterLoop body
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.forLoop init? cond? post? body) => do
      let loopEnv ←
        match init? with
        | none => Except.ok env
        | some initStmt =>
            match initStmt with
            | Solidity.Stmt.varDecl bindings _ => do
                let _ ← checkStmt env initStmt
                let named ← VarBindings.namedTypeStorageRefs env bindings
                let dataLocations ← VarBindings.namedDataLocations env bindings
                Except.ok
                  ((env.extendVarsWithStorageRefs named).extendDataLocations
                    dataLocations)
            | _ => let _ ← checkStmt env initStmt; Except.ok env
      match cond? with
      | some cond =>
          let condChecked ← checkExpr loopEnv cond
          condChecked.expectBool
      | none => Except.ok ()
      match post? with
      | some post => let _ ← checkExpr loopEnv post; Except.ok ()
      | none => Except.ok ()
      let _ ← checkStmt loopEnv.enterLoop body
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.tryCatch expr clauses) => do
      let _ ← checkTryTarget env expr
      requireCatchClausesNonempty clauses
      checkCatchClauseKindsUnique clauses
      let _ ← checkCatchClauses env clauses
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.tryCatchReturns expr returns success clauses) => do
      Parameters.checkTryReturnParams env.types returns
      ensureUniqueNames "try return"
        ((Parameters.namedTypes returns).map Prod.fst)
      let checked ← checkTryTarget env expr
      checked.expectAssignableToTys env.types (Parameters.tys returns)
      let successEnv :=
        (env.extendVarsWithStorageRefs
        (Parameters.namedTypeStorageRefs env.types returns)).extendDataLocations
          (Parameters.namedDataLocations env.types returns)
      let _ ← checkStmt successEnv success
      requireCatchClausesNonempty clauses
      checkCatchClauseKindsUnique clauses
      let _ ← checkCatchClauses env clauses
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.emitEvent expr) => do
      requireLogOrCreateAllowed env
        "event emission in view or pure function"
      checkEventEmission env expr
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.revertCall expr) => do
      checkRevertCall env expr
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.returnValues expr?) => do
      checkReturnExprs env expr?
      Except.ok { source := stmt }
  | stmt@Solidity.Stmt.break => do
      require (env.loopDepth > 0) TypeError.breakOutsideLoop
      Except.ok { source := stmt }
  | stmt@Solidity.Stmt.continue => do
      require (env.loopDepth > 0) TypeError.continueOutsideLoop
      Except.ok { source := stmt }
  | stmt@(Solidity.Stmt.unchecked body) => do
      require (!env.inUnchecked) (TypeError.unsupported
        "nested unchecked block")
      let _ ← checkStmt env.enterUnchecked body
      Except.ok { source := stmt }
  | Solidity.Stmt.inlineAssembly _ =>
      Except.error (TypeError.unsupported "inline assembly")
  | stmt@Solidity.Stmt.modifierPlaceholder => do
      require env.inModifier TypeError.modifierPlaceholderOutsideModifier
      require (!env.inUnchecked) (TypeError.unsupported
        "modifier placeholder in unchecked block")
      Except.ok { source := stmt }

def checkStmtSeq (env : CheckEnv) :
    List Solidity.Stmt -> Except TypeError CheckEnv
  | [] => Except.ok env
  | stmt :: rest => do
      let declaredNames ←
        match stmt with
        | Solidity.Stmt.varDecl bindings _ => do
            let named ← VarBindings.namedTypes env bindings
            let names := named.map Prod.fst
            ensureNamesDisjointFrom "local" env.blockScopeNames names
            Except.ok names
        | _ => Except.ok []
      let _ ← checkStmt env stmt
      let nextEnv ←
        match stmt with
        | Solidity.Stmt.varDecl bindings _ => do
            let named ← VarBindings.namedTypeStorageRefs env bindings
            let dataLocations ← VarBindings.namedDataLocations env bindings
            Except.ok
              { ((env.extendVarsWithStorageRefs named).extendDataLocations
                  dataLocations) with
                blockScopeNames := declaredNames ++ env.blockScopeNames }
        | _ => Except.ok env
      checkStmtSeq nextEnv rest

def checkCatchClause (env : CheckEnv) :
    Solidity.CatchClause -> Except TypeError Unit
  | Solidity.CatchClause.clause name? params body => do
      checkCatchClauseHeader env name? params
      let clauseEnv :=
        (env.extendVarsWithStorageRefs
          (Parameters.namedTypeStorageRefs env.types params)).extendDataLocations
          (Parameters.namedDataLocations env.types params)
      let _ ← checkStmt clauseEnv body
      Except.ok ()

def checkCatchClauses (env : CheckEnv) :
    List Solidity.CatchClause -> Except TypeError Unit
  | [] => Except.ok ()
  | clause :: rest => do
      checkCatchClause env clause
      checkCatchClauses env rest

end

def StateVarDecl.check (env : CheckEnv)
    (decl : Solidity.StateVarDecl) : Except TypeError Unit := do
  let declTy := env.qualifyCurrentLocalUserTypes decl.ty
  checkTy env.types declTy
  require (!Ty.containsLibraryType env.types 64 declTy)
    (TypeError.invalidType declTy)
  require (!(decl.visibility == some Solidity.Visibility.external_))
    (TypeError.invalidVariableDecl "state variable is external")
  if decl.visibility == some Solidity.Visibility.public_ then
    env.types.requireNoFixedPointValue declTy
      "public state-variable getter for"
    let getterShape ←
      match Ty.publicGetterShape? env.types 64 declTy with
      | some shape => Except.ok shape
      | none => Except.error (TypeError.invalidType declTy)
    -- solc error 5359: a struct getter with all members omitted returns no
    -- values, so the getter cannot exist. `getterShape.snd` (the returned
    -- members) is empty exactly in that case.
    require (!getterShape.snd.isEmpty)
      (TypeError.invalidType declTy)
    -- solc error 6744 ("Internal or recursive type"): now that struct-getter
    -- omission is SHALLOW, a nested struct member is returned WHOLE. If any
    -- returned member transitively contains a mapping, the getter has no valid
    -- external interface type. `Ty.containsMapping` walks nested structs.
    require (!Tys.containsMapping env.types 64 getterShape.snd)
      (TypeError.invalidType declTy)
    match Tys.firstNonAbiEncodable? env.types getterShape.fst with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Tys.firstNonAbiEncodable? env.types getterShape.snd with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Tys.firstAbiCoderV2Only? env.types getterShape.fst with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Tys.firstAbiCoderV2Only? env.types getterShape.snd with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
  else
    Except.ok ()
  if decl.mutability == Solidity.VarMutability.constant then
    require (env.types.isConstantStateVarTypeShape declTy)
      (TypeError.invalidVariableDecl
        "constant variable has unsupported type")
    require decl.init.isSome
      (TypeError.invalidVariableDecl "constant variable has no initializer")
    match decl.init with
    | some init =>
        require (Expr.isCompileTimeConstant env init)
          (TypeError.invalidVariableDecl
            "constant variable initializer is not compile-time constant")
    | none => Except.ok ()
  else if decl.mutability == Solidity.VarMutability.immutable then
    require (env.types.isImmutableStateVarTypeShape declTy)
      (TypeError.invalidVariableDecl
        "immutable variable has unsupported type")
  else if decl.mutability == Solidity.VarMutability.transient then
    requireCancunOrLater env "transient storage"
    require (env.types.isValueTypeShape declTy)
      (TypeError.invalidVariableDecl
        "transient variable has unsupported type")
    require decl.init.isNone
      (TypeError.invalidVariableDecl
        "transient variable has an initializer")
  else
    Except.ok ()
  match decl.init with
  | none => Except.ok ()
  | some init => checkExprAssignableTo env init declTy

def StateVarDecl.checkFileLevelConstant (env : CheckEnv)
    (decl : Solidity.StateVarDecl) : Except TypeError Unit := do
  require (decl.mutability == Solidity.VarMutability.constant)
    (TypeError.invalidVariableDecl
      "only constant variables are allowed at file level")
  require decl.visibility.isNone
    (TypeError.invalidVariableDecl
      "file-level constant has visibility")
  require decl.override?.isNone
    (TypeError.invalidVariableDecl
      "file-level constant has override")
  StateVarDecl.check env decl

def StateVarDecl.namedType (decl : Solidity.StateVarDecl) :
    Name × Ty :=
  (decl.name, decl.ty)

def StateVarDecl.namedConstness (decl : Solidity.StateVarDecl) :
    Name × Bool :=
  (decl.name, decl.mutability == Solidity.VarMutability.constant)

def StateVarDecl.isRuntimeStateRead
    (decl : Solidity.StateVarDecl) : Bool :=
  decl.mutability == Solidity.VarMutability.mutable ||
    decl.mutability == Solidity.VarMutability.transient

def StateVarDecl.immutableName? (decl : Solidity.StateVarDecl) :
    Option Name :=
  if decl.mutability == Solidity.VarMutability.immutable then
    some decl.name
  else
    none

def StateVarDecl.runtimeStateName? (decl : Solidity.StateVarDecl) :
    Option Name :=
  if StateVarDecl.isRuntimeStateRead decl then some decl.name else none

def StateVarDecls.namedTypes :
    List Solidity.StateVarDecl -> List (Name × Ty)
  | [] => []
  | decl :: rest => StateVarDecl.namedType decl :: StateVarDecls.namedTypes rest

def StateVarDecl.namedTypeQualifiedLocalTypes
    (contractName : Name) (localTypeNames : List Name)
    (decl : Solidity.StateVarDecl) : Name × Ty :=
  (decl.name,
    Ty.qualifyLocalUserTypes contractName localTypeNames decl.ty)

def StateVarDecls.namedTypesQualifiedLocalTypes
    (contractName : Name) (localTypeNames : List Name) :
    List Solidity.StateVarDecl -> List (Name × Ty)
  | [] => []
  | decl :: rest =>
      StateVarDecl.namedTypeQualifiedLocalTypes
        contractName localTypeNames decl ::
        StateVarDecls.namedTypesQualifiedLocalTypes
          contractName localTypeNames rest

def StateVarDecls.namedConstness :
    List Solidity.StateVarDecl -> List (Name × Bool)
  | [] => []
  | decl :: rest =>
      StateVarDecl.namedConstness decl :: StateVarDecls.namedConstness rest

def StateVarDecls.runtimeStateNames :
    List Solidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.runtimeStateName? decl with
      | some name => name :: StateVarDecls.runtimeStateNames rest
      | none => StateVarDecls.runtimeStateNames rest

def StateVarDecls.immutableNames :
    List Solidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.immutableName? decl with
      | some name => name :: StateVarDecls.immutableNames rest
      | none => StateVarDecls.immutableNames rest

def StateVarDecl.visibleToDerived
    (decl : Solidity.StateVarDecl) : Bool :=
  !(decl.visibility == some Solidity.Visibility.private_)

def ContractItem.visibleStateVarName? :
    Solidity.ContractItem -> Option Name
  | Solidity.ContractItem.stateVar decl =>
      if StateVarDecl.visibleToDerived decl then some decl.name else none
  | _ => none

def ContractItem.visibleStateVar? :
    Solidity.ContractItem ->
    Option Solidity.StateVarDecl
  | Solidity.ContractItem.stateVar decl =>
      if StateVarDecl.visibleToDerived decl then some decl else none
  | _ => none

def ContractDecl.visibleStateVarNames
    (decl : Solidity.ContractDecl) : List Name :=
  decl.items.filterMap ContractItem.visibleStateVarName?

def ContractDecl.visibleStateVars
    (decl : Solidity.ContractDecl) :
    List Solidity.StateVarDecl :=
  decl.items.filterMap ContractItem.visibleStateVar?

def ContractDecls.visibleStateVarNames (types : TypeContext) :
    List Path -> List Name
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.visibleStateVarNames decl ++
            ContractDecls.visibleStateVarNames types rest
      | none => ContractDecls.visibleStateVarNames types rest

def ContractDecls.visibleStateVars (types : TypeContext) :
    List Path -> List Solidity.StateVarDecl
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.visibleStateVars decl ++
            ContractDecls.visibleStateVars types rest
      | none => ContractDecls.visibleStateVars types rest

def StateVarDecls.checkNoInheritedShadowing
    (inheritedNames : List Name) :
    List Solidity.StateVarDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | decl :: rest => do
      require
        (!Solidity.Executable.nameIn decl.name inheritedNames)
        (TypeError.invalidContractHeader
          "state variable shadows inherited state variable")
      StateVarDecls.checkNoInheritedShadowing inheritedNames rest

def checkNoInheritedStateNameClashes
    (inheritedNames : List Name) :
    List Name -> Except TypeError Unit
  | [] => Except.ok ()
  | name :: rest => do
      require
        (!Solidity.Executable.nameIn name inheritedNames)
        (TypeError.invalidContractHeader
          "declaration shadows inherited state variable")
      checkNoInheritedStateNameClashes inheritedNames rest

def checkNoInheritedNamedDeclarationClashes
    (message : String) (inheritedNames : List Name) :
    List Name -> Except TypeError Unit
  | [] => Except.ok ()
  | name :: rest => do
      require
        (!Solidity.Executable.nameIn name inheritedNames)
        (TypeError.invalidContractHeader message)
      checkNoInheritedNamedDeclarationClashes message inheritedNames rest

structure OverrideMember where
  origin : Path
  originKind : Solidity.ContractKind
  fromStateVar : Bool := false
  name : Name
  params : List Ty := []
  paramDataLocations :
    List (Option Solidity.DataLocation) := []
  returns : List Ty := []
  returnDataLocations :
    List (Option Solidity.DataLocation) := []
  visibility : Option Solidity.Visibility := none
  mutability : Solidity.StateMutability :=
    Solidity.StateMutability.nonpayable
  virtual : Bool := false
  implemented : Bool := true
  deriving Repr

def OverrideMember.sameKey (a b : OverrideMember) : Bool :=
  a.name == b.name && a.params == b.params

def OverrideMember.sameOriginKey (a b : OverrideMember) : Bool :=
  a.origin == b.origin && OverrideMember.sameKey a b

def OverrideMember.matchesKey (member : OverrideMember)
    (name : Name) (params : List Ty) : Bool :=
  member.name == name && member.params == params

def overrideVisibilityAllowed
    (base actual : Option Solidity.Visibility) : Bool :=
  if base == actual then
    true
  else
    base == some Solidity.Visibility.external_ &&
      actual == some Solidity.Visibility.public_

def overrideMutabilityAllowed
    (base actual : Solidity.StateMutability) : Bool :=
  match base with
  | Solidity.StateMutability.pure =>
      actual == Solidity.StateMutability.pure
  | Solidity.StateMutability.view =>
      actual == Solidity.StateMutability.view ||
        actual == Solidity.StateMutability.pure
  | Solidity.StateMutability.nonpayable =>
      actual == Solidity.StateMutability.nonpayable ||
        actual == Solidity.StateMutability.view ||
        actual == Solidity.StateMutability.pure
  | Solidity.StateMutability.payable =>
      actual == Solidity.StateMutability.payable

namespace OverrideMembers

def containsKey (name : Name) (params : List Ty) :
    List OverrideMember -> Bool
  | [] => false
  | member :: rest =>
      member.matchesKey name params || containsKey name params rest

def containsSameOriginKey (target : OverrideMember) :
    List OverrideMember -> Bool
  | [] => false
  | member :: rest =>
      OverrideMember.sameOriginKey target member ||
        containsSameOriginKey target rest

def addIfNewKey (members : List OverrideMember)
    (member : OverrideMember) : List OverrideMember :=
  if containsKey member.name member.params members then
    members
  else
    members ++ [member]

def addAllIfNewKey (members : List OverrideMember) :
    List OverrideMember -> List OverrideMember
  | [] => members
  | member :: rest =>
      addAllIfNewKey (addIfNewKey members member) rest

def dedupOriginKeys : List OverrideMember -> List OverrideMember
  | [] => []
  | member :: rest =>
      if containsSameOriginKey member rest then
        dedupOriginKeys rest
      else
        member :: dedupOriginKeys rest

def matchingKey (target : OverrideMember) :
    List OverrideMember -> List OverrideMember
  | [] => []
  | member :: rest =>
      if OverrideMember.sameKey target member then
        member :: matchingKey target rest
      else
        matchingKey target rest

def hasNonStateMemberNamed (name : Name) : List OverrideMember -> Bool
  | [] => false
  | member :: rest =>
      (!member.fromStateVar && member.name == name) ||
        hasNonStateMemberNamed name rest

def nonStateNames : List OverrideMember -> List Name
  | [] => []
  | member :: rest =>
      if member.fromStateVar then
        nonStateNames rest
      else
        member.name :: nonStateNames rest

def originPaths : List OverrideMember -> List Path
  | [] => []
  | member :: rest => member.origin :: originPaths rest

def checkOverridable : List OverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | member :: rest => do
      require member.virtual
        (TypeError.invalidOverride
          "base member is not virtual or is a public state-variable getter")
      checkOverridable rest

def checkCompatible (current : OverrideMember) :
    List OverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | base :: rest => do
      require (current.returns == base.returns)
        (TypeError.invalidOverride "override return types do not match")
      if base.visibility == some Solidity.Visibility.external_ then
        Except.ok ()
      else
        require (current.paramDataLocations == base.paramDataLocations)
          (TypeError.invalidOverride
            "override parameter data locations do not match")
        require (current.returnDataLocations == base.returnDataLocations)
          (TypeError.invalidOverride
            "override return data locations do not match")
      require (overrideVisibilityAllowed base.visibility current.visibility)
        (TypeError.invalidOverride "override visibility is incompatible")
      require (overrideMutabilityAllowed base.mutability current.mutability)
        (TypeError.invalidOverride "override mutability is incompatible")
      checkCompatible current rest

end OverrideMembers

def pathAllIn (targets allowed : List Path) : Bool :=
  match targets with
  | [] => true
  | path :: rest =>
      TypeContext.pathIn path allowed && pathAllIn rest allowed

def pathSetsEqual (left right : List Path) : Bool :=
  pathAllIn left right && pathAllIn right left

/-- solc `OverrideChecker.cpp:850-879` (`checkOverrideList`, error 4520) rejects a
duplicate contract in an `override(...)` list, e.g. `override(A, A)`. -/
def pathListHasDuplicate : List Path -> Bool
  | [] => false
  | path :: rest =>
      TypeContext.pathIn path rest || pathListHasDuplicate rest

def StateVarDecl.publicGetterOverrideMember? (types : TypeContext)
    (contractName : Name) (localTypeNames : List Name)
    (origin : Path) (originKind : Solidity.ContractKind)
    (decl : Solidity.StateVarDecl) : Option OverrideMember :=
  match decl.visibility with
  | some Solidity.Visibility.public_ => do
      let declTy :=
        Ty.qualifyLocalUserTypes contractName localTypeNames decl.ty
      let shape ← Ty.publicGetterShape? types 64 declTy
      some
        { origin := origin
          originKind := originKind
          fromStateVar := true
          name := decl.name
          params := shape.fst
          returns := shape.snd
          visibility := some Solidity.Visibility.external_
          mutability := Solidity.StateMutability.view
          virtual := false
          implemented := true }
  | _ => none

def receiveOverrideName : Name := "#receive"

def fallbackOverrideName : Name := "#fallback"

def FunctionDecl.overrideMember? (origin : Path)
    (contractName : Name) (localTypeNames : List Name)
    (originKind : Solidity.ContractKind)
    (fn : Solidity.FunctionDecl) : Option OverrideMember :=
  match fn.kind, fn.name, fn.visibility with
  | Solidity.FunctionKind.function, some _,
      some Solidity.Visibility.private_ => none
  | Solidity.FunctionKind.function, some name, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := name
          params :=
            Tys.qualifyLocalUserTypes contractName localTypeNames
              (Parameters.tys fn.params)
          paramDataLocations := Parameters.dataLocations fn.params
          returns :=
            Tys.qualifyLocalUserTypes contractName localTypeNames
              (Parameters.tys fn.returns)
          returnDataLocations := Parameters.dataLocations fn.returns
          visibility := visibility
          mutability := fn.mutability
          virtual :=
            fn.virtual ||
              originKind == Solidity.ContractKind.interface
          implemented := fn.body.isSome }
  | Solidity.FunctionKind.receive, _, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := receiveOverrideName
          params := []
          returns := []
          visibility := visibility
          mutability := fn.mutability
          virtual :=
            fn.virtual ||
              originKind == Solidity.ContractKind.interface
          implemented := fn.body.isSome }
  | Solidity.FunctionKind.fallback, _, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := fallbackOverrideName
          params := []
          returns := []
          visibility := visibility
          mutability := fn.mutability
          virtual :=
            fn.virtual ||
              originKind == Solidity.ContractKind.interface
          implemented := fn.body.isSome }
  | _, _, _ => none

def ContractItem.overrideMember? (types : TypeContext)
    (contractName : Name) (localTypeNames : List Name)
    (origin : Path) (originKind : Solidity.ContractKind) :
    Solidity.ContractItem -> Option OverrideMember
  | Solidity.ContractItem.function fn =>
      FunctionDecl.overrideMember? origin contractName localTypeNames
        originKind fn
  | Solidity.ContractItem.stateVar decl =>
      StateVarDecl.publicGetterOverrideMember? types
        contractName localTypeNames origin originKind decl
  | _ => none

def ContractDecl.overrideMembers (types : TypeContext)
    (decl : Solidity.ContractDecl) : List OverrideMember :=
  let origin := TypeContext.pathOfName decl.name
  let localTypeNames := ContractDecl.localTypeNames decl
  decl.items.filterMap
    (ContractItem.overrideMember? types decl.name localTypeNames
      origin decl.kind)

def ContractDecls.lookupPath? (target : Path) :
    List Solidity.ContractDecl ->
    Option Solidity.ContractDecl
  | [] => none
  | decl :: rest =>
      if TypeContext.pathMatches target (TypeContext.pathOfName decl.name) then
        some decl
      else
        ContractDecls.lookupPath? target rest

def OverrideMembers.collectMostDerivedFrom (types : TypeContext)
    (members : List OverrideMember) :
    List Solidity.ContractDecl -> List OverrideMember
  | [] => members
  | decl :: rest =>
      OverrideMembers.collectMostDerivedFrom types
        (OverrideMembers.addAllIfNewKey members
          (ContractDecl.overrideMembers types decl))
        rest

def OverrideMembers.collectMostDerived (types : TypeContext)
    (order : List Solidity.ContractDecl) :
    List OverrideMember :=
  OverrideMembers.collectMostDerivedFrom types [] order

def BaseSpecifier.frontierOverrideMembers? (types : TypeContext)
    (contracts : List Solidity.ContractDecl)
    (specifier : Solidity.BaseSpecifier) :
    Option (List OverrideMember) := do
  let base ← ContractDecls.lookupPath? specifier.base contracts
  let order ←
    Solidity.Executable.ContractDecl.dispatchOrder? contracts base
  some (OverrideMembers.collectMostDerived types order)

def BaseSpecifiers.frontierOverrideMembers? (types : TypeContext)
    (contracts : List Solidity.ContractDecl) :
    List Solidity.BaseSpecifier -> Option (List OverrideMember)
  | [] => some []
  | specifier :: rest => do
      let head ← BaseSpecifier.frontierOverrideMembers? types contracts specifier
      let tail ← BaseSpecifiers.frontierOverrideMembers? types contracts rest
      some (head ++ tail)

def ContractDecl.inheritedOverrideMembers? (types : TypeContext)
    (contracts : List Solidity.ContractDecl)
    (decl : Solidity.ContractDecl) :
    Option (List OverrideMember) := do
  let members ← BaseSpecifiers.frontierOverrideMembers? types contracts decl.bases
  some (OverrideMembers.dedupOriginKeys members)

def ContractDecl.ancestorPaths? (contracts : List Solidity.ContractDecl)
    (decl : Solidity.ContractDecl) : Option (List Path) := do
  let order ←
    Solidity.Executable.ContractDecl.dispatchOrder? contracts decl
  some ((List.drop 1 order).map (fun base => TypeContext.pathOfName base.name))

def ContractDecl.originStrictlyInherits
    (contracts : List Solidity.ContractDecl)
    (descendant ancestor : Path) : Bool :=
  match ContractDecls.lookupPath? descendant contracts with
  | none => false
  | some decl =>
      match ContractDecl.ancestorPaths? contracts decl with
      | none => false
      | some ancestors => TypeContext.pathIn ancestor ancestors

def singleImplicitInterfaceOverride : List OverrideMember -> Bool
  | [member] => member.originKind == Solidity.ContractKind.interface
  | _ => false

def checkOverrideSpecifier (ancestorPaths : List Path)
    (baseMatches : List OverrideMember)
    (specifier : Solidity.OverrideSpecifier) :
    Except TypeError Unit := do
  require (pathAllIn specifier.bases ancestorPaths)
    (TypeError.invalidOverride "override specifier names a non-base contract")
  require (!pathListHasDuplicate specifier.bases)
    (TypeError.invalidOverride "duplicate contract in override list")
  if specifier.bases.isEmpty then
    require (baseMatches.length <= 1)
      (TypeError.invalidOverride "multiple base overrides require base list")
  else
    require
      (pathSetsEqual specifier.bases
        (OverrideMembers.originPaths baseMatches))
      (TypeError.invalidOverride "override base list does not match bases")

def checkOverrideUse (ancestorPaths : List Path)
    (override? : Option Solidity.OverrideSpecifier)
    (baseMatches : List OverrideMember) : Except TypeError Unit :=
  match override? with
  | none =>
      require (singleImplicitInterfaceOverride baseMatches)
        (TypeError.invalidOverride "missing override specifier")
  | some specifier =>
      checkOverrideSpecifier ancestorPaths baseMatches specifier

def FunctionDecl.checkOverrideRules (currentPath : Path)
    (currentContractName : Name) (localTypeNames : List Name)
    (currentKind : Solidity.ContractKind)
    (ancestorPaths : List Path) (inherited : List OverrideMember)
    (inheritedStateNames : List Name)
    (fn : Solidity.FunctionDecl) :
    Except TypeError Unit := do
  match fn.kind, fn.name with
  | Solidity.FunctionKind.function, some name =>
      require
        (!Solidity.Executable.nameIn name inheritedStateNames)
        (TypeError.invalidContractHeader
          "function shadows inherited state variable")
  | _, _ => Except.ok ()
  match FunctionDecl.overrideMember? currentPath currentContractName
      localTypeNames currentKind fn with
  | none =>
      require fn.override?.isNone
        (TypeError.invalidOverride "override on non-overridable function")
  | some current => do
      let baseMatches := OverrideMembers.matchingKey current inherited
      match baseMatches with
      | [] =>
          require fn.override?.isNone
            (TypeError.invalidOverride "override without matching base member")
      | _ =>
          OverrideMembers.checkOverridable baseMatches
          OverrideMembers.checkCompatible current baseMatches
          if !current.implemented then
            require (!baseMatches.any fun base => base.implemented)
              (TypeError.invalidOverride
                "implemented function cannot be overridden without a body")
          checkOverrideUse ancestorPaths fn.override? baseMatches

def StateVarDecl.checkOverrideRules (types : TypeContext)
    (currentPath : Path) (currentContractName : Name)
    (localTypeNames : List Name)
    (currentKind : Solidity.ContractKind)
    (ancestorPaths : List Path) (inherited : List OverrideMember)
    (decl : Solidity.StateVarDecl) :
    Except TypeError Unit :=
  match StateVarDecl.publicGetterOverrideMember? types
      currentContractName localTypeNames currentPath currentKind decl with
  | none => do
      require decl.override?.isNone
        (TypeError.invalidOverride "override on non-public state variable")
      require (!OverrideMembers.hasNonStateMemberNamed decl.name inherited)
        (TypeError.invalidContractHeader
          "state variable shadows inherited function")
  | some current => do
      let baseMatches := OverrideMembers.matchingKey current inherited
      match baseMatches with
      | [] =>
          require decl.override?.isNone
            (TypeError.invalidOverride
              "state-variable override without matching base function")
      | _ =>
          OverrideMembers.checkOverridable baseMatches
          OverrideMembers.checkCompatible current baseMatches
          checkOverrideUse ancestorPaths decl.override? baseMatches

def OverrideMembers.hasConflictFor (target : OverrideMember)
    (contracts : List Solidity.ContractDecl)
    (members : List OverrideMember) : Bool :=
  let dominated := fun member =>
    !member.implemented &&
      members.any (fun candidate =>
        OverrideMember.sameKey member candidate &&
          ContractDecl.originStrictlyInherits contracts
            candidate.origin member.origin)
  (matchingKey target (members.filter fun member => !dominated member)).length > 1

def OverrideMembers.hasDominatingImplementedFor
    (contracts : List Solidity.ContractDecl)
    (target : OverrideMember) (members : List OverrideMember) : Bool :=
  members.any (fun member =>
    OverrideMember.sameKey target member && member.implemented &&
      ContractDecl.originStrictlyInherits contracts
        member.origin target.origin)

def OverrideMembers.hasCurrentOverrideFor (target : OverrideMember)
    (current : List OverrideMember) : Bool :=
  containsKey target.name target.params current

def OverrideMembers.hasImplementedCurrentFor (target : OverrideMember)
    (current : List OverrideMember) : Bool :=
  match current with
  | [] => false
  | member :: rest =>
      (OverrideMember.sameKey target member && member.implemented) ||
        hasImplementedCurrentFor target rest

def OverrideMembers.checkInheritedConflicts
    (contracts : List Solidity.ContractDecl)
    (current : List OverrideMember)
    (members : List OverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if hasConflictFor member contracts members &&
          !hasCurrentOverrideFor member current then
        Except.error
          (TypeError.invalidOverride
            "multiple inherited base members require an override")
      else
        checkInheritedConflicts contracts current rest

def OverrideMembers.checkInheritedAbstractImplementedAux
    (contracts : List Solidity.ContractDecl)
    (contractIsAbstract : Bool) (current : List OverrideMember)
    (allMembers : List OverrideMember) :
    List OverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | member :: rest => do
      if !contractIsAbstract && !member.implemented &&
          !hasImplementedCurrentFor member current &&
          !hasDominatingImplementedFor contracts member allMembers then
        Except.error
          (TypeError.invalidContractHeader
            "non-abstract contract inherits unimplemented function")
      else
        checkInheritedAbstractImplementedAux contracts contractIsAbstract
          current allMembers rest

def OverrideMembers.checkInheritedAbstractImplemented
    (contracts : List Solidity.ContractDecl)
    (contractIsAbstract : Bool) (current : List OverrideMember)
    (members : List OverrideMember) : Except TypeError Unit :=
  checkInheritedAbstractImplementedAux contracts contractIsAbstract current
    members members

structure ModifierOverrideMember where
  origin : Path
  originKind : Solidity.ContractKind
  name : Name
  params : List Ty := []
  paramDataLocations :
    List (Option Solidity.DataLocation) := []
  virtual : Bool := false
  implemented : Bool := true
  deriving Repr

def ModifierDecl.overrideMember (origin : Path)
    (originKind : Solidity.ContractKind)
    (modifier : Solidity.ModifierDecl) : ModifierOverrideMember :=
  { origin := origin
    originKind := originKind
    name := modifier.name
    params := Parameters.tys modifier.params
    paramDataLocations := Parameters.dataLocations modifier.params
    virtual := modifier.virtual
    implemented := modifier.body.isSome }

namespace ModifierOverrideMembers

def sameName (a b : ModifierOverrideMember) : Bool :=
  a.name == b.name

def sameOriginName (a b : ModifierOverrideMember) : Bool :=
  a.origin == b.origin && sameName a b

def containsName (name : Name) : List ModifierOverrideMember -> Bool
  | [] => false
  | member :: rest => member.name == name || containsName name rest

def containsSameOriginName (target : ModifierOverrideMember) :
    List ModifierOverrideMember -> Bool
  | [] => false
  | member :: rest =>
      sameOriginName target member || containsSameOriginName target rest

def addIfNewName (members : List ModifierOverrideMember)
    (member : ModifierOverrideMember) : List ModifierOverrideMember :=
  if containsName member.name members then
    members
  else
    members ++ [member]

def addAllIfNewName (members : List ModifierOverrideMember) :
    List ModifierOverrideMember -> List ModifierOverrideMember
  | [] => members
  | member :: rest =>
      addAllIfNewName (addIfNewName members member) rest

def dedupOriginNames : List ModifierOverrideMember ->
    List ModifierOverrideMember
  | [] => []
  | member :: rest =>
      if containsSameOriginName member rest then
        dedupOriginNames rest
      else
        member :: dedupOriginNames rest

def matchingName (target : ModifierOverrideMember) :
    List ModifierOverrideMember -> List ModifierOverrideMember
  | [] => []
  | member :: rest =>
      if sameName target member then
        member :: matchingName target rest
      else
        matchingName target rest

def names : List ModifierOverrideMember -> List Name
  | [] => []
  | member :: rest => member.name :: names rest

def originPaths : List ModifierOverrideMember -> List Path
  | [] => []
  | member :: rest => member.origin :: originPaths rest

def checkOverridable : List ModifierOverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | member :: rest => do
      require member.virtual
        (TypeError.invalidOverride "base modifier is not virtual")
      checkOverridable rest

def checkCompatible (current : ModifierOverrideMember) :
    List ModifierOverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | base :: rest => do
      require (current.params == base.params)
        (TypeError.invalidOverride "override modifier parameters do not match")
      require (current.paramDataLocations == base.paramDataLocations)
        (TypeError.invalidOverride
          "override modifier parameter data locations do not match")
      checkCompatible current rest

def itemMember? (origin : Path)
    (originKind : Solidity.ContractKind) :
    Solidity.ContractItem -> Option ModifierOverrideMember
  | Solidity.ContractItem.modifierDecl modifier =>
      some (ModifierDecl.overrideMember origin originKind modifier)
  | _ => none

def forContract (decl : Solidity.ContractDecl) :
    List ModifierOverrideMember :=
  let origin := TypeContext.pathOfName decl.name
  decl.items.filterMap (itemMember? origin decl.kind)

def collectMostDerivedFrom (members : List ModifierOverrideMember) :
    List Solidity.ContractDecl -> List ModifierOverrideMember
  | [] => members
  | decl :: rest =>
      collectMostDerivedFrom
        (addAllIfNewName members (forContract decl)) rest

def collectMostDerived (order : List Solidity.ContractDecl) :
    List ModifierOverrideMember :=
  collectMostDerivedFrom [] order

def hasConflictFor (target : ModifierOverrideMember)
    (contracts : List Solidity.ContractDecl)
    (members : List ModifierOverrideMember) : Bool :=
  let dominated := fun member =>
    !member.implemented &&
      members.any (fun candidate =>
        sameName member candidate &&
          ContractDecl.originStrictlyInherits contracts
            candidate.origin member.origin)
  (matchingName target (members.filter fun member => !dominated member)).length > 1

def hasCurrentOverrideFor (target : ModifierOverrideMember)
    (current : List ModifierOverrideMember) : Bool :=
  containsName target.name current

def hasImplementedCurrentFor (target : ModifierOverrideMember)
    (current : List ModifierOverrideMember) : Bool :=
  match current with
  | [] => false
  | member :: rest =>
      (sameName target member && member.implemented) ||
        hasImplementedCurrentFor target rest

def hasDominatingImplementedFor
    (contracts : List Solidity.ContractDecl)
    (target : ModifierOverrideMember)
    (members : List ModifierOverrideMember) : Bool :=
  members.any (fun member =>
    sameName target member && member.implemented &&
      ContractDecl.originStrictlyInherits contracts
        member.origin target.origin)

def checkInheritedConflicts
    (contracts : List Solidity.ContractDecl)
    (current : List ModifierOverrideMember)
    (members : List ModifierOverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if hasConflictFor member contracts members &&
          !hasCurrentOverrideFor member current then
        Except.error
          (TypeError.invalidOverride
            "multiple inherited modifiers require an override")
      else
        checkInheritedConflicts contracts current rest

def checkInheritedAbstractImplemented
    (contracts : List Solidity.ContractDecl)
    (contractIsAbstract : Bool) (current : List ModifierOverrideMember)
    (allMembers : List ModifierOverrideMember) :
    List ModifierOverrideMember -> Except TypeError Unit
  | [] => Except.ok ()
  | member :: rest => do
      if !contractIsAbstract && !member.implemented &&
          !hasImplementedCurrentFor member current &&
          !hasDominatingImplementedFor contracts member allMembers then
        Except.error
          (TypeError.invalidContractHeader
            "non-abstract contract inherits unimplemented modifier")
      else
        checkInheritedAbstractImplemented contracts contractIsAbstract current
          allMembers rest

end ModifierOverrideMembers

def BaseSpecifier.frontierModifierMembers?
    (contracts : List Solidity.ContractDecl)
    (specifier : Solidity.BaseSpecifier) :
    Option (List ModifierOverrideMember) := do
  let base ← ContractDecls.lookupPath? specifier.base contracts
  let order ←
    Solidity.Executable.ContractDecl.dispatchOrder? contracts base
  some (ModifierOverrideMembers.collectMostDerived order)

def BaseSpecifiers.frontierModifierMembers?
    (contracts : List Solidity.ContractDecl) :
    List Solidity.BaseSpecifier ->
    Option (List ModifierOverrideMember)
  | [] => some []
  | specifier :: rest => do
      let head ← BaseSpecifier.frontierModifierMembers? contracts specifier
      let tail ← BaseSpecifiers.frontierModifierMembers? contracts rest
      some (head ++ tail)

def ContractDecl.inheritedModifierMembers?
    (contracts : List Solidity.ContractDecl)
    (decl : Solidity.ContractDecl) :
    Option (List ModifierOverrideMember) := do
  let members ← BaseSpecifiers.frontierModifierMembers? contracts decl.bases
  some (ModifierOverrideMembers.dedupOriginNames members)

def checkModifierOverrideUse (ancestorPaths : List Path)
    (override? : Option Solidity.OverrideSpecifier)
    (baseMatches : List ModifierOverrideMember) : Except TypeError Unit :=
  match override? with
  | none =>
      require false
        (TypeError.invalidOverride "missing modifier override specifier")
  | some specifier => do
      require (pathAllIn specifier.bases ancestorPaths)
        (TypeError.invalidOverride
          "modifier override specifier names a non-base contract")
      require (!pathListHasDuplicate specifier.bases)
        (TypeError.invalidOverride
          "duplicate contract in modifier override list")
      if specifier.bases.isEmpty then
        require (baseMatches.length <= 1)
          (TypeError.invalidOverride
            "multiple base modifier overrides require base list")
      else
        require
          (pathSetsEqual specifier.bases
            (ModifierOverrideMembers.originPaths baseMatches))
          (TypeError.invalidOverride
            "modifier override base list does not match bases")

def ModifierDecl.checkOverrideRules (currentPath : Path)
    (currentKind : Solidity.ContractKind)
    (ancestorPaths : List Path)
    (inherited : List ModifierOverrideMember)
    (modifier : Solidity.ModifierDecl) :
    Except TypeError Unit := do
  let current := ModifierDecl.overrideMember currentPath currentKind modifier
  let baseMatches := ModifierOverrideMembers.matchingName current inherited
  match baseMatches with
  | [] =>
      require modifier.override?.isNone
        (TypeError.invalidOverride "modifier override without matching base")
  | _ =>
      ModifierOverrideMembers.checkOverridable baseMatches
      ModifierOverrideMembers.checkCompatible current baseMatches
      if !current.implemented then
        require (!baseMatches.any fun base => base.implemented)
          (TypeError.invalidOverride
            "implemented modifier cannot be overridden without a body")
      checkModifierOverrideUse ancestorPaths modifier.override? baseMatches

def FunctionDecl.externallyVisible
    (fn : Solidity.FunctionDecl) : Bool :=
  match fn.visibility with
  | some Solidity.Visibility.public_ => true
  | some Solidity.Visibility.external_ => true
  | _ => false

def FunctionDecl.checkHeader (env : CheckEnv)
    (fn : Solidity.FunctionDecl) : Except TypeError Unit := do
  match env.contractKind, fn.kind with
  | none, Solidity.FunctionKind.function =>
      require fn.name.isSome
        (TypeError.invalidFunctionHeader "free function missing name")
      require fn.visibility.isNone
        (TypeError.invalidFunctionHeader "free function has visibility")
      require (!(fn.mutability == Solidity.StateMutability.payable))
        (TypeError.invalidFunctionHeader "free function is payable")
      require (!fn.virtual)
        (TypeError.invalidFunctionHeader "free function is virtual")
      require fn.override?.isNone
        (TypeError.invalidFunctionHeader "free function has override")
      require fn.modifiers.isEmpty
        (TypeError.invalidFunctionHeader "free function has modifiers")
  | none, _ =>
      Except.error
        (TypeError.invalidFunctionHeader
          "free declaration is not an ordinary function")
  | some _, Solidity.FunctionKind.function =>
      require fn.name.isSome
        (TypeError.invalidFunctionHeader "function missing name")
      require fn.visibility.isSome
        (TypeError.invalidFunctionHeader "contract function missing visibility")
  | some _, Solidity.FunctionKind.constructor =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "constructor has a name")
      match fn.visibility with
      | none => Except.ok ()
      | some Solidity.Visibility.public_ =>
          require (!env.currentContractAbstract)
            (TypeError.invalidFunctionHeader
              "abstract constructor is public")
      | some Solidity.Visibility.internal_ =>
          require env.currentContractAbstract
            (TypeError.invalidFunctionHeader
              "non-abstract constructor is internal")
      | some _ =>
          Except.error
            (TypeError.invalidFunctionHeader "constructor has visibility")
      require (!fn.virtual)
        (TypeError.invalidFunctionHeader "constructor is virtual")
      require fn.override?.isNone
        (TypeError.invalidFunctionHeader "constructor has override")
      require fn.returns.isEmpty
        (TypeError.invalidFunctionHeader "constructor has returns")
      require fn.body.isSome
        (TypeError.invalidFunctionHeader "constructor has no implementation")
      require
        (fn.mutability == Solidity.StateMutability.nonpayable ||
          fn.mutability == Solidity.StateMutability.payable)
        (TypeError.invalidFunctionHeader
          "constructor has invalid mutability")
      require (!Parameters.anyCalldata fn.params)
        (TypeError.invalidFunctionHeader
          "constructor parameter uses calldata")
      if env.currentContractAbstract then
        Except.ok ()
      else
        require (!Parameters.anyStorageRef env.types fn.params)
          (TypeError.invalidFunctionHeader
            "constructor parameter uses storage")
      if env.currentContractAbstract then
        Except.ok ()
      else
        match Parameters.firstAbiCoderV2OnlyTy? env.types fn.params with
        | some ty => Except.error (TypeError.invalidAbiType ty)
        | none => Except.ok ()
  | some _, Solidity.FunctionKind.receive =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "receive function has a name")
      require fn.params.isEmpty
        (TypeError.invalidFunctionHeader "receive function has parameters")
      require fn.returns.isEmpty
        (TypeError.invalidFunctionHeader "receive function has returns")
      require
        (fn.visibility == some Solidity.Visibility.external_)
        (TypeError.invalidFunctionHeader
          "receive function is not external")
      require
        (fn.mutability == Solidity.StateMutability.payable)
        (TypeError.invalidFunctionHeader
          "receive function is not payable")
  | some _, Solidity.FunctionKind.fallback =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "fallback function has a name")
      require
        (fn.visibility == some Solidity.Visibility.external_)
        (TypeError.invalidFunctionHeader
          "fallback function is not external")
      require
        (fn.mutability == Solidity.StateMutability.nonpayable ||
          fn.mutability == Solidity.StateMutability.payable)
        (TypeError.invalidFunctionHeader
          "fallback function has invalid mutability")
      let untypedFallback := fn.params.isEmpty && fn.returns.isEmpty
      let typedFallback :=
        match fn.params, fn.returns with
        | [input], [output] =>
            Parameter.isBytesCalldata input &&
              Parameter.isBytesMemory output
        | _, _ => false
      require (untypedFallback || typedFallback)
        (TypeError.invalidFunctionHeader
          "fallback function has invalid parameters or returns")
  if env.contractKind.isNone then
    require fn.body.isSome
      (TypeError.invalidFunctionHeader "free function has no implementation")
  else
    Except.ok ()
  require
    (!(fn.visibility == some Solidity.Visibility.private_) ||
      !fn.virtual)
    (TypeError.invalidFunctionHeader "private function is virtual")
  if env.inLibrary && fn.kind == Solidity.FunctionKind.function then
    require (!fn.virtual)
      (TypeError.invalidFunctionHeader "library function is virtual")
    require (!(fn.mutability == Solidity.StateMutability.payable))
      (TypeError.invalidFunctionHeader "library function is payable")
  else
    Except.ok ()
  if env.contractKind == some Solidity.ContractKind.interface then
    Except.ok ()
  else if !(fn.kind == Solidity.FunctionKind.constructor) &&
      fn.body.isNone then
    require fn.virtual
      (TypeError.invalidFunctionHeader
        "unimplemented function is not virtual")
  else
    Except.ok ()
  if FunctionDecl.externallyVisible fn then
    if env.inLibrary then
      Except.ok ()
    else
      require (!Parameters.anyStorageRef env.types fn.params)
        (TypeError.invalidFunctionHeader
          "external/public function parameter uses storage")
    require (!Parameters.anyStorageRef env.types fn.returns)
      (TypeError.invalidFunctionHeader
        "external/public function return uses storage")
    if env.inLibrary then
      Except.ok ()
    else
      match Parameters.firstMappingContainingTy? env.types fn.params with
      | some ty => Except.error (TypeError.invalidAbiType ty)
      | none => Except.ok ()
    if env.inLibrary then
      Except.ok ()
    else
      match Parameters.firstNonAbiEncodableTy? env.types fn.params with
      | some ty => Except.error (TypeError.invalidAbiType ty)
      | none => Except.ok ()
    if env.inLibrary then
      Except.ok ()
    else
      match Parameters.firstAbiCoderV2OnlyTy? env.types fn.params with
      | some ty => Except.error (TypeError.invalidAbiType ty)
      | none => Except.ok ()
    match Parameters.firstMappingContainingTy? env.types fn.returns with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Parameters.firstNonAbiEncodableTy? env.types fn.returns with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Parameters.firstAbiCoderV2OnlyTy? env.types fn.returns with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
  else
    Except.ok ()

def ModifierInvocation.targetName
    (invocation : Solidity.ModifierInvocation) :
    Except TypeError Name := do
  let name ←
    match Solidity.Executable.pathLast? invocation.target with
    | some name => Except.ok name
    | none =>
        Except.error
          (TypeError.invalidFunctionHeader "empty modifier invocation")
  Except.ok name

def ModifierInvocation.baseConstructorPath?
    (env : CheckEnv)
    (invocation : Solidity.ModifierInvocation) :
    Option Path := do
  let name ← Solidity.Executable.pathLast? invocation.target
  let path := TypeContext.pathOfName name
  if TypeContext.pathIn path env.ancestorPaths then
    some path
  else
    none

def ModifierInvocation.baseConstructorDecl?
    (env : CheckEnv)
    (invocation : Solidity.ModifierInvocation) :
    Option Solidity.ContractDecl := do
  let path ← ModifierInvocation.baseConstructorPath? env invocation
  env.types.lookupContractDecl? path

def ModifierInvocation.checkBaseConstructor (env : CheckEnv)
    (invocation : Solidity.ModifierInvocation)
    (baseDecl : Solidity.ContractDecl) :
    Except TypeError Unit := do
  let sig := ContractDecl.constructorSignature baseDecl
  match checkArgs env invocation.args with
  | Except.ok checkedArgs =>
      match
          checkCheckedArgsAssignableToFunctionSig env.types
            ("base constructor " ++ baseDecl.name) sig invocation.args
            checkedArgs with
      | Except.ok _ => Except.ok ()
      | Except.error checkedErr =>
          match
              checkContextualArgsAssignableToParamsWithStorageRefsFor
                env ("base constructor " ++ baseDecl.name)
                sig.paramNames sig.params sig.paramStorageRefs
                sig.paramDataLocations invocation.args with
          | Except.ok _ => Except.ok ()
          | Except.error _ => Except.error checkedErr
  | Except.error argErr =>
      match
          checkContextualArgsAssignableToParamsWithStorageRefsFor
            env ("base constructor " ++ baseDecl.name)
            sig.paramNames sig.params sig.paramStorageRefs
            sig.paramDataLocations invocation.args with
      | Except.ok _ => Except.ok ()
      | Except.error _ => Except.error argErr

def ModifierInvocation.check (env : CheckEnv) (allowBaseConstructors : Bool)
    (invocation : Solidity.ModifierInvocation) :
    Except TypeError Unit := do
  match ModifierInvocation.baseConstructorDecl? env invocation with
  | some baseDecl =>
      require allowBaseConstructors
        (TypeError.invalidFunctionHeader
          "base constructor invocation outside constructor")
      -- solc 1563 (ContractLevelChecker.cpp:372-382): a modifier-style
      -- base-constructor call with no argument list (bare `B`, not `B()`) is a
      -- declaration error, regardless of whether the base has a constructor.
      require invocation.hasArgList
        (TypeError.invalidFunctionHeader
          "modifier-style base constructor call without arguments")
      ModifierInvocation.checkBaseConstructor env invocation baseDecl
  | none =>
      let name ← ModifierInvocation.targetName invocation
      checkModifierArgs env name invocation.args

def modifierBodyFunction? :
    Solidity.ContractItem -> Option Solidity.FunctionDecl
  | Solidity.ContractItem.function fn => some fn
  | _ => none

def contractFunctionSigsForModifierBody
    (entry : Path × Solidity.ContractDecl) :
    List FunctionSig :=
  let decl := entry.snd
  (FunctionDecls.signatures (decl.items.filterMap modifierBodyFunction?)).map
    (FunctionSig.qualifyLocalUserTypes decl.name
      (ContractDecl.localTypeNames decl))

def contractEntriesFunctionSigsForModifierBodies :
    List (Path × Solidity.ContractDecl) -> List FunctionSig
  | [] => []
  | entry :: rest =>
      contractFunctionSigsForModifierBody entry ++
        contractEntriesFunctionSigsForModifierBodies rest

def TypeContext.functionSigsForModifierBodies
    (types : TypeContext) : List FunctionSig :=
  contractEntriesFunctionSigsForModifierBodies types.contractDecls

def ModifierInvocation.checkBodyForCaller (env : CheckEnv)
    (invocation : Solidity.ModifierInvocation) :
    Except TypeError Unit := do
  match ModifierInvocation.baseConstructorDecl? env invocation with
  | some _ => Except.ok ()
  | none =>
      let name ← ModifierInvocation.targetName invocation
      match env.lookupModifierDecl? name with
      | none =>
          Except.error
            (TypeError.unknownIdentifier name)
      | some modifier =>
          match modifier.body with
          | none => Except.ok ()
          | some body =>
              let locals :=
                Parameters.namedTypeStorageRefs env.types modifier.params
              let dataLocations :=
                Parameters.namedDataLocations env.types modifier.params
              let modifierEnv :=
                { env.enterModifier with
                  functions :=
                    env.types.functionSigsForModifierBodies ++
                      env.functions
                  vars := locals.map (fun entry => (entry.1, entry.2.1)) ++
                    env.vars
                  localNames := locals.map Prod.fst ++ env.localNames
                  localStorageRefs :=
                    (locals.filterMap
                      (fun entry =>
                        if entry.2.2 then some entry.1 else none)) ++
                      env.localStorageRefs
                  localDataLocations :=
                    dataLocations ++ env.localDataLocations
                  returnTys := []
                  returnNames := [] }
              let _ ← checkStmt modifierEnv body
              Except.ok ()

def ModifierInvocations.checkWithSeen (env : CheckEnv)
    (allowBaseConstructors : Bool) (seenBaseConstructors : List Path) :
    List Solidity.ModifierInvocation -> Except TypeError Unit
  | [] => Except.ok ()
  | invocation :: rest => do
      let nextSeen ←
        match ModifierInvocation.baseConstructorPath? env invocation with
        | some path => do
            require (!TypeContext.pathIn path seenBaseConstructors)
              (TypeError.invalidContractHeader
                "duplicate base constructor invocation")
            Except.ok (path :: seenBaseConstructors)
        | none => Except.ok seenBaseConstructors
      ModifierInvocation.check env allowBaseConstructors invocation
      ModifierInvocations.checkWithSeen env allowBaseConstructors nextSeen
        rest

def ModifierInvocations.check (env : CheckEnv)
    (allowBaseConstructors : Bool) :
    List Solidity.ModifierInvocation -> Except TypeError Unit :=
  ModifierInvocations.checkWithSeen env allowBaseConstructors []

def ModifierInvocations.checkBodiesForCaller (env : CheckEnv) :
    List Solidity.ModifierInvocation -> Except TypeError Unit
  | [] => Except.ok ()
  | invocation :: rest => do
      ModifierInvocation.checkBodyForCaller env invocation
      ModifierInvocations.checkBodiesForCaller env rest

abbrev PointerReturnAssigned := List Name

def PointerReturnAssigned.add
    (assigned : PointerReturnAssigned) (name : Name) :
    PointerReturnAssigned :=
  if assigned.contains name then assigned else name :: assigned

def PointerReturnAssigned.intersection
    (left right : PointerReturnAssigned) : PointerReturnAssigned :=
  left.filter (fun name => right.contains name)

def mergePointerReturnState :
    Option PointerReturnAssigned -> Option PointerReturnAssigned ->
    Option PointerReturnAssigned
  | none, right => right
  | left, none => left
  | some left, some right =>
      some (PointerReturnAssigned.intersection left right)

structure PointerReturnRequirements where
  named : List Name := []
  hasUnnamed : Bool := false
  deriving Repr

def Parameter.isUninitializedPointerReturn
    (types : TypeContext) (param : Solidity.Parameter) : Bool :=
  Ty.needsDataLocation types param.ty &&
    (param.location == some Solidity.DataLocation.storage ||
      param.location == some Solidity.DataLocation.calldata)

def Parameters.pointerReturnRequirements (types : TypeContext) :
    List Solidity.Parameter -> PointerReturnRequirements
  | [] => {}
  | param :: rest =>
      let tail := Parameters.pointerReturnRequirements types rest
      if Parameter.isUninitializedPointerReturn types param then
        match param.name with
        | some name => { tail with named := name :: tail.named }
        | none => { tail with hasUnnamed := true }
      else
        tail

def PointerReturnRequirements.isEmpty
    (requirements : PointerReturnRequirements) : Bool :=
  requirements.named.isEmpty && !requirements.hasUnnamed

def PointerReturnRequirements.allAssigned
    (requirements : PointerReturnRequirements)
    (assigned : PointerReturnAssigned) : Bool :=
  !requirements.hasUnnamed &&
    requirements.named.all (fun name => assigned.contains name)

structure PointerExprFlow where
  assigned : PointerReturnAssigned
  unsafeRead : Bool := false
  deriving Repr

def mergePointerExprBranches
    (left right : PointerExprFlow) : PointerExprFlow :=
  { assigned := PointerReturnAssigned.intersection left.assigned right.assigned
    unsafeRead := left.unsafeRead || right.unsafeRead }

mutual

def Expr.pointerReturnFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    Solidity.Expr -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, Solidity.Expr.literal _ =>
      { assigned := assigned }
  | _ + 1, requirements, assigned,
      Solidity.Expr.ident name =>
      { assigned := assigned
        unsafeRead :=
          requirements.named.contains name && !assigned.contains name }
  | _ + 1, _, assigned, Solidity.Expr.typeName _ =>
      { assigned := assigned }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.member base _ =>
      Expr.pointerReturnFlowFuel fuel requirements assigned base
  | fuel + 1, requirements, assigned,
      Solidity.Expr.index base index =>
      let indexFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned index
      let baseFlow :=
        Expr.pointerReturnFlowFuel fuel requirements indexFlow.assigned base
      { baseFlow with
        unsafeRead := indexFlow.unsafeRead || baseFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.slice base start stop =>
      let stopFlow :=
        match stop with
        | some expr =>
            Expr.pointerReturnFlowFuel fuel requirements assigned expr
        | none => { assigned := assigned }
      let startFlow :=
        match start with
        | some expr =>
            Expr.pointerReturnFlowFuel fuel requirements stopFlow.assigned expr
        | none => { assigned := stopFlow.assigned }
      let baseFlow :=
        Expr.pointerReturnFlowFuel fuel requirements startFlow.assigned base
      { baseFlow with
        unsafeRead := stopFlow.unsafeRead || startFlow.unsafeRead ||
          baseFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.call fn args =>
      let argsFlow :=
        Args.pointerReturnFlowFuel fuel requirements assigned args
      let fnFlow :=
        Expr.pointerReturnFlowFuel fuel requirements argsFlow.assigned fn
      { fnFlow with
        unsafeRead := argsFlow.unsafeRead || fnFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.callWithOptions fn options args =>
      let argsFlow :=
        Args.pointerReturnFlowFuel fuel requirements assigned args
      let optionsFlow :=
        CallOptions.pointerReturnFlowFuel fuel requirements argsFlow.assigned
          options
      let fnFlow :=
        Expr.pointerReturnFlowFuel fuel requirements optionsFlow.assigned fn
      { fnFlow with
        unsafeRead := argsFlow.unsafeRead || optionsFlow.unsafeRead ||
          fnFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.newExpr _ args =>
      Args.pointerReturnFlowFuel fuel requirements assigned args
  | fuel + 1, requirements, assigned,
      Solidity.Expr.tuple items =>
      TupleItems.pointerReturnFlowFuel fuel requirements assigned items
  | fuel + 1, requirements, assigned,
      Solidity.Expr.array items =>
      Exprs.pointerReturnFlowFuel fuel requirements assigned items
  | fuel + 1, requirements, assigned,
      Solidity.Expr.enumFromUInt _ inner =>
      Expr.pointerReturnFlowFuel fuel requirements assigned inner
  | fuel + 1, requirements, assigned,
      Solidity.Expr.unary _ inner =>
      Expr.pointerReturnFlowFuel fuel requirements assigned inner
  | fuel + 1, requirements, assigned,
      Solidity.Expr.binary op left right =>
      if op == Solidity.BinaryOp.boolAnd ||
          op == Solidity.BinaryOp.boolOr then
        let leftFlow :=
          Expr.pointerReturnFlowFuel fuel requirements assigned left
        let rightFlow :=
          Expr.pointerReturnFlowFuel fuel requirements leftFlow.assigned right
        mergePointerExprBranches leftFlow
          { rightFlow with
            unsafeRead := leftFlow.unsafeRead || rightFlow.unsafeRead }
      else
        let rightFlow :=
          Expr.pointerReturnFlowFuel fuel requirements assigned right
        let leftFlow :=
          Expr.pointerReturnFlowFuel fuel requirements rightFlow.assigned left
        { leftFlow with
          unsafeRead := rightFlow.unsafeRead || leftFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.ternary cond thenExpr elseExpr =>
      let condFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned cond
      let thenFlow :=
        Expr.pointerReturnFlowFuel fuel requirements condFlow.assigned thenExpr
      let elseFlow :=
        Expr.pointerReturnFlowFuel fuel requirements condFlow.assigned elseExpr
      let branches := mergePointerExprBranches thenFlow elseFlow
      { branches with
        unsafeRead := condFlow.unsafeRead || branches.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.assign lhs op rhs =>
      let rhsFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned rhs
      let lhsFlow :=
        match op with
        | Solidity.AssignOp.assign =>
            Expr.pointerReturnLValueFlowFuel fuel requirements rhsFlow.assigned
              lhs
        | _ =>
            Expr.pointerReturnFlowFuel fuel requirements rhsFlow.assigned lhs
      { lhsFlow with
        unsafeRead := rhsFlow.unsafeRead || lhsFlow.unsafeRead }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.payableConversion inner =>
      Expr.pointerReturnFlowFuel fuel requirements assigned inner

def Expr.pointerReturnLValueFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    Solidity.Expr -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, requirements, assigned,
      Solidity.Expr.ident name =>
      if requirements.named.contains name then
        { assigned := PointerReturnAssigned.add assigned name }
      else
        { assigned := assigned }
  | fuel + 1, requirements, assigned,
      Solidity.Expr.tuple items =>
      TupleItems.pointerReturnLValueFlowFuel fuel requirements assigned items
  | fuel + 1, requirements, assigned, other =>
      Expr.pointerReturnFlowFuel fuel requirements assigned other

def Exprs.pointerReturnFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    List Solidity.Expr -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, [] => { assigned := assigned }
  | fuel + 1, requirements, assigned, expr :: rest =>
      let tailFlow :=
        Exprs.pointerReturnFlowFuel fuel requirements assigned rest
      let headFlow :=
        Expr.pointerReturnFlowFuel fuel requirements tailFlow.assigned expr
      { headFlow with
        unsafeRead := tailFlow.unsafeRead || headFlow.unsafeRead }

def Args.pointerReturnFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    List Solidity.Arg -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, [] => { assigned := assigned }
  | fuel + 1, requirements, assigned, arg :: rest =>
      let tailFlow :=
        Args.pointerReturnFlowFuel fuel requirements assigned rest
      let expr :=
        match arg with
        | Solidity.Arg.positional expr => expr
        | Solidity.Arg.named _ expr => expr
      let headFlow :=
        Expr.pointerReturnFlowFuel fuel requirements tailFlow.assigned expr
      { headFlow with
        unsafeRead := tailFlow.unsafeRead || headFlow.unsafeRead }

def CallOptions.pointerReturnFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    List Solidity.CallOption -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, [] => { assigned := assigned }
  | fuel + 1, requirements, assigned,
      Solidity.CallOption.named _ expr :: rest =>
      let tailFlow :=
        CallOptions.pointerReturnFlowFuel fuel requirements assigned rest
      let headFlow :=
        Expr.pointerReturnFlowFuel fuel requirements tailFlow.assigned expr
      { headFlow with
        unsafeRead := tailFlow.unsafeRead || headFlow.unsafeRead }

def TupleItems.pointerReturnFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    List Solidity.TupleItem -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, [] => { assigned := assigned }
  | fuel + 1, requirements, assigned, item :: rest =>
      let tailFlow :=
        TupleItems.pointerReturnFlowFuel fuel requirements assigned rest
      match item with
      | Solidity.TupleItem.hole => tailFlow
      | Solidity.TupleItem.value expr =>
          let headFlow :=
            Expr.pointerReturnFlowFuel fuel requirements tailFlow.assigned expr
          { headFlow with
            unsafeRead := tailFlow.unsafeRead || headFlow.unsafeRead }

def TupleItems.pointerReturnLValueFlowFuel :
    Nat -> PointerReturnRequirements -> PointerReturnAssigned ->
    List Solidity.TupleItem -> PointerExprFlow
  | 0, _, assigned, _ => { assigned := assigned, unsafeRead := true }
  | _ + 1, _, assigned, [] => { assigned := assigned }
  | fuel + 1, requirements, assigned, item :: rest =>
      let tailFlow :=
        TupleItems.pointerReturnLValueFlowFuel fuel requirements assigned rest
      match item with
      | Solidity.TupleItem.hole => tailFlow
      | Solidity.TupleItem.value expr =>
          let headFlow :=
            Expr.pointerReturnLValueFlowFuel fuel requirements tailFlow.assigned
              expr
          { headFlow with
            unsafeRead := tailFlow.unsafeRead || headFlow.unsafeRead }

end

structure PointerReturnFlow where
  normal? : Option PointerReturnAssigned := none
  breaks? : Option PointerReturnAssigned := none
  continues? : Option PointerReturnAssigned := none
  unsafeReturn : Bool := false
  deriving Repr

def PointerReturnFlow.mergeBranches
    (left right : PointerReturnFlow) : PointerReturnFlow :=
  { normal? := mergePointerReturnState left.normal? right.normal?
    breaks? := mergePointerReturnState left.breaks? right.breaks?
    continues? := mergePointerReturnState left.continues? right.continues?
    unsafeReturn := left.unsafeReturn || right.unsafeReturn }

structure PointerReturnPlaceholder where
  modifiers : List Solidity.ModifierInvocation
  body : Solidity.Stmt

def exprFlowToNormal (flow : PointerExprFlow) : PointerReturnFlow :=
  { normal? := some flow.assigned, unsafeReturn := flow.unsafeRead }

def Expr.isTerminalBuiltinCall : Solidity.Expr -> Bool
  | Solidity.Expr.call
      (Solidity.Expr.ident "selfdestruct") _ => true
  | Solidity.Expr.call
      (Solidity.Expr.ident "revert") _ => true
  | _ => false

-- CF2: the callee name of a direct-by-name call `f(...)` / `f{...}(...)`, if any.
-- Only bare-ident callees are internal-call targets that the revert pruner
-- resolves; `this.f()` / member calls are external and never pruned.
def Expr.callTargetName? : Solidity.Expr -> Option Name
  | Solidity.Expr.call (Solidity.Expr.ident name) _ => some name
  | Solidity.Expr.callWithOptions (Solidity.Expr.ident name) _ _ => some name
  | _ => none

-- CF2: is `e` a call to a provably-always-reverting internal function?
def Expr.isAlwaysRevertingCall
    (arNames : List Name) (e : Solidity.Expr) : Bool :=
  match Expr.callTargetName? e with
  | some name => Solidity.Executable.nameIn name arNames
  | none => false

mutual

def Stmt.pointerReturnFlowFuel :
    Nat -> CheckEnv -> PointerReturnRequirements ->
    Option PointerReturnPlaceholder -> PointerReturnAssigned ->
    Solidity.Stmt -> PointerReturnFlow
  | 0, _, _, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, _, _, assigned, Solidity.Stmt.empty =>
      { normal? := some assigned }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.block body =>
      Stmts.pointerReturnFlowFuel fuel env requirements placeholder assigned body
  | fuel + 1, _, requirements, _, assigned,
      Solidity.Stmt.varDecl _ init? =>
      match init? with
      | some init =>
          exprFlowToNormal
            (Expr.pointerReturnFlowFuel fuel requirements assigned init)
      | none => { normal? := some assigned }
  | fuel + 1, env, requirements, _, assigned,
      Solidity.Stmt.expr expr =>
      let flow := Expr.pointerReturnFlowFuel fuel requirements assigned expr
      -- CF2: a call to a provably-always-reverting internal function never
      -- returns, so (like a direct `revert`/`selfdestruct`) it does not reach
      -- the function exit — no `normal?` continuation. The args are still
      -- evaluated before the call, so an unsafe read there is preserved.
      if Expr.isTerminalBuiltinCall expr ||
          Expr.isAlwaysRevertingCall env.alwaysRevertNames expr then
        { unsafeReturn := flow.unsafeRead }
      else
        exprFlowToNormal flow
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.ifElse cond thenBranch elseBranch =>
      let condFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned cond
      let thenFlow :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder
          condFlow.assigned thenBranch
      let elseFlow :=
        match elseBranch with
        | some branch =>
            Stmt.pointerReturnFlowFuel fuel env requirements placeholder
              condFlow.assigned branch
        | none => { normal? := some condFlow.assigned }
      let branches := thenFlow.mergeBranches elseFlow
      { branches with
        unsafeReturn := condFlow.unsafeRead || branches.unsafeReturn }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.whileLoop cond body =>
      let condFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned cond
      let bodyFlow :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder
          condFlow.assigned body
      { normal? := some condFlow.assigned
        unsafeReturn := condFlow.unsafeRead || bodyFlow.unsafeReturn }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.doWhile body cond =>
      let bodyFlow :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder assigned body
      let reachesCond :=
        mergePointerReturnState bodyFlow.normal? bodyFlow.continues?
      let condFlow? :=
        reachesCond.map (fun state =>
          Expr.pointerReturnFlowFuel fuel requirements state cond)
      let normalFromCond := condFlow?.map PointerExprFlow.assigned
      { normal? := mergePointerReturnState bodyFlow.breaks? normalFromCond
        unsafeReturn := bodyFlow.unsafeReturn ||
          condFlow?.any PointerExprFlow.unsafeRead }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.forLoop init cond post body =>
      let initFlow :=
        match init with
        | some stmt =>
            Stmt.pointerReturnFlowFuel fuel env requirements placeholder
              assigned stmt
        | none => { normal? := some assigned }
      match initFlow.normal? with
      | none => initFlow
      | some afterInit =>
          let condFlow :=
            match cond with
            | some expr =>
                Expr.pointerReturnFlowFuel fuel requirements afterInit expr
            | none => { assigned := afterInit }
          let bodyFlow :=
            Stmt.pointerReturnFlowFuel fuel env requirements placeholder
              condFlow.assigned body
          let postInput :=
            mergePointerReturnState bodyFlow.normal? bodyFlow.continues?
          let postUnsafe :=
            match postInput, post with
            | some state, some expr =>
                (Expr.pointerReturnFlowFuel fuel requirements state expr).unsafeRead
            | _, _ => false
          { normal? := some condFlow.assigned
            breaks? := initFlow.breaks?
            continues? := initFlow.continues?
            unsafeReturn := initFlow.unsafeReturn || condFlow.unsafeRead ||
              bodyFlow.unsafeReturn || postUnsafe }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.tryCatch expr clauses =>
      let exprFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned expr
      let catches :=
        CatchClauses.pointerReturnFlowFuel fuel env requirements placeholder
          exprFlow.assigned clauses
      let success : PointerReturnFlow := { normal? := some exprFlow.assigned }
      let merged := success.mergeBranches catches
      { merged with
        unsafeReturn := exprFlow.unsafeRead || merged.unsafeReturn }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.tryCatchReturns expr _ success clauses =>
      let exprFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned expr
      let successFlow :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder
          exprFlow.assigned success
      let catches :=
        CatchClauses.pointerReturnFlowFuel fuel env requirements placeholder
          exprFlow.assigned clauses
      let merged := successFlow.mergeBranches catches
      { merged with
        unsafeReturn := exprFlow.unsafeRead || merged.unsafeReturn }
  | fuel + 1, _, requirements, _, assigned,
      Solidity.Stmt.emitEvent expr =>
      exprFlowToNormal
        (Expr.pointerReturnFlowFuel fuel requirements assigned expr)
  | fuel + 1, _, requirements, _, assigned,
      Solidity.Stmt.revertCall expr =>
      let flow := Expr.pointerReturnFlowFuel fuel requirements assigned expr
      { unsafeReturn := flow.unsafeRead }
  | fuel + 1, _, requirements, _, assigned,
      Solidity.Stmt.returnValues expr? =>
      match expr? with
      | some expr =>
          let flow := Expr.pointerReturnFlowFuel fuel requirements assigned expr
          { unsafeReturn := flow.unsafeRead }
      | none =>
          { unsafeReturn := !requirements.allAssigned assigned }
  | _ + 1, _, _, _, assigned, Solidity.Stmt.break =>
      { breaks? := some assigned }
  | _ + 1, _, _, _, assigned, Solidity.Stmt.continue =>
      { continues? := some assigned }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.unchecked body =>
      Stmt.pointerReturnFlowFuel fuel env requirements placeholder assigned body
  | _ + 1, _, _, _, _, Solidity.Stmt.inlineAssembly _ =>
      { unsafeReturn := true }
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.Stmt.modifierPlaceholder =>
      match placeholder with
      | some continuation =>
          FunctionDecl.pointerReturnFlowWithModifiersFuel fuel env requirements
            continuation.modifiers continuation.body assigned
      | none => { unsafeReturn := true }

def Stmts.pointerReturnFlowFuel :
    Nat -> CheckEnv -> PointerReturnRequirements ->
    Option PointerReturnPlaceholder -> PointerReturnAssigned ->
    List Solidity.Stmt -> PointerReturnFlow
  | 0, _, _, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, _, _, assigned, [] => { normal? := some assigned }
  | fuel + 1, env, requirements, placeholder, assigned, stmt :: rest =>
      let head :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder assigned stmt
      let tail :=
        match head.normal? with
        | some state =>
            Stmts.pointerReturnFlowFuel fuel env requirements placeholder state
              rest
        | none => {}
      { normal? := tail.normal?
        breaks? := mergePointerReturnState head.breaks? tail.breaks?
        continues? :=
          mergePointerReturnState head.continues? tail.continues?
        unsafeReturn := head.unsafeReturn || tail.unsafeReturn }

def CatchClauses.pointerReturnFlowFuel :
    Nat -> CheckEnv -> PointerReturnRequirements ->
    Option PointerReturnPlaceholder -> PointerReturnAssigned ->
    List Solidity.CatchClause -> PointerReturnFlow
  | 0, _, _, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, _, _, _, [] => {}
  | fuel + 1, env, requirements, placeholder, assigned,
      Solidity.CatchClause.clause _ _ body :: rest =>
      let head :=
        Stmt.pointerReturnFlowFuel fuel env requirements placeholder assigned body
      let tail :=
        CatchClauses.pointerReturnFlowFuel fuel env requirements placeholder
          assigned rest
      head.mergeBranches tail

def FunctionDecl.pointerReturnFlowWithModifiersFuel :
    Nat -> CheckEnv -> PointerReturnRequirements ->
    List Solidity.ModifierInvocation -> Solidity.Stmt ->
    PointerReturnAssigned -> PointerReturnFlow
  | 0, _, _, _, _, _ => { unsafeReturn := true }
  | fuel + 1, env, requirements, [], body, assigned =>
      Stmt.pointerReturnFlowFuel fuel env requirements none assigned body
  | fuel + 1, env, requirements, invocation :: rest, body, assigned =>
      let argFlow :=
        Args.pointerReturnFlowFuel fuel requirements assigned invocation.args
      let modifierName? :=
        (Solidity.Executable.pathInitLast? invocation.target).map
          Prod.snd
      match modifierName?.bind env.lookupModifierDecl? with
      | some modifier =>
          match modifier.body with
          | some modifierBody =>
              let placeholder := some { modifiers := rest, body := body }
              let flow :=
                Stmt.pointerReturnFlowFuel fuel env requirements placeholder
                  argFlow.assigned modifierBody
              { flow with
                unsafeReturn := argFlow.unsafeRead || flow.unsafeReturn }
          | none => { unsafeReturn := true }
      | none => { unsafeReturn := true }

end

def defaultPointerReturnFlowFuel : Nat := 4096

/-!
CF2 — the "always reverts" analysis (solc `ControlFlowRevertPruner`).

A function ALWAYS reverts iff, in solc's CFG, its entry cannot reach the exit
node — every path ends at the revert node. We under-approximate this soundly:
we only mark a statement as always-reverting when it PROVABLY diverts to a
revert on every path.

Primitive terminators (solc `ControlFlowBuilder::visit(FunctionCall)` /
`RevertStatement` / `Throw`):
- a `revert(...)` / `revert Err(...)` / `selfdestruct(...)`;
- a call to an internal function already known to always revert.
`require`/`assert` are NOT terminators: solc connects them to BOTH the revert
node and a following node (probed: a `require(false)` helper does NOT prune),
so `require(false)`-style helpers correctly stay non-reverting here.

We compute per statement a pair `(falls, exits)` (`Stmt.revertFlowFuel`):
  * `falls` — control can reach the END of the statement (continue to the
    following statement / fall out of the function body);
  * `exits` — control can leave the FUNCTION via a `return` reachable inside
    the statement (reach the CFG exit node).
A statement ALWAYS reverts iff `!falls && !exits` — every path ends at the
revert node. Both bits are OVER-approximated (biased to `true`) for everything
we don't prove terminating, so `alwaysReverts` is UNDER-approximated: we only
mark a statement always-reverting when provably so.

Terminating leaves (`(false, false)`): `revert`/`selfdestruct` and a call to an
already-known-always-reverting internal function. `return` is `(false, true)`
(reaches the exit, NOT the revert node — so it does NOT make a function always
revert). Sequencing threads control only past a statement that can fall
through; a statement's `exits` bit is always accumulated so a returning path is
never lost. `if`-without-`else`, loops, `try/catch`, inline assembly, and
unknown statements stay `(true, true)`.

`require`/`assert` are NOT terminators: solc connects them to BOTH the revert
node and a following node (probed: a `require(false)` helper does NOT prune), so
`require(false)`-style helpers correctly stay non-reverting here.

SOUNDNESS: this is acceptance-loosening. Marking a callee always-reverting
prunes a path in the pointer-return check, so a WRONG "always reverts" could
accept an invalid program. Because we only ever assert `(false, false)` on a
provable terminator and accumulate every `return`, we never over-accept.
Non-terminating recursion (`f(){ f(); }`) is treated by solc as reverting; we
conservatively do NOT (our monotone fixpoint from the empty set never marks it),
a sound residual over-reject on that exotic shape.
-/
mutual

def Stmt.revertFlowFuel :
    Nat -> List Name -> Solidity.Stmt -> Bool × Bool
  | 0, _, _ => (true, true)
  | fuel + 1, arNames, Solidity.Stmt.block body =>
      Stmts.revertFlowFuel fuel arNames body
  | fuel + 1, arNames, Solidity.Stmt.unchecked body =>
      Stmt.revertFlowFuel fuel arNames body
  | _ + 1, arNames, Solidity.Stmt.expr expr =>
      if Expr.isTerminalBuiltinCall expr ||
          Expr.isAlwaysRevertingCall arNames expr then
        (false, false)
      else
        (true, false)
  | _ + 1, _, Solidity.Stmt.revertCall _ => (false, false)
  | _ + 1, _, Solidity.Stmt.returnValues _ => (false, true)
  | fuel + 1, arNames,
      Solidity.Stmt.ifElse _ thenBranch (some elseBranch) =>
      let thenFlow := Stmt.revertFlowFuel fuel arNames thenBranch
      let elseFlow := Stmt.revertFlowFuel fuel arNames elseBranch
      (thenFlow.fst || elseFlow.fst, thenFlow.snd || elseFlow.snd)
  | fuel + 1, arNames,
      Solidity.Stmt.ifElse _ thenBranch none =>
      let thenFlow := Stmt.revertFlowFuel fuel arNames thenBranch
      (true, thenFlow.snd)
  | _ + 1, _, Solidity.Stmt.empty => (true, false)
  | _ + 1, _, Solidity.Stmt.varDecl _ _ => (true, false)
  | _ + 1, _, Solidity.Stmt.emitEvent _ => (true, false)
  | _ + 1, _, Solidity.Stmt.break => (false, true)
  | _ + 1, _, Solidity.Stmt.continue => (false, true)
  | _ + 1, _, _ => (true, true)

def Stmts.revertFlowFuel :
    Nat -> List Name -> List Solidity.Stmt -> Bool × Bool
  | 0, _, _ => (true, true)
  | _ + 1, _, [] => (true, false)
  | fuel + 1, arNames, stmt :: rest =>
      let headFlow := Stmt.revertFlowFuel fuel arNames stmt
      if headFlow.fst then
        let tailFlow := Stmts.revertFlowFuel fuel arNames rest
        (tailFlow.fst, headFlow.snd || tailFlow.snd)
      else
        (false, headFlow.snd)

end

def Stmt.alwaysRevertsFuel
    (fuel : Nat) (arNames : List Name) (stmt : Solidity.Stmt) : Bool :=
  let flow := Stmt.revertFlowFuel fuel arNames stmt
  !flow.fst && !flow.snd

-- CF2: one Kleene step of the always-reverts fixpoint. A name qualifies iff it
-- names at least one bodied function AND every bodied declaration with that
-- name always reverts under the current `known` oracle (sound under
-- overloading). `candidates` is the fixed list of all bodied-function names;
-- the filtered result grows monotonically as `known` grows.
def alwaysRevertStep
    (candidates : List Name) (decls : List (Name × Solidity.Stmt))
    (known : List Name) : List Name :=
  candidates.filter (fun nm =>
    decls.all (fun d =>
      d.fst != nm ||
        Stmt.alwaysRevertsFuel defaultPointerReturnFlowFuel known d.snd))

def alwaysRevertFixpoint
    (candidates : List Name) (decls : List (Name × Solidity.Stmt)) :
    Nat -> List Name -> List Name
  | 0, known => known
  | iter + 1, known =>
      let next := alwaysRevertStep candidates decls known
      if next.length <= known.length then known
      else alwaysRevertFixpoint candidates decls iter next

-- CF2: names of functions (from the given decls) that provably always revert.
def computeAlwaysRevertNames
    (fns : List Solidity.FunctionDecl) : List Name :=
  let decls : List (Name × Solidity.Stmt) :=
    fns.filterMap (fun fn =>
      match fn.name, fn.body with
      | some name, some body => some (name, body)
      | _, _ => none)
  let candidates := decls.map Prod.fst
  alwaysRevertFixpoint candidates decls (candidates.length + 1) []

def FunctionDecl.checkPointerReturnDefiniteAssignment
    (env : CheckEnv) (fn : Solidity.FunctionDecl)
    (body : Solidity.Stmt) : Except TypeError Unit := do
  let requirements := Parameters.pointerReturnRequirements env.types fn.returns
  if requirements.isEmpty then
    Except.ok ()
  else
    let flow :=
      FunctionDecl.pointerReturnFlowWithModifiersFuel
        defaultPointerReturnFlowFuel env requirements fn.modifiers body []
    require (!flow.unsafeReturn)
      (TypeError.invalidVariableDecl
        "storage or calldata return pointer can be accessed before assignment")
    match flow.normal? with
    | none => Except.ok ()
    | some assigned =>
        require (requirements.allAssigned assigned)
          (TypeError.invalidVariableDecl
            "storage or calldata return pointer can be returned before assignment")

def VarBinding.isUninitializedLocalPointer
    (binding : Solidity.VarBinding) : Bool :=
  binding.name.isSome && binding.ty.isSome &&
    (binding.location == some Solidity.DataLocation.storage ||
      binding.location == some Solidity.DataLocation.calldata)

def VarBindings.uninitializedLocalPointerNames :
    List Solidity.VarBinding -> List Name
  | [] => []
  | binding :: rest =>
      let tail := VarBindings.uninitializedLocalPointerNames rest
      if VarBinding.isUninitializedLocalPointer binding then
        match binding.name with
        | some name => name :: tail
        | none => tail
      else
        tail

def VarBindings.declaresName
    (bindings : List Solidity.VarBinding) (name : Name) : Bool :=
  bindings.any (fun binding => binding.name == some name)

def Parameters.declaresName
    (params : List Solidity.Parameter) (name : Name) : Bool :=
  params.any (fun param => param.name == some name)

def pointerLocalRequirements (name : Name) : PointerReturnRequirements :=
  { named := [name] }

mutual

def Stmt.pointerLocalFlowFuel :
    Nat -> Name -> PointerReturnAssigned ->
    Solidity.Stmt -> PointerReturnFlow
  | 0, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, assigned, Solidity.Stmt.empty =>
      { normal? := some assigned }
  | fuel + 1, name, assigned, Solidity.Stmt.block body =>
      Stmts.pointerLocalFlowFuel fuel name assigned body
  | fuel + 1, name, assigned,
      Solidity.Stmt.varDecl _ init? =>
      match init? with
      | some init =>
          exprFlowToNormal
            (Expr.pointerReturnFlowFuel fuel
              (pointerLocalRequirements name) assigned init)
      | none => { normal? := some assigned }
  | fuel + 1, name, assigned, Solidity.Stmt.expr expr =>
      let flow :=
        Expr.pointerReturnFlowFuel fuel
          (pointerLocalRequirements name) assigned expr
      if Expr.isTerminalBuiltinCall expr then
        { unsafeReturn := flow.unsafeRead }
      else
        exprFlowToNormal flow
  | fuel + 1, name, assigned,
      Solidity.Stmt.ifElse cond thenBranch elseBranch =>
      let requirements := pointerLocalRequirements name
      let condFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned cond
      let thenFlow :=
        Stmt.pointerLocalFlowFuel fuel name condFlow.assigned thenBranch
      let elseFlow :=
        match elseBranch with
        | some branch =>
            Stmt.pointerLocalFlowFuel fuel name condFlow.assigned branch
        | none => { normal? := some condFlow.assigned }
      let branches := thenFlow.mergeBranches elseFlow
      { branches with
        unsafeReturn := condFlow.unsafeRead || branches.unsafeReturn }
  | fuel + 1, name, assigned,
      Solidity.Stmt.whileLoop cond body =>
      let requirements := pointerLocalRequirements name
      let condFlow :=
        Expr.pointerReturnFlowFuel fuel requirements assigned cond
      let bodyFlow :=
        Stmt.pointerLocalFlowFuel fuel name condFlow.assigned body
      { normal? := some condFlow.assigned
        unsafeReturn := condFlow.unsafeRead || bodyFlow.unsafeReturn }
  | fuel + 1, name, assigned,
      Solidity.Stmt.doWhile body cond =>
      let bodyFlow := Stmt.pointerLocalFlowFuel fuel name assigned body
      let reachesCond :=
        mergePointerReturnState bodyFlow.normal? bodyFlow.continues?
      let condFlow? :=
        reachesCond.map (fun state =>
          Expr.pointerReturnFlowFuel fuel
            (pointerLocalRequirements name) state cond)
      let normalFromCond := condFlow?.map PointerExprFlow.assigned
      { normal? := mergePointerReturnState bodyFlow.breaks? normalFromCond
        unsafeReturn := bodyFlow.unsafeReturn ||
          condFlow?.any PointerExprFlow.unsafeRead }
  | fuel + 1, name, assigned,
      Solidity.Stmt.forLoop init cond post body =>
      match init with
      | some (Solidity.Stmt.varDecl bindings initExpr?) =>
          if VarBindings.declaresName bindings name then
            match initExpr? with
            | some initExpr =>
                exprFlowToNormal
                  (Expr.pointerReturnFlowFuel fuel
                    (pointerLocalRequirements name) assigned initExpr)
            | none => { normal? := some assigned }
          else
            let initFlow :=
              Stmt.pointerLocalFlowFuel fuel name assigned
                (Solidity.Stmt.varDecl bindings initExpr?)
            match initFlow.normal? with
            | none => initFlow
            | some afterInit =>
                let condFlow :=
                  match cond with
                  | some expr =>
                      Expr.pointerReturnFlowFuel fuel
                        (pointerLocalRequirements name) afterInit expr
                  | none => { assigned := afterInit }
                let bodyFlow :=
                  Stmt.pointerLocalFlowFuel fuel name condFlow.assigned body
                let postInput :=
                  mergePointerReturnState bodyFlow.normal?
                    bodyFlow.continues?
                let postUnsafe :=
                  match postInput, post with
                  | some state, some expr =>
                      (Expr.pointerReturnFlowFuel fuel
                        (pointerLocalRequirements name) state expr).unsafeRead
                  | _, _ => false
                { normal? := some condFlow.assigned
                  breaks? := initFlow.breaks?
                  continues? := initFlow.continues?
                  unsafeReturn := initFlow.unsafeReturn ||
                    condFlow.unsafeRead || bodyFlow.unsafeReturn || postUnsafe }
      | initStmt? =>
          let initFlow :=
            match initStmt? with
            | some initStmt =>
                Stmt.pointerLocalFlowFuel fuel name assigned initStmt
            | none => { normal? := some assigned }
          match initFlow.normal? with
          | none => initFlow
          | some afterInit =>
              let condFlow :=
                match cond with
                | some expr =>
                    Expr.pointerReturnFlowFuel fuel
                      (pointerLocalRequirements name) afterInit expr
                | none => { assigned := afterInit }
              let bodyFlow :=
                Stmt.pointerLocalFlowFuel fuel name condFlow.assigned body
              let postInput :=
                mergePointerReturnState bodyFlow.normal?
                  bodyFlow.continues?
              let postUnsafe :=
                match postInput, post with
                | some state, some expr =>
                    (Expr.pointerReturnFlowFuel fuel
                      (pointerLocalRequirements name) state expr).unsafeRead
                | _, _ => false
              { normal? := some condFlow.assigned
                breaks? := initFlow.breaks?
                continues? := initFlow.continues?
                unsafeReturn := initFlow.unsafeReturn ||
                  condFlow.unsafeRead || bodyFlow.unsafeReturn || postUnsafe }
  | fuel + 1, name, assigned,
      Solidity.Stmt.tryCatch expr clauses =>
      let exprFlow :=
        Expr.pointerReturnFlowFuel fuel
          (pointerLocalRequirements name) assigned expr
      let catches :=
        CatchClauses.pointerLocalFlowFuel fuel name exprFlow.assigned clauses
      let success : PointerReturnFlow :=
        { normal? := some exprFlow.assigned }
      let merged := success.mergeBranches catches
      { merged with
        unsafeReturn := exprFlow.unsafeRead || merged.unsafeReturn }
  | fuel + 1, name, assigned,
      Solidity.Stmt.tryCatchReturns expr returns success clauses =>
      let exprFlow :=
        Expr.pointerReturnFlowFuel fuel
          (pointerLocalRequirements name) assigned expr
      let successFlow : PointerReturnFlow :=
        if Parameters.declaresName returns name then
          { normal? := some exprFlow.assigned }
        else
          Stmt.pointerLocalFlowFuel fuel name exprFlow.assigned success
      let catches :=
        CatchClauses.pointerLocalFlowFuel fuel name exprFlow.assigned clauses
      let merged := successFlow.mergeBranches catches
      { merged with
        unsafeReturn := exprFlow.unsafeRead || merged.unsafeReturn }
  | fuel + 1, name, assigned,
      Solidity.Stmt.emitEvent expr =>
      exprFlowToNormal
        (Expr.pointerReturnFlowFuel fuel
          (pointerLocalRequirements name) assigned expr)
  | fuel + 1, name, assigned,
      Solidity.Stmt.revertCall expr =>
      let flow :=
        Expr.pointerReturnFlowFuel fuel
          (pointerLocalRequirements name) assigned expr
      { unsafeReturn := flow.unsafeRead }
  | fuel + 1, name, assigned,
      Solidity.Stmt.returnValues expr? =>
      match expr? with
      | some expr =>
          let flow :=
            Expr.pointerReturnFlowFuel fuel
              (pointerLocalRequirements name) assigned expr
          { unsafeReturn := flow.unsafeRead }
      | none => {}
  | _ + 1, _, assigned, Solidity.Stmt.break =>
      { breaks? := some assigned }
  | _ + 1, _, assigned, Solidity.Stmt.continue =>
      { continues? := some assigned }
  | fuel + 1, name, assigned,
      Solidity.Stmt.unchecked body =>
      Stmt.pointerLocalFlowFuel fuel name assigned body
  | _ + 1, _, _, Solidity.Stmt.inlineAssembly _ =>
      { unsafeReturn := true }
  | _ + 1, _, assigned, Solidity.Stmt.modifierPlaceholder =>
      { normal? := some assigned }

def Stmts.pointerLocalFlowFuel :
    Nat -> Name -> PointerReturnAssigned ->
    List Solidity.Stmt -> PointerReturnFlow
  | 0, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, assigned, [] => { normal? := some assigned }
  | fuel + 1, name, assigned, stmt :: rest =>
      match stmt with
      | Solidity.Stmt.varDecl bindings init? =>
          if VarBindings.declaresName bindings name then
            match init? with
            | some init =>
                exprFlowToNormal
                  (Expr.pointerReturnFlowFuel fuel
                    (pointerLocalRequirements name) assigned init)
            | none => { normal? := some assigned }
          else
            let head := Stmt.pointerLocalFlowFuel fuel name assigned stmt
            let tail :=
              match head.normal? with
              | some state =>
                  Stmts.pointerLocalFlowFuel fuel name state rest
              | none => {}
            { normal? := tail.normal?
              breaks? := mergePointerReturnState head.breaks? tail.breaks?
              continues? :=
                mergePointerReturnState head.continues? tail.continues?
              unsafeReturn := head.unsafeReturn || tail.unsafeReturn }
      | _ =>
          let head := Stmt.pointerLocalFlowFuel fuel name assigned stmt
          let tail :=
            match head.normal? with
            | some state => Stmts.pointerLocalFlowFuel fuel name state rest
            | none => {}
          { normal? := tail.normal?
            breaks? := mergePointerReturnState head.breaks? tail.breaks?
            continues? :=
              mergePointerReturnState head.continues? tail.continues?
            unsafeReturn := head.unsafeReturn || tail.unsafeReturn }

def CatchClauses.pointerLocalFlowFuel :
    Nat -> Name -> PointerReturnAssigned ->
    List Solidity.CatchClause -> PointerReturnFlow
  | 0, _, _, _ => { unsafeReturn := true }
  | _ + 1, _, _, [] => {}
  | fuel + 1, name, assigned,
      Solidity.CatchClause.clause _ params body :: rest =>
      let head : PointerReturnFlow :=
        if Parameters.declaresName params name then
          { normal? := some assigned }
        else
          Stmt.pointerLocalFlowFuel fuel name assigned body
      let tail :=
        CatchClauses.pointerLocalFlowFuel fuel name assigned rest
      head.mergeBranches tail

end

def checkPointerLocalNamesInSuffix
    (names : List Name) (suffix : List Solidity.Stmt) :
    Except TypeError Unit := do
  match names with
  | [] => Except.ok ()
  | name :: rest =>
      let flow :=
        Stmts.pointerLocalFlowFuel defaultPointerReturnFlowFuel name [] suffix
      require (!flow.unsafeReturn)
        (TypeError.invalidVariableDecl
          "storage or calldata local pointer can be accessed before assignment")
      checkPointerLocalNamesInSuffix rest suffix

mutual

def Stmt.checkLocalPointerDefiniteAssignmentFuel :
    Nat -> Solidity.Stmt -> Except TypeError Unit
  | 0, _ =>
      Except.error
        (TypeError.invalidVariableDecl
          "local pointer definite-assignment analysis exhausted")
  | fuel + 1, Solidity.Stmt.block body =>
      Stmts.checkLocalPointerDefiniteAssignmentFuel fuel body
  | fuel + 1, Solidity.Stmt.ifElse _ thenBranch elseBranch => do
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel thenBranch
      match elseBranch with
      | some branch =>
          Stmt.checkLocalPointerDefiniteAssignmentFuel fuel branch
      | none => Except.ok ()
  | fuel + 1, Solidity.Stmt.whileLoop _ body =>
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel body
  | fuel + 1, Solidity.Stmt.doWhile body _ =>
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel body
  | fuel + 1, Solidity.Stmt.forLoop init cond post body => do
      match init with
      | some (Solidity.Stmt.varDecl bindings none) =>
          let names :=
            VarBindings.uninitializedLocalPointerNames bindings
          checkPointerLocalNamesInSuffix names
            [Solidity.Stmt.forLoop none cond post body]
      | some initStmt =>
          Stmt.checkLocalPointerDefiniteAssignmentFuel fuel initStmt
      | none => Except.ok ()
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel body
  | fuel + 1, Solidity.Stmt.tryCatch _ clauses =>
      CatchClauses.checkLocalPointerDefiniteAssignmentFuel fuel clauses
  | fuel + 1,
      Solidity.Stmt.tryCatchReturns _ _ success clauses => do
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel success
      CatchClauses.checkLocalPointerDefiniteAssignmentFuel fuel clauses
  | fuel + 1, Solidity.Stmt.unchecked body =>
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel body
  | _ + 1, _ => Except.ok ()

def Stmts.checkLocalPointerDefiniteAssignmentFuel :
    Nat -> List Solidity.Stmt -> Except TypeError Unit
  | 0, _ =>
      Except.error
        (TypeError.invalidVariableDecl
          "local pointer definite-assignment analysis exhausted")
  | _ + 1, [] => Except.ok ()
  | fuel + 1, stmt :: rest => do
      match stmt with
      | Solidity.Stmt.varDecl bindings none =>
          checkPointerLocalNamesInSuffix
            (VarBindings.uninitializedLocalPointerNames bindings) rest
      | _ => Except.ok ()
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel stmt
      Stmts.checkLocalPointerDefiniteAssignmentFuel fuel rest

def CatchClauses.checkLocalPointerDefiniteAssignmentFuel :
    Nat -> List Solidity.CatchClause -> Except TypeError Unit
  | 0, _ =>
      Except.error
        (TypeError.invalidVariableDecl
          "local pointer definite-assignment analysis exhausted")
  | _ + 1, [] => Except.ok ()
  | fuel + 1,
      Solidity.CatchClause.clause _ _ body :: rest => do
      Stmt.checkLocalPointerDefiniteAssignmentFuel fuel body
      CatchClauses.checkLocalPointerDefiniteAssignmentFuel fuel rest

end

def Stmt.checkLocalPointerDefiniteAssignment
    (body : Solidity.Stmt) : Except TypeError Unit :=
  Stmt.checkLocalPointerDefiniteAssignmentFuel
    defaultPointerReturnFlowFuel body

mutual

def Stmt.containsModifierPlaceholderFuel :
    Nat -> Solidity.Stmt -> Bool
  | 0, _ => false
  | _ + 1, Solidity.Stmt.modifierPlaceholder => true
  | fuel + 1, Solidity.Stmt.block body =>
      Stmts.containsModifierPlaceholderFuel fuel body
  | fuel + 1, Solidity.Stmt.ifElse _ thenBranch elseBranch =>
      Stmt.containsModifierPlaceholderFuel fuel thenBranch ||
        elseBranch.any (Stmt.containsModifierPlaceholderFuel fuel)
  | fuel + 1, Solidity.Stmt.whileLoop _ body =>
      Stmt.containsModifierPlaceholderFuel fuel body
  | fuel + 1, Solidity.Stmt.doWhile body _ =>
      Stmt.containsModifierPlaceholderFuel fuel body
  | fuel + 1, Solidity.Stmt.forLoop init _ _ body =>
      init.any (Stmt.containsModifierPlaceholderFuel fuel) ||
        Stmt.containsModifierPlaceholderFuel fuel body
  | fuel + 1, Solidity.Stmt.tryCatch _ clauses =>
      CatchClauses.containsModifierPlaceholderFuel fuel clauses
  | fuel + 1, Solidity.Stmt.tryCatchReturns _ _ success clauses =>
      Stmt.containsModifierPlaceholderFuel fuel success ||
        CatchClauses.containsModifierPlaceholderFuel fuel clauses
  | fuel + 1, Solidity.Stmt.unchecked body =>
      Stmt.containsModifierPlaceholderFuel fuel body
  | _ + 1, _ => false

def Stmts.containsModifierPlaceholderFuel :
    Nat -> List Solidity.Stmt -> Bool
  | 0, _ => false
  | _ + 1, [] => false
  | fuel + 1, stmt :: rest =>
      Stmt.containsModifierPlaceholderFuel fuel stmt ||
        Stmts.containsModifierPlaceholderFuel fuel rest

def CatchClauses.containsModifierPlaceholderFuel :
    Nat -> List Solidity.CatchClause -> Bool
  | 0, _ => false
  | _ + 1, [] => false
  | fuel + 1, Solidity.CatchClause.clause _ _ body :: rest =>
      Stmt.containsModifierPlaceholderFuel fuel body ||
        CatchClauses.containsModifierPlaceholderFuel fuel rest

end

def Stmt.containsModifierPlaceholder
    (stmt : Solidity.Stmt) : Bool :=
  Stmt.containsModifierPlaceholderFuel 4096 stmt

def FunctionDecl.check (baseEnv : CheckEnv)
    (fn : Solidity.FunctionDecl) : Except TypeError Unit := do
  FunctionDecl.checkHeader baseEnv fn
  Parameters.check baseEnv.types fn.params
  Parameters.check baseEnv.types fn.returns
  let localNames := (Parameters.namedTypes fn.params).map Prod.fst ++
    (Parameters.namedTypes fn.returns).map Prod.fst
  ensureUniqueNames "function local" localNames
  let qualifyLocalEntry (entry : Name × Ty × Bool) : Name × Ty × Bool :=
    (entry.1, baseEnv.qualifyCurrentLocalUserTypes entry.2.1, entry.2.2)
  let locals :=
    (Parameters.namedTypeStorageRefs baseEnv.types fn.returns ++
      Parameters.namedTypeStorageRefs baseEnv.types fn.params).map
        qualifyLocalEntry
  let dataLocations :=
    Parameters.namedDataLocations baseEnv.types fn.returns ++
      Parameters.namedDataLocations baseEnv.types fn.params
  let env :=
    { baseEnv with
      vars := locals.map (fun entry => (entry.1, entry.2.1)) ++ baseEnv.vars
      localNames := locals.map Prod.fst ++ baseEnv.localNames
      localStorageRefs :=
        (locals.filterMap
          (fun entry =>
            if entry.2.2 then some entry.1 else none)) ++
          baseEnv.localStorageRefs
      localDataLocations := dataLocations ++ baseEnv.localDataLocations
      currentMutability := some fn.mutability
      currentVisibility := fn.visibility
      returnTys :=
        (Parameters.tys fn.returns).map baseEnv.qualifyCurrentLocalUserTypes
      returnNames := fn.returns.map Solidity.Parameter.name
      returnStorageRefs := Parameters.storageLocationFlags fn.returns
      returnDataLocations := Parameters.dataLocations fn.returns
      inConstructor := fn.kind == Solidity.FunctionKind.constructor
      inReceive := fn.kind == Solidity.FunctionKind.receive }
  ModifierInvocations.check env
    (fn.kind == Solidity.FunctionKind.constructor)
    fn.modifiers
  match fn.body with
  | none => Except.ok ()
  | some body =>
      ModifierInvocations.checkBodiesForCaller env fn.modifiers
      let _ ← checkStmt env body
      Stmt.checkLocalPointerDefiniteAssignment body
      FunctionDecl.checkPointerReturnDefiniteAssignment env fn body
      Except.ok ()

def ModifierDecl.check (baseEnv : CheckEnv)
    (modifier : Solidity.ModifierDecl) : Except TypeError Unit := do
  Parameters.check baseEnv.types modifier.params
  ensureUniqueNames "modifier parameter"
    ((Parameters.namedTypes modifier.params).map Prod.fst)
  if baseEnv.inLibrary then
    require (!modifier.virtual)
      (TypeError.invalidFunctionHeader "library modifier is virtual")
  else
    Except.ok ()
  match modifier.body with
  | none =>
      require modifier.virtual
        (TypeError.invalidFunctionHeader
          "modifier without implementation is not virtual")
  | some body =>
      require (Stmt.containsModifierPlaceholder body)
        (TypeError.invalidFunctionHeader
          "modifier body does not contain a placeholder")
      let locals := Parameters.namedTypeStorageRefs baseEnv.types modifier.params
      let dataLocations :=
        Parameters.namedDataLocations baseEnv.types modifier.params
      let env :=
        { baseEnv.enterModifier with
          vars := locals.map (fun entry => (entry.1, entry.2.1)) ++
            baseEnv.vars
          localNames := locals.map Prod.fst ++ baseEnv.localNames
          localStorageRefs :=
            (locals.filterMap
              (fun entry =>
                if entry.2.2 then some entry.1 else none)) ++
              baseEnv.localStorageRefs
          localDataLocations := dataLocations ++ baseEnv.localDataLocations
          returnTys := []
          returnNames := [] }
      let _ ← checkStmt env body
      Stmt.checkLocalPointerDefiniteAssignment body
      Except.ok ()

def EventParam.indexedWeight
    (param : Solidity.EventParam) : Nat :=
  if param.indexed then 1 else 0

def EventParams.indexedCount :
    List Solidity.EventParam -> Nat
  | [] => 0
  | param :: rest =>
      EventParam.indexedWeight param + EventParams.indexedCount rest

def EventDecl.indexedLimit
    (event : Solidity.EventDecl) : Nat :=
  if event.anonymous then 4 else 3

def EventParam.check (env : CheckEnv)
    (param : Solidity.EventParam) :
    Except TypeError Unit := do
  checkTy env.types param.ty
  require (TypeContext.isAbiEncodable env.types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (TypeContext.abiCoderSupports env.types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (!Ty.containsMapping env.types 64 param.ty)
    (TypeError.invalidAbiType param.ty)

def EventParams.check (env : CheckEnv) :
    List Solidity.EventParam -> Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      EventParam.check env param
      EventParams.check env rest

def EventDecl.check (env : CheckEnv)
    (event : Solidity.EventDecl) :
    Except TypeError Unit := do
  EventParams.check env event.params
  ensureUniqueNames "event parameter"
    (event.params.filterMap Solidity.EventParam.name)
  require (EventParams.indexedCount event.params <=
      EventDecl.indexedLimit event)
    (TypeError.invalidEventHeader event.name
      "too many indexed event parameters")

def Parameter.checkErrorParam (types : TypeContext)
    (param : Solidity.Parameter) : Except TypeError Unit := do
  checkTy types param.ty
  require param.location.isNone
    (TypeError.invalidDataLocation param.ty param.location)
  require (TypeContext.isAbiEncodable types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (TypeContext.abiCoderSupports types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (!Ty.containsMapping types 64 param.ty)
    (TypeError.invalidAbiType param.ty)

def Parameters.checkErrorParams (types : TypeContext) :
    List Solidity.Parameter -> Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      Parameter.checkErrorParam types param
      Parameters.checkErrorParams types rest

def ErrorDecl.check (env : CheckEnv)
    (err : Solidity.ErrorDecl) :
    Except TypeError Unit := do
  require (!(err.name == "Error" || err.name == "Panic"))
    (TypeError.invalidErrorHeader err.name
      "built-in error cannot be redefined")
  ensureUniqueNames "error parameter"
    (err.params.filterMap Solidity.Parameter.name)
  Parameters.checkErrorParams env.types err.params

def pathInList (target : Path) : List Path -> Bool :=
  TypeContext.pathIn target

mutual

def Ty.hasForbiddenStructReferenceCycle (types : TypeContext)
    (targets : List Path) : Nat -> Ty -> Bool
  | 0, _ => false
  | fuel + 1, Solidity.Ty.user path =>
      if pathInList path targets then
        true
      else
        match types.lookupStruct? path with
        | some decl =>
            StructDecl.hasForbiddenStructReferenceCycle types targets fuel
              decl
        | none => false
  | fuel + 1, Solidity.Ty.array element (some _) =>
      Ty.hasForbiddenStructReferenceCycle types targets fuel element
  | fuel + 1, Solidity.Ty.tuple tys =>
      Tys.hasForbiddenStructReferenceCycle types targets fuel tys
  | _, _ => false

def Tys.hasForbiddenStructReferenceCycle (types : TypeContext)
    (targets : List Path) (fuel : Nat) : List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.hasForbiddenStructReferenceCycle types targets fuel ty ||
        Tys.hasForbiddenStructReferenceCycle types targets fuel rest

def StructField.hasForbiddenStructReferenceCycle (types : TypeContext)
    (targets : List Path) (fuel : Nat)
    (field : Solidity.StructField) : Bool :=
  Ty.hasForbiddenStructReferenceCycle types targets fuel field.ty

def StructFields.hasForbiddenStructReferenceCycle (types : TypeContext)
    (targets : List Path) (fuel : Nat) :
    List Solidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      StructField.hasForbiddenStructReferenceCycle types targets fuel field ||
        StructFields.hasForbiddenStructReferenceCycle types targets fuel rest

def StructDecl.hasForbiddenStructReferenceCycle (types : TypeContext)
    (targets : List Path) (fuel : Nat)
    (decl : Solidity.StructDecl) : Bool :=
  StructFields.hasForbiddenStructReferenceCycle types targets fuel decl.fields

end

def StructField.check (env : CheckEnv) (selfPaths : List Path)
    (field : Solidity.StructField) : Except TypeError Unit := do
  checkTy env.types field.ty
  require (!Ty.containsLibraryType env.types 64 field.ty)
    (TypeError.invalidType field.ty)
  require
    (!Ty.hasForbiddenStructReferenceCycle env.types selfPaths 64 field.ty)
    (TypeError.invalidType field.ty)

def StructDecl.check (env : CheckEnv) (selfPaths : List Path)
    (decl : Solidity.StructDecl) : Except TypeError Unit := do
  ensureUniqueNames "struct field" (decl.fields.map Solidity.StructField.name)
  let rec checkFields :
      List Solidity.StructField -> Except TypeError Unit
    | [] => Except.ok ()
    | field :: rest => do
        StructField.check env selfPaths field
        checkFields rest
  checkFields decl.fields

def EnumDecl.check (decl : Solidity.EnumDecl) :
    Except TypeError Unit := do
  require (decl.cases.length > 0 && decl.cases.length <= 256)
    (TypeError.invalidEnum decl.name)
  ensureUniqueNames "enum case" decl.cases

def UserValueTypeDecl.check (env : CheckEnv)
    (decl : Solidity.UserValueTypeDecl) :
    Except TypeError Unit := do
  checkTy env.types decl.underlying
  require (Ty.isBuiltInValueTypeShape decl.underlying)
    (TypeError.invalidUserValueType decl.name decl.underlying)

def UsingFunction.check (env : CheckEnv)
    (target? : Option Ty) (global : Bool)
    (binding : Solidity.UsingFunction) : Except TypeError Unit := do
  let (libraryPath, functionName) ←
    match Solidity.Executable.pathInitLast? binding.function with
    | some parts => Except.ok parts
    | none => Except.error (TypeError.unknownFunction "")
  match binding.operator? with
  | some operator =>
      require global
        (TypeError.invalidContractHeader
          "using operator binding must be global")
      require libraryPath.segments.isEmpty
        (TypeError.invalidContractHeader
          "using operator binding must name a free function")
      let targetTy ←
        match target? with
        | some ty => Except.ok ty
        | none =>
            Except.error
              (TypeError.invalidContractHeader
                "using operator binding requires a target type")
      match targetTy with
      | Solidity.Ty.user path =>
          require (env.types.isUserValueTypePath path)
            (TypeError.invalidContractHeader
              "using operator binding target is not a user value type")
      | _ =>
          Except.error
            (TypeError.invalidContractHeader
              "using operator binding target is not a user value type")
      require (UsingOperator.userDefinedResultTy? targetTy operator).isSome
        (TypeError.invalidContractHeader
          "unsupported using operator binding")
      let candidates :=
        ((FunctionSigs.nonPrivate env.functions).filter
          (fun sig =>
            sig.name == functionName &&
              sig.matchesUserDefinedOperatorDecl targetTy operator))
      require (!candidates.isEmpty) (TypeError.unknownFunction functionName)
  | none =>
      let candidates ←
        if libraryPath.segments.isEmpty then
          Except.ok
            ((FunctionSigs.nonPrivate env.functions).filter
              (fun sig => sig.name == functionName))
        else
          let libraryDecl ←
            match env.types.lookupContractDecl? libraryPath with
            | some libraryDecl => Except.ok libraryDecl
            | none => Except.error (TypeError.unknownType libraryPath)
          require (libraryDecl.kind == Solidity.ContractKind.library)
            (TypeError.invalidContractHeader "using target is not a library")
          Except.ok
            ((FunctionSigs.nonPrivate
              (ContractDecl.directFunctionSigsQualifiedLocalTypes
                libraryDecl)).filter
                (fun sig => sig.name == functionName))
      require (!candidates.isEmpty) (TypeError.unknownFunction functionName)

def UsingFunctions.check (env : CheckEnv)
    (target? : Option Ty) (global : Bool) :
    List Solidity.UsingFunction -> Except TypeError Unit
  | [] => Except.ok ()
  | binding :: rest => do
      UsingFunction.check env target? global binding
      UsingFunctions.check env target? global rest

def UsingDecl.checkCore (env : CheckEnv)
    (decl : Solidity.UsingDecl) : Except TypeError Unit := do
  if decl.functions.isEmpty then
    let libraryDecl ←
      match env.types.lookupContractDecl? decl.library with
      | some libraryDecl => Except.ok libraryDecl
      | none => Except.error (TypeError.unknownType decl.library)
    require (libraryDecl.kind == Solidity.ContractKind.library)
      (TypeError.invalidContractHeader "using target is not a library")
  else
    UsingFunctions.check env decl.target decl.global decl.functions
  match decl.target with
  | some ty => do
      checkTy env.types ty
      require (!Ty.containsLibraryType env.types 64 ty)
        (TypeError.invalidType ty)
  | none => Except.ok ()

def UsingDecl.checkContractLevel (env : CheckEnv)
    (decl : Solidity.UsingDecl) : Except TypeError Unit := do
  UsingDecl.checkCore env decl
  require (!decl.global)
    (TypeError.invalidContractHeader
      "global using directive is only allowed at file scope")

def UsingDecl.checkFileLevel (env : CheckEnv)
    (decl : Solidity.UsingDecl) : Except TypeError Unit := do
  UsingDecl.checkCore env decl
  require decl.target.isSome
    (TypeError.invalidContractHeader
      "file-level using directive requires an explicit type")
  if decl.global then
    -- solc `TypeChecker.cpp:4006-4021`: a file-level `global` directive admits
    -- ANY same-source-unit user-defined type whose `typeDefinition()` is
    -- non-null — struct, enum, or UDVT (a *contract* type has no
    -- `typeDefinition()` and is rejected with 8841; so are built-ins and
    -- cross-file types). The UDVT-only restriction is kept ONLY for operator
    -- bindings, enforced separately in `UsingFunction.check`.
    match decl.target with
    | some (Solidity.Ty.user path) =>
        require (env.types.isStructPath path || env.types.isEnumPath path ||
            env.types.isUserValueTypePath path)
          (TypeError.invalidContractHeader
            "global using directive target is not a user-defined type")
    | _ =>
        Except.error
          (TypeError.invalidContractHeader
            "global using directive target is not a user-defined type")
  else
    Except.ok ()

/-- The `(operator, target-type)` pairs a using directive binds as operators. -/
def UsingDecl.operatorBindings (decl : Solidity.UsingDecl) :
    List (Solidity.UsingOperator × Ty) :=
  match decl.target with
  | some ty =>
      decl.functions.filterMap (fun binding =>
        match binding.operator? with
        | some operator => some (operator, ty)
        | none => none)
  | none => []

/-- solc `TypeChecker.cpp:4229-4254` (error 4705): binding the same operator for
the same operand type more than once among the directives visible in scope is a
directive-level error, independent of whether the operator is ever applied.
Operator bindings must be `global` (file level), so scanning the file-level
using directives collects every binding in scope. -/
def UsingDecls.checkNoDuplicateOperatorBindings
    (decls : List Solidity.UsingDecl) : Except TypeError Unit :=
  let pairs := decls.flatMap UsingDecl.operatorBindings
  let rec go : List (Solidity.UsingOperator × Ty) -> Except TypeError Unit
    | [] => Except.ok ()
    | pair :: rest =>
        if rest.contains pair then
          Except.error
            (TypeError.invalidContractHeader
              "duplicate using operator binding for the same operator and type")
        else
          go rest
  go pairs

def ContractItem.stateVar? :
    Solidity.ContractItem -> Option Solidity.StateVarDecl
  | Solidity.ContractItem.stateVar decl => some decl
  | _ => none

def ContractItem.function? :
    Solidity.ContractItem -> Option Solidity.FunctionDecl
  | Solidity.ContractItem.function decl => some decl
  | _ => none

def ContractItem.modifier? :
    Solidity.ContractItem -> Option Solidity.ModifierDecl
  | Solidity.ContractItem.modifierDecl decl => some decl
  | _ => none

def ContractItem.event? :
    Solidity.ContractItem -> Option Solidity.EventDecl
  | Solidity.ContractItem.eventDecl decl => some decl
  | _ => none

def ContractItem.error? :
    Solidity.ContractItem -> Option Solidity.ErrorDecl
  | Solidity.ContractItem.errorDecl decl => some decl
  | _ => none

def ContractItem.struct? :
    Solidity.ContractItem -> Option Solidity.StructDecl
  | Solidity.ContractItem.structDecl decl => some decl
  | _ => none

def ContractItem.enum? :
    Solidity.ContractItem -> Option Solidity.EnumDecl
  | Solidity.ContractItem.enumDecl decl => some decl
  | _ => none

def ContractItem.userValueType? :
    Solidity.ContractItem ->
    Option Solidity.UserValueTypeDecl
  | Solidity.ContractItem.userValueTypeDecl decl => some decl
  | _ => none

def ContractItem.using? :
    Solidity.ContractItem -> Option Solidity.UsingDecl
  | Solidity.ContractItem.usingDecl decl => some decl
  | _ => none

def ContractDecl.eventSigs
    (decl : Solidity.ContractDecl) : List EventSig :=
  (decl.items.filterMap ContractItem.event?).map EventDecl.signature

def ContractDecl.errorSigs
    (decl : Solidity.ContractDecl) : List ErrorSig :=
  (decl.items.filterMap ContractItem.error?).map ErrorDecl.signature

def ContractDecl.eventNames
    (decl : Solidity.ContractDecl) : List Name :=
  (decl.items.filterMap ContractItem.event?).map
    Solidity.EventDecl.name

def ContractDecl.nonEventTypeNames
    (decl : Solidity.ContractDecl) : List Name :=
  (decl.items.filterMap ContractItem.error?).map
      Solidity.ErrorDecl.name ++
    (decl.items.filterMap ContractItem.struct?).map
      Solidity.StructDecl.name ++
    (decl.items.filterMap ContractItem.enum?).map
      Solidity.EnumDecl.name ++
    (decl.items.filterMap ContractItem.userValueType?).map
      Solidity.UserValueTypeDecl.name

def ContractDecls.eventSigs (types : TypeContext) :
    List Path -> List EventSig
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.eventSigs decl ++ ContractDecls.eventSigs types rest
      | none => ContractDecls.eventSigs types rest

def ContractDecls.errorSigs (types : TypeContext) :
    List Path -> List ErrorSig
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.errorSigs decl ++ ContractDecls.errorSigs types rest
      | none => ContractDecls.errorSigs types rest

def ContractDecls.eventNames (types : TypeContext) :
    List Path -> List Name
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.eventNames decl ++ ContractDecls.eventNames types rest
      | none => ContractDecls.eventNames types rest

def ContractDecls.nonEventTypeNames (types : TypeContext) :
    List Path -> List Name
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.nonEventTypeNames decl ++
            ContractDecls.nonEventTypeNames types rest
      | none => ContractDecls.nonEventTypeNames types rest

def ContractDecl.addNestedTypesToContext
    (types : TypeContext) (decl : Solidity.ContractDecl) :
    TypeContext :=
  types.withContractTypes decl.name
    (decl.items.filterMap ContractItem.struct?)
    (decl.items.filterMap ContractItem.enum?)
    (decl.items.filterMap ContractItem.userValueType?)

def ContractDecls.addNestedTypesToContext :
    TypeContext -> List Solidity.ContractDecl -> TypeContext
  | types, [] => types
  | types, decl :: rest =>
      ContractDecl.addNestedTypesToContext
        (ContractDecls.addNestedTypesToContext types rest) decl

def StateVarDecl.isConstant (decl : Solidity.StateVarDecl) : Bool :=
  decl.mutability == Solidity.VarMutability.constant

def FunctionDecl.hasBody (fn : Solidity.FunctionDecl) : Bool :=
  match fn.body with
  | some _ => true
  | none => false

def FunctionDecl.isOrdinary (fn : Solidity.FunctionDecl) : Bool :=
  fn.kind == Solidity.FunctionKind.function

def FunctionDecl.declaredName? (fn : Solidity.FunctionDecl) :
    Option Name :=
  match fn.kind, fn.name with
  | Solidity.FunctionKind.function, some name => some name
  | _, _ => none

def FunctionDecl.isInterfaceDeclaration
    (fn : Solidity.FunctionDecl) : Bool :=
  match fn.kind with
  | Solidity.FunctionKind.function =>
      !FunctionDecl.hasBody fn &&
        fn.visibility == some Solidity.Visibility.external_
  | Solidity.FunctionKind.receive
  | Solidity.FunctionKind.fallback =>
      !FunctionDecl.hasBody fn &&
        fn.visibility == some Solidity.Visibility.external_
  | Solidity.FunctionKind.constructor => false

def FunctionDecl.isConstructor
    (fn : Solidity.FunctionDecl) : Bool :=
  fn.kind == Solidity.FunctionKind.constructor

def FunctionDecl.isConstructorLike
    (fn : Solidity.FunctionDecl) : Bool :=
  fn.kind == Solidity.FunctionKind.constructor ||
    fn.kind == Solidity.FunctionKind.receive ||
    fn.kind == Solidity.FunctionKind.fallback

def FunctionDecl.requiresImplementation
    (fn : Solidity.FunctionDecl) : Bool :=
  !FunctionDecl.hasBody fn

def ModifierDecl.hasBody (modifier : Solidity.ModifierDecl) : Bool :=
  match modifier.body with
  | some _ => true
  | none => false

def ModifierDecl.requiresImplementation
    (modifier : Solidity.ModifierDecl) : Bool :=
  !ModifierDecl.hasBody modifier

def Functions.anyMissingBody :
    List Solidity.FunctionDecl -> Bool
  | [] => false
  | fn :: rest =>
      FunctionDecl.requiresImplementation fn || Functions.anyMissingBody rest

def Modifiers.anyMissingBody :
    List Solidity.ModifierDecl -> Bool
  | [] => false
  | modifier :: rest =>
      ModifierDecl.requiresImplementation modifier ||
        Modifiers.anyMissingBody rest

def Functions.anyConstructorLike :
    List Solidity.FunctionDecl -> Bool
  | [] => false
  | fn :: rest =>
      FunctionDecl.isConstructorLike fn || Functions.anyConstructorLike rest

def Functions.anyConstructor :
    List Solidity.FunctionDecl -> Bool
  | [] => false
  | fn :: rest =>
      FunctionDecl.isConstructor fn || Functions.anyConstructor rest

def StateVars.allConstant :
    List Solidity.StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.isConstant decl && StateVars.allConstant rest

def ContractDecl.hasStorageLayoutBase
    (decl : Solidity.ContractDecl) : Bool :=
  decl.layoutBase.isSome

def ContractDecls.anyStorageLayoutBase :
    List Solidity.ContractDecl -> Bool
  | [] => false
  | decl :: rest =>
      ContractDecl.hasStorageLayoutBase decl ||
        ContractDecls.anyStorageLayoutBase rest

def ContractDecl.checkStorageLayoutBase (env : CheckEnv)
    (contract : Solidity.ContractDecl) :
    Except TypeError Unit := do
  match contract.layoutBase with
  | none => Except.ok ()
  | some expr => do
      require (contract.kind == Solidity.ContractKind.contract)
        (TypeError.invalidContractHeader
          "storage layout on non-contract")
      require (!contract.abstract)
        (TypeError.invalidContractHeader
          "storage layout on abstract contract")
      require (Expr.isStorageLayoutBaseComptime env expr)
        (TypeError.invalidContractHeader
          "storage layout base is not compile-time constant")
      let checked ← checkExpr env expr
      checked.expectAssignableToIn env.types
        (Solidity.Ty.uint 256)

def BaseSpecifier.check (env : CheckEnv) (sourceTypes : TypeContext)
    (contractKind : Solidity.ContractKind) (contractName : Name)
    (specifier : Solidity.BaseSpecifier) :
    Except TypeError Unit := do
  let baseDecl ←
    match sourceTypes.lookupContractDecl? specifier.base with
    | some decl => Except.ok decl
    | none => Except.error (TypeError.unknownType specifier.base)
  require (!(baseDecl.name == contractName))
    (TypeError.invalidContractHeader "contract inherits itself")
  if contractKind == Solidity.ContractKind.interface then
    require (baseDecl.kind == Solidity.ContractKind.interface)
      (TypeError.invalidContractHeader
        "interface inherits non-interface")
  else
    Except.ok ()
  if baseDecl.kind == Solidity.ContractKind.library then
    Except.error
      (TypeError.invalidContractHeader "contract inherits library")
  else
    Except.ok ()
  if specifier.args.isEmpty then
    Except.ok ()
  else
    let sig := ContractDecl.constructorSignature baseDecl
    match checkArgs env specifier.args with
    | Except.ok checkedArgs =>
        match
            checkCheckedArgsAssignableToFunctionSig env.types
              ("base constructor " ++ baseDecl.name)
              sig specifier.args checkedArgs with
        | Except.ok _ => Except.ok ()
        | Except.error checkedErr =>
            match
                checkContextualArgsAssignableToParamsWithStorageRefsFor
                  env ("base constructor " ++ baseDecl.name)
                  sig.paramNames sig.params sig.paramStorageRefs
                  sig.paramDataLocations specifier.args with
            | Except.ok _ => Except.ok ()
            | Except.error _ => Except.error checkedErr
    | Except.error argErr =>
        match
            checkContextualArgsAssignableToParamsWithStorageRefsFor
              env ("base constructor " ++ baseDecl.name)
              sig.paramNames sig.params sig.paramStorageRefs
              sig.paramDataLocations specifier.args with
        | Except.ok _ => Except.ok ()
        | Except.error _ => Except.error argErr

def BaseSpecifiers.check (env : CheckEnv) (sourceTypes : TypeContext)
    (contractKind : Solidity.ContractKind) (contractName : Name) :
    List Solidity.BaseSpecifier -> Except TypeError Unit
  | [] => Except.ok ()
  | specifier :: rest => do
      BaseSpecifier.check env sourceTypes contractKind contractName specifier
      BaseSpecifiers.check env sourceTypes contractKind contractName rest

def ContractDecl.checkBaseConstructorArgsForDeployment
    (storageOrder : List Solidity.ContractDecl)
    (target : Solidity.ContractDecl) :
    List Solidity.ContractDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | baseDecl :: rest => do
      if baseDecl.name == target.name then
        ContractDecl.checkBaseConstructorArgsForDeployment storageOrder target
          rest
      else
        let args ←
          match Solidity.Executable.ContractDecl.baseConstructorArgsAndSupplier?
              storageOrder baseDecl with
          | some (args, _) => Except.ok args
          | none =>
              Except.error
                (TypeError.invalidContractHeader
                  "base constructor arguments could not be resolved")
        let sig := ContractDecl.constructorSignature baseDecl
        if args.length == sig.params.length then
          ContractDecl.checkBaseConstructorArgsForDeployment storageOrder
            target rest
        else if args.isEmpty && target.abstract then
          ContractDecl.checkBaseConstructorArgsForDeployment storageOrder
            target rest
        else
          Except.error
            (TypeError.arityMismatch
              ("base constructor " ++ baseDecl.name)
              sig.params.length args.length)

def Functions.checkInterfaceDeclarations :
    List Solidity.FunctionDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | fn :: rest => do
      require (FunctionDecl.isInterfaceDeclaration fn)
        (TypeError.invalidContractHeader
          "interface function is not an external declaration")
      Functions.checkInterfaceDeclarations rest

def ContractDecl.checkKindShape (env : CheckEnv) (sourceTypes : TypeContext)
    (contract : Solidity.ContractDecl)
    (stateVars : List Solidity.StateVarDecl)
    (functions : List Solidity.FunctionDecl)
    (modifiers : List Solidity.ModifierDecl)
    (usingDecls : List Solidity.UsingDecl) :
    Except TypeError Unit := do
  BaseSpecifiers.check env sourceTypes contract.kind contract.name contract.bases
  match contract.kind with
  | Solidity.ContractKind.interface =>
      require (!contract.abstract)
        (TypeError.invalidContractHeader "interface is explicitly abstract")
      require stateVars.isEmpty
        (TypeError.invalidContractHeader
          "interface declares state variables")
      require modifiers.isEmpty
        (TypeError.invalidContractHeader "interface declares modifiers")
      require usingDecls.isEmpty
        (TypeError.invalidContractHeader
          "interface declares using directive")
      require (!Functions.anyConstructor functions)
        (TypeError.invalidContractHeader
          "interface declares constructor")
      Functions.checkInterfaceDeclarations functions
  | Solidity.ContractKind.library =>
      require contract.bases.isEmpty
        (TypeError.invalidContractHeader "library has bases")
      require (!contract.abstract)
        (TypeError.invalidContractHeader "library is abstract")
      require (StateVars.allConstant stateVars)
        (TypeError.invalidContractHeader
          "library declares non-constant state variables")
      require (!Functions.anyConstructorLike functions)
        (TypeError.invalidContractHeader
          "library declares constructor, receive, or fallback")
      require (!Functions.anyMissingBody functions)
        (TypeError.invalidContractHeader
          "library function has no implementation")
      require (!Modifiers.anyMissingBody modifiers)
        (TypeError.invalidContractHeader
          "library modifier has no implementation")
  | Solidity.ContractKind.contract =>
      if contract.abstract then
        Except.ok ()
      else if Functions.anyMissingBody functions ||
          Modifiers.anyMissingBody modifiers then
        Except.error
          (TypeError.invalidContractHeader
            "non-abstract contract has unimplemented function or modifier")
      else
        Except.ok ()

def ContractDecl.check (sourceFunctions : List FunctionSig)
    (sourceErrors : List ErrorSig) (sourceEvents : List EventSig)
    (sourceConstants : List Solidity.StateVarDecl)
    (sourceUsingDecls : List Solidity.UsingDecl)
    (sourceFreeFunctions : List Solidity.FunctionDecl)
    (sourceTypes : TypeContext)
    (contract : Solidity.ContractDecl) : Except TypeError Unit := do
  let stateVars := contract.items.filterMap ContractItem.stateVar?
  require (!StateVarDecls.constantsHaveCycle (stateVars ++ sourceConstants))
    (TypeError.invalidVariableDecl "constant has a cyclic dependency")
  let functions := contract.items.filterMap ContractItem.function?
  let modifiers := contract.items.filterMap ContractItem.modifier?
  let events := contract.items.filterMap ContractItem.event?
  let errors := contract.items.filterMap ContractItem.error?
  let structs := contract.items.filterMap ContractItem.struct?
  let enums := contract.items.filterMap ContractItem.enum?
  let userValueTypes := contract.items.filterMap ContractItem.userValueType?
  let usingDecls := contract.items.filterMap ContractItem.using?
  let functionNames := functions.filterMap FunctionDecl.declaredName?
  let nonFunctionNames :=
    stateVars.map Solidity.StateVarDecl.name ++
      modifiers.map Solidity.ModifierDecl.name ++
      errors.map Solidity.ErrorDecl.name ++
      structs.map Solidity.StructDecl.name ++
      enums.map Solidity.EnumDecl.name ++
      userValueTypes.map Solidity.UserValueTypeDecl.name
  ensureUniqueNames "contract declaration" nonFunctionNames
  ensureNamesDisjointFrom "contract declaration" nonFunctionNames
    functionNames
  ensureNamesDisjointFrom "contract declaration"
    (nonFunctionNames ++ functionNames)
    (events.map Solidity.EventDecl.name)
  let contractTypes :=
    sourceTypes.withContractTypes contract.name structs enums userValueTypes
  let localTypeNames := ContractDecl.localTypeNames contract
  let functionSigs :=
    (FunctionDecls.signatures functions).map
      (FunctionSig.qualifyLocalUserTypes contract.name localTypeNames)
  FunctionSigs.ensureNoDuplicateSignatures functionSigs
  FunctionSigs.ensureNoDuplicateExternalAbiSignatures contractTypes
    functionSigs
  FunctionSigs.ensureNoDuplicateExternalAbiSelectors contractTypes
    (ContractDecl.directExternalFunctionSigs contractTypes contract)
  require ((functions.filter
      (fun fn => fn.kind == Solidity.FunctionKind.constructor)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple constructors")
  require ((functions.filter
      (fun fn => fn.kind == Solidity.FunctionKind.receive)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple receive functions")
  require ((functions.filter
      (fun fn => fn.kind == Solidity.FunctionKind.fallback)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple fallback functions")
  let modifierSigs := modifiers.map ModifierDecl.signature
  let eventSigs := events.map EventDecl.signature
  EventSigs.ensureNoDuplicateAbiSignatures contractTypes eventSigs
  let errorSigs := errors.map ErrorDecl.signature
  let visibleSourceErrors := ErrorSigs.withoutNamesOf errorSigs sourceErrors
  let visibleSourceEvents := EventSigs.withoutNamesOf eventSigs sourceEvents
  let visibleSourceFunctions :=
    FunctionSigs.withoutNamesOf functionSigs sourceFunctions
  let currentPath := TypeContext.pathOfName contract.name
  let currentStateVarTypes :=
    StateVarDecls.namedTypesQualifiedLocalTypes
      contract.name localTypeNames stateVars
  let sourceConstantVars := StateVarDecls.namedTypes sourceConstants
  let sourceConstantBindings := StateVarDecls.namedConstness sourceConstants
  let currentConstantBindings :=
    StateVarDecls.namedConstness stateVars ++ sourceConstantBindings
  let baseEnv : CheckEnv :=
    { types := contractTypes
      vars := currentStateVarTypes ++ sourceConstantVars
      stateNames :=
        StateVarDecls.runtimeStateNamesWith currentConstantBindings stateVars
      constantBindings := currentConstantBindings
      immutableNames := StateVarDecls.immutableNames stateVars
      functions := functionSigs ++ visibleSourceFunctions
      modifiers := modifierSigs
      modifierDecls := modifiers
      usingDecls := UsingDecls.dedup (usingDecls ++ sourceUsingDecls)
      errors := errorSigs ++ visibleSourceErrors
      events := eventSigs ++ visibleSourceEvents
      contractKind := some contract.kind
      currentContractAbstract := contract.abstract
      currentContract := some currentPath
      returnTys := []
      returnNames := [] }
  let baseSpecifierEnv :=
    { baseEnv with
      vars := sourceConstantVars
      stateNames := []
      constantBindings := sourceConstantBindings
      immutableNames := []
      functions := sourceFunctions
      usingDecls := UsingDecls.dedup (usingDecls ++ sourceUsingDecls) }
  ContractDecl.checkKindShape baseSpecifierEnv sourceTypes contract stateVars
    functions modifiers usingDecls
  ContractDecl.checkStorageLayoutBase baseEnv contract
  let allContracts := sourceTypes.contractDecls.map Prod.snd
  let dispatchOrder ←
    match Solidity.Executable.ContractDecl.dispatchOrder?
        allContracts contract with
    | some order => Except.ok order
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  let ancestorPaths :=
    (List.drop 1 dispatchOrder).map
      (fun base => TypeContext.pathOfName base.name)
  let inheritedContracts := List.drop 1 dispatchOrder
  let contractTypes :=
    ContractDecls.addNestedTypesToContext contractTypes inheritedContracts
  require
    (!ContractDecls.anyStorageLayoutBase inheritedContracts)
    (TypeError.invalidContractHeader
      "storage layout specified by inherited contract")
  let storageOrder ←
    match Solidity.Executable.ContractDecl.storageOrder?
        allContracts contract with
    | some order => Except.ok order
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  FunctionSigs.ensureNoDuplicateExternalAbiSignatures contractTypes
    functionSigs
  EventSigs.ensureNoDuplicateAbiSignatures contractTypes eventSigs
  let allModifierDecls := ContractDecl.modifierDeclsFromOrder dispatchOrder
  let inheritedStateVars :=
    ContractDecls.visibleStateVars contractTypes ancestorPaths
  let inheritedStateVarNames :=
    ContractDecls.visibleStateVarNames contractTypes ancestorPaths
  let inheritedEventSigs :=
    ContractDecls.eventSigs contractTypes ancestorPaths
  let inheritedErrorSigs :=
    ContractDecls.errorSigs contractTypes ancestorPaths
  let inheritedEventNames :=
    ContractDecls.eventNames contractTypes ancestorPaths
  let inheritedNonEventTypeNames :=
    ContractDecls.nonEventTypeNames contractTypes ancestorPaths
  let visibleSourceErrors :=
    ErrorSigs.withoutNamesOf (errorSigs ++ inheritedErrorSigs)
      sourceErrors
  let visibleSourceEvents :=
    EventSigs.withoutNamesOf (eventSigs ++ inheritedEventSigs)
      sourceEvents
  let inheritedFunctionSigs :=
    ContractDecl.nonPrivateFunctionSigsFromOrder inheritedContracts
  let visibleFunctionSigs :=
    FunctionSigs.addNonPrivateAllIfNewSignature
      functionSigs inheritedFunctionSigs
  -- OV1: shadow free functions by the contract's visible member function names
  -- (own — any visibility — plus non-private inherited, exactly the set solc
  -- keeps in the contract's name scope).
  let visibleSourceFunctions :=
    FunctionSigs.withoutNamesOf visibleFunctionSigs sourceFunctions
  FunctionSigs.ensureNoDuplicateExternalAbiSelectors contractTypes
    (ContractDecl.externalFunctionSigsFromOrder contractTypes dispatchOrder)
  let visibleStateVars := stateVars ++ inheritedStateVars
  let visibleStateVarTypes :=
    currentStateVarTypes ++ StateVarDecls.namedTypes inheritedStateVars
  let visibleConstantBindings :=
    StateVarDecls.namedConstness visibleStateVars ++ sourceConstantBindings
  let baseEnv :=
    { baseEnv with
      types := contractTypes
      ancestorPaths := ancestorPaths
      vars := visibleStateVarTypes ++ sourceConstantVars
      stateNames :=
        StateVarDecls.runtimeStateNamesWith visibleConstantBindings
          visibleStateVars
      constantBindings := visibleConstantBindings
      immutableNames := StateVarDecls.immutableNames visibleStateVars
      functions := visibleFunctionSigs ++ visibleSourceFunctions
      -- G6: `super.f()` must resolve to an *implemented* base function; an
      -- abstract (bodyless) base declaration is not a valid super target
      -- (solc TypeError 9582). Regular dispatch (`functions`) keeps the
      -- abstract sigs; only the super chain filters them out.
      superFunctions := inheritedFunctionSigs.filter FunctionSig.hasBody
      modifiers := ModifierDecls.signatures allModifierDecls
      modifierDecls := allModifierDecls
      errors := errorSigs ++ inheritedErrorSigs ++ visibleSourceErrors
      events := eventSigs ++ inheritedEventSigs ++ visibleSourceEvents
      -- G8: contract-level (own + inherited) NON-error member names. Uses the
      -- CONTRACT function sigs (`visibleFunctionSigs`), NOT the merged
      -- `functions` (which also carries free functions), so a free function
      -- does not spuriously shadow a contract error.
      contractNonErrorMemberNames :=
        visibleFunctionSigs.map (·.name) ++
          visibleStateVars.map Solidity.StateVarDecl.name ++
          (ModifierDecls.signatures allModifierDecls).map (·.name) ++
          (eventSigs ++ inheritedEventSigs).map (·.name)
      -- CF2: provably-always-reverting internal callees in scope. Own contract
      -- functions ∪ file-level free functions (inherited-base helper bodies are
      -- out of scope here — a sound under-detection, never an over-accept).
      alwaysRevertNames :=
        computeAlwaysRevertNames (functions ++ sourceFreeFunctions) }
  ContractDecl.checkBaseConstructorArgsForDeployment storageOrder contract
    storageOrder
  EventSigs.ensureNoDuplicateAbiSignaturesAgainst contractTypes
    inheritedEventSigs eventSigs
  StateVarDecls.checkNoInheritedShadowing inheritedStateVarNames stateVars
  checkNoInheritedStateNameClashes inheritedStateVarNames
    (modifiers.map Solidity.ModifierDecl.name ++
      events.map Solidity.EventDecl.name ++
      errors.map Solidity.ErrorDecl.name ++
      structs.map Solidity.StructDecl.name ++
      enums.map Solidity.EnumDecl.name ++
      userValueTypes.map Solidity.UserValueTypeDecl.name)
  let localNamesExceptEvents :=
    stateVars.map Solidity.StateVarDecl.name ++
      functionNames ++
      modifiers.map Solidity.ModifierDecl.name ++
      errors.map Solidity.ErrorDecl.name ++
      structs.map Solidity.StructDecl.name ++
      enums.map Solidity.EnumDecl.name ++
      userValueTypes.map Solidity.UserValueTypeDecl.name
  let allLocalDeclarationNames :=
    localNamesExceptEvents ++ events.map Solidity.EventDecl.name
  checkNoInheritedNamedDeclarationClashes
    "declaration shadows inherited event"
    inheritedEventNames localNamesExceptEvents
  checkNoInheritedNamedDeclarationClashes
    "declaration shadows inherited type or error"
    inheritedNonEventTypeNames allLocalDeclarationNames
  let inheritedMembers ←
    match ContractDecl.inheritedOverrideMembers? contractTypes allContracts
        contract with
    | some members => Except.ok members
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  let inheritedModifierMembers ←
    match ContractDecl.inheritedModifierMembers? allContracts contract with
    | some members => Except.ok members
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  let inheritedFunctionNames :=
    OverrideMembers.nonStateNames inheritedMembers
  let inheritedModifierNames :=
    ModifierOverrideMembers.names inheritedModifierMembers
  let nonFunctionTypeNames :=
    events.map Solidity.EventDecl.name ++
      errors.map Solidity.ErrorDecl.name ++
      structs.map Solidity.StructDecl.name ++
      enums.map Solidity.EnumDecl.name ++
      userValueTypes.map Solidity.UserValueTypeDecl.name
  checkNoInheritedNamedDeclarationClashes
    "declaration shadows inherited function"
    inheritedFunctionNames
    (modifiers.map Solidity.ModifierDecl.name ++
      nonFunctionTypeNames)
  checkNoInheritedNamedDeclarationClashes
    "declaration shadows inherited modifier"
    inheritedModifierNames
    (stateVars.map Solidity.StateVarDecl.name ++
      functionNames ++ nonFunctionTypeNames)
  let currentMembers := ContractDecl.overrideMembers contractTypes contract
  let currentModifierMembers := ModifierOverrideMembers.forContract contract
  let inheritsUnimplementedAllowed :=
    contract.abstract ||
      contract.kind == Solidity.ContractKind.interface
  OverrideMembers.checkInheritedConflicts allContracts currentMembers
    inheritedMembers
  ModifierOverrideMembers.checkInheritedConflicts allContracts
    currentModifierMembers inheritedModifierMembers
  OverrideMembers.checkInheritedAbstractImplemented allContracts
    inheritsUnimplementedAllowed currentMembers inheritedMembers
  ModifierOverrideMembers.checkInheritedAbstractImplemented allContracts
    inheritsUnimplementedAllowed currentModifierMembers inheritedModifierMembers
    inheritedModifierMembers
  let rec checkStructs :
      List Solidity.StructDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StructDecl.check baseEnv
          [ TypeContext.pathOfName decl.name,
            TypeContext.qualifiedPath contract.name decl.name ] decl
        checkStructs rest
  let rec checkEnums :
      List Solidity.EnumDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        EnumDecl.check decl
        checkEnums rest
  let rec checkUserValueTypes :
      List Solidity.UserValueTypeDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UserValueTypeDecl.check baseEnv decl
        checkUserValueTypes rest
  let rec checkUsingDecls :
      List Solidity.UsingDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UsingDecl.checkContractLevel baseEnv decl
        checkUsingDecls rest
  let rec checkStateVars :
      List Solidity.StateVarDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StateVarDecl.checkOverrideRules contractTypes currentPath
          contract.name localTypeNames contract.kind ancestorPaths
          inheritedMembers decl
        StateVarDecl.check baseEnv decl
        checkStateVars rest
  let rec checkFunctions :
      List Solidity.FunctionDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | fn :: rest => do
        FunctionDecl.checkOverrideRules currentPath contract.name
          localTypeNames contract.kind ancestorPaths inheritedMembers
          inheritedStateVarNames fn
        FunctionDecl.check baseEnv fn
        checkFunctions rest
  let rec checkModifiers :
      List Solidity.ModifierDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | modifier :: rest => do
        ModifierDecl.checkOverrideRules currentPath contract.kind
          ancestorPaths inheritedModifierMembers modifier
        ModifierDecl.check baseEnv modifier
        checkModifiers rest
  let rec checkEvents :
      List Solidity.EventDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | event :: rest => do
        EventDecl.check baseEnv event
        checkEvents rest
  let rec checkErrors :
      List Solidity.ErrorDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | err :: rest => do
        ErrorDecl.check baseEnv err
        checkErrors rest
  checkStructs structs
  checkEnums enums
  checkUserValueTypes userValueTypes
  checkUsingDecls usingDecls
  checkStateVars stateVars
  checkFunctions functions
  checkModifiers modifiers
  checkEvents events
  checkErrors errors

structure CheckedSourceUnit where
  source : Solidity.SourceUnit
  deriving Repr

structure SolidityVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving Repr, BEq

structure SolidityVersionLiteral where
  version : SolidityVersion
  components : Nat
  deriving Repr, BEq

inductive SolidityVersionConstraint where
  | any : SolidityVersionConstraint
  | never : SolidityVersionConstraint
  | exact : SolidityVersionLiteral -> SolidityVersionConstraint
  | ge : SolidityVersionLiteral -> SolidityVersionConstraint
  | gt : SolidityVersionLiteral -> SolidityVersionConstraint
  | le : SolidityVersionLiteral -> SolidityVersionConstraint
  | lt : SolidityVersionLiteral -> SolidityVersionConstraint
  | caret : SolidityVersionLiteral -> SolidityVersionConstraint
  | tilde : SolidityVersionLiteral -> SolidityVersionConstraint
  | range : SolidityVersion -> Option SolidityVersion ->
      SolidityVersionConstraint
  deriving Repr, BEq

structure SolidityVersionPattern where
  major : Option Nat
  minor : Option Nat
  patch : Option Nat
  components : Nat
  deriving Repr, BEq

def solidityCompilerVersion : SolidityVersion :=
  { major := 0, minor := 8, patch := 35 }

def SolidityVersion.lt (left right : SolidityVersion) : Bool :=
  left.major < right.major ||
    (left.major == right.major &&
      (left.minor < right.minor ||
        (left.minor == right.minor && left.patch < right.patch)))

def SolidityVersion.le (left right : SolidityVersion) : Bool :=
  left == right || left.lt right

def SolidityVersion.withPatchDefault
    (major minor patch : Nat) : SolidityVersion :=
  { major := major, minor := minor, patch := patch }

def isSolidityVersionWildcardPart (text : String) : Bool :=
  text == "x" || text == "X" || text == "*"

def parseSolidityVersionPatternPart? (text : String) :
    Option (Option Nat) :=
  if isSolidityVersionWildcardPart text then
    some none
  else do
    let value ← Solidity.Executable.parseDecimalNat? text
    some (some value)

def parseSolidityVersionPattern? (text : String) :
    Option SolidityVersionPattern :=
  match
      ((String.trimAscii text).toString.splitOn ".").filter
        (fun part => part != "")
  with
  | [majorText] => do
      let major ← parseSolidityVersionPatternPart? majorText
      some
        { major := major
          minor := some 0
          patch := some 0
          components := 1 }
  | [majorText, minorText] => do
      let major ← parseSolidityVersionPatternPart? majorText
      let minor ← parseSolidityVersionPatternPart? minorText
      some
        { major := major
          minor := minor
          patch := some 0
          components := 2 }
  | [majorText, minorText, patchText] => do
      let major ← parseSolidityVersionPatternPart? majorText
      let minor ← parseSolidityVersionPatternPart? minorText
      let patch ← parseSolidityVersionPatternPart? patchText
      some
        { major := major
          minor := minor
          patch := patch
          components := 3 }
  | _ => none

def SolidityVersionPattern.hasWildcard
    (pattern : SolidityVersionPattern) : Bool :=
  pattern.major.isNone ||
    (pattern.components >= 2 && pattern.minor.isNone) ||
    (pattern.components >= 3 && pattern.patch.isNone)

def SolidityVersionPattern.lowerBound
    (pattern : SolidityVersionPattern) : SolidityVersion :=
  { major := pattern.major.getD 0
    minor := pattern.minor.getD 0
    patch := pattern.patch.getD 0 }

def SolidityVersionPattern.upperBound?
    (pattern : SolidityVersionPattern) : Option SolidityVersion :=
  match pattern.major, pattern.minor, pattern.patch with
  | none, _, _ => none
  | some major, none, _ =>
      some { major := major + 1, minor := 0, patch := 0 }
  | some major, some minor, none =>
      some { major := major, minor := minor + 1, patch := 0 }
  | some major, some minor, some patch =>
      some { major := major, minor := minor, patch := patch + 1 }

def parseSolidityWildcardRange? (text : String) :
    Option (SolidityVersion × Option SolidityVersion) := do
  let pattern ← parseSolidityVersionPattern? text
  if pattern.hasWildcard then
    some (pattern.lowerBound, pattern.upperBound?)
  else
    none

def parseSolidityVersionLiteral? (text : String) :
    Option SolidityVersionLiteral :=
  match
      ((String.trimAscii text).toString.splitOn ".").filter
        (fun part => part != "")
  with
  | [majorText] => do
      let major ← Solidity.Executable.parseDecimalNat? majorText
      some
        { version := SolidityVersion.withPatchDefault major 0 0
          components := 1 }
  | [majorText, minorText] => do
      let major ← Solidity.Executable.parseDecimalNat? majorText
      let minor ← Solidity.Executable.parseDecimalNat? minorText
      some
        { version := SolidityVersion.withPatchDefault major minor 0
          components := 2 }
  | [majorText, minorText, patchText] => do
      let major ← Solidity.Executable.parseDecimalNat? majorText
      let minor ← Solidity.Executable.parseDecimalNat? minorText
      let patch ← Solidity.Executable.parseDecimalNat? patchText
      some
        { version := SolidityVersion.withPatchDefault major minor patch
          components := 3 }
  | _ => none

def SolidityVersionLiteral.matchesExactCurrent
    (literal : SolidityVersionLiteral) : Bool :=
  match literal.components with
  | 1 => solidityCompilerVersion.major == literal.version.major
  | 2 =>
      solidityCompilerVersion.major == literal.version.major &&
        solidityCompilerVersion.minor == literal.version.minor
  | _ => solidityCompilerVersion == literal.version

def SolidityVersionLiteral.caretUpperBound
    (literal : SolidityVersionLiteral) : SolidityVersion :=
  let version := literal.version
  if version.major > 0 then
    { major := version.major + 1, minor := 0, patch := 0 }
  else if version.minor > 0 then
    { major := 0, minor := version.minor + 1, patch := 0 }
  else
    { major := 0, minor := 0, patch := version.patch + 1 }

def SolidityVersionLiteral.tildeUpperBound
    (literal : SolidityVersionLiteral) : SolidityVersion :=
  let version := literal.version
  match literal.components with
  | 1 => { major := version.major + 1, minor := 0, patch := 0 }
  | _ => { major := version.major, minor := version.minor + 1, patch := 0 }

def SolidityVersionConstraint.matchesCurrent :
    SolidityVersionConstraint -> Bool
  | SolidityVersionConstraint.any => true
  | SolidityVersionConstraint.never => false
  | SolidityVersionConstraint.exact literal =>
      literal.matchesExactCurrent
  | SolidityVersionConstraint.ge literal =>
      literal.version.le solidityCompilerVersion
  | SolidityVersionConstraint.gt literal =>
      literal.version.lt solidityCompilerVersion
  | SolidityVersionConstraint.le literal =>
      solidityCompilerVersion.le literal.version
  | SolidityVersionConstraint.lt literal =>
      solidityCompilerVersion.lt literal.version
  | SolidityVersionConstraint.caret literal =>
      literal.version.le solidityCompilerVersion &&
        solidityCompilerVersion.lt literal.caretUpperBound
  | SolidityVersionConstraint.tilde literal =>
      literal.version.le solidityCompilerVersion &&
        solidityCompilerVersion.lt literal.tildeUpperBound
  | SolidityVersionConstraint.range lower upper? =>
      lower.le solidityCompilerVersion &&
        match upper? with
        | some upper => solidityCompilerVersion.lt upper
        | none => true

def parseSolidityConstraintWithOperator? (op version : String) :
    Option SolidityVersionConstraint :=
  match parseSolidityWildcardRange? version with
  | some (lower, upper?) =>
      let lowerLiteral : SolidityVersionLiteral :=
        { version := lower, components := 3 }
      if op == ">=" then some (SolidityVersionConstraint.ge lowerLiteral)
      else if op == ">" then
        match upper? with
        | some upper =>
            some
              (SolidityVersionConstraint.ge
                { version := upper, components := 3 })
        | none => some SolidityVersionConstraint.never
      else if op == "<=" then
        match upper? with
        | some upper =>
            some
              (SolidityVersionConstraint.lt
                { version := upper, components := 3 })
        | none => some SolidityVersionConstraint.any
      else if op == "<" then some (SolidityVersionConstraint.lt lowerLiteral)
      else if op == "=" || op == "==" || op == "^" || op == "~" then
        some (SolidityVersionConstraint.range lower upper?)
      else none
  | none => do
      let literal ← parseSolidityVersionLiteral? version
      if op == ">=" then some (SolidityVersionConstraint.ge literal)
      else if op == ">" then some (SolidityVersionConstraint.gt literal)
      else if op == "<=" then some (SolidityVersionConstraint.le literal)
      else if op == "<" then some (SolidityVersionConstraint.lt literal)
      else if op == "=" || op == "==" then
        some (SolidityVersionConstraint.exact literal)
      else if op == "^" then some (SolidityVersionConstraint.caret literal)
      else if op == "~" then some (SolidityVersionConstraint.tilde literal)
      else none

def parseSolidityConstraintToken? (token : String) :
    Option SolidityVersionConstraint :=
  if String.isPrefixOf ">=" token then
    parseSolidityConstraintWithOperator? ">=" (token.drop 2).toString
  else if String.isPrefixOf "<=" token then
    parseSolidityConstraintWithOperator? "<=" (token.drop 2).toString
  else if String.isPrefixOf "==" token then
    parseSolidityConstraintWithOperator? "==" (token.drop 2).toString
  else if String.isPrefixOf ">" token then
    parseSolidityConstraintWithOperator? ">" (token.drop 1).toString
  else if String.isPrefixOf "<" token then
    parseSolidityConstraintWithOperator? "<" (token.drop 1).toString
  else if String.isPrefixOf "=" token then
    parseSolidityConstraintWithOperator? "=" (token.drop 1).toString
  else if String.isPrefixOf "^" token then
    parseSolidityConstraintWithOperator? "^" (token.drop 1).toString
  else if String.isPrefixOf "~" token then
    parseSolidityConstraintWithOperator? "~" (token.drop 1).toString
  else
    match parseSolidityWildcardRange? token with
    | some (lower, upper?) =>
        some (SolidityVersionConstraint.range lower upper?)
    | none => do
        let literal ← parseSolidityVersionLiteral? token
        some (SolidityVersionConstraint.exact literal)

def isSolidityConstraintOperator (token : String) : Bool :=
  token == ">=" || token == ">" || token == "<=" || token == "<" ||
    token == "=" || token == "==" || token == "^" || token == "~"

def splitPragmaWhitespace (text : String) : List String :=
  (text.split
    (fun ch =>
      ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r')).toList.map
      (fun slice => slice.toString)

def parseSolidityConstraints? :
    List String -> Option (List SolidityVersionConstraint)
  | [] => some []
  | op :: version :: rest =>
      if isSolidityConstraintOperator op then do
        let head ← parseSolidityConstraintWithOperator? op version
        let tail ← parseSolidityConstraints? rest
        some (head :: tail)
      else do
        let head ← parseSolidityConstraintToken? op
        let tail ← parseSolidityConstraints? (version :: rest)
        some (head :: tail)
  | [token] => do
      let head ← parseSolidityConstraintToken? token
      some [head]

def parseSolidityHyphenRange? (text : String) :
    Option (List SolidityVersionConstraint) :=
  match text.splitOn "-" with
  | [lowerText, upperText] => do
      let lowerPattern ← parseSolidityVersionPattern? lowerText
      let upperPattern ← parseSolidityVersionPattern? upperText
      some
        [ SolidityVersionConstraint.range lowerPattern.lowerBound
            upperPattern.upperBound? ]
  | _ => none

def parseSolidityConstraintGroup? (text : String) :
    Option (List SolidityVersionConstraint) :=
  match parseSolidityHyphenRange? text with
  | some constraints => some constraints
  | none =>
      parseSolidityConstraints?
        ((splitPragmaWhitespace text).filter (fun token => token != ""))

def SolidityVersionConstraints.allMatchCurrent :
    List SolidityVersionConstraint -> Bool
  | [] => false
  | constraint :: rest =>
      constraint.matchesCurrent &&
        match rest with
        | [] => true
        | _ => SolidityVersionConstraints.allMatchCurrent rest

def solidityPragmaMatchesCurrentCompiler (expr : String) : Bool :=
  let groups :=
    (expr.splitOn "||").map (fun group => (String.trimAscii group).toString)
  groups.any
    (fun group =>
      match parseSolidityConstraintGroup? group with
      | some constraints => SolidityVersionConstraints.allMatchCurrent constraints
      | none => false)

def SourceItem.checkPragma :
    Solidity.SourceItem -> Except TypeError Unit
  | Solidity.SourceItem.pragma name value =>
      if name == "solidity" then
        require (solidityPragmaMatchesCurrentCompiler value)
          (TypeError.unsupported "source solidity pragma version")
      else if name == "abicoder" then
        let value := (String.trimAscii value).toString
        require (value == "v1" || value == "v2")
          (TypeError.unsupported "source abicoder pragma")
      else if name == "experimental" then
        let value := (String.trimAscii value).toString
        require (value == "ABIEncoderV2" || value == "SMTChecker")
          (TypeError.unsupported "source experimental pragma")
      else
        Except.error (TypeError.unsupported ("unknown pragma " ++ name))
  | _ => Except.ok ()

def SourceItem.experimentalPragmaFeature? :
    Solidity.SourceItem -> Option String
  | Solidity.SourceItem.pragma "experimental" value =>
      some (String.trimAscii value).toString
  | _ => none

def SourceItems.checkPragmasFrom (seenExperimental : List String) :
    List Solidity.SourceItem -> Except TypeError Unit
  | [] => Except.ok ()
  | item :: rest => do
      SourceItem.checkPragma item
      match SourceItem.experimentalPragmaFeature? item with
      | some feature =>
          require (!seenExperimental.contains feature)
            (TypeError.unsupported "duplicate experimental pragma")
          SourceItems.checkPragmasFrom (feature :: seenExperimental) rest
      | none =>
          SourceItems.checkPragmasFrom seenExperimental rest

def SourceItems.checkPragmas :
    List Solidity.SourceItem -> Except TypeError Unit
  | items => SourceItems.checkPragmasFrom [] items

inductive AbiCoderSelection where
  | explicitV1 : AbiCoderSelection
  | explicitV2 : AbiCoderSelection
  | experimentalV2 : AbiCoderSelection
  deriving Repr, BEq

def AbiCoderSelection.isV1 : AbiCoderSelection -> Bool
  | AbiCoderSelection.explicitV1 => true
  | _ => false

def SourceItem.abiCoderSelection? :
    Solidity.SourceItem ->
    Except TypeError (Option AbiCoderSelection)
  | Solidity.SourceItem.pragma "abicoder" value =>
      let value := (String.trimAscii value).toString
      if value == "v1" then
        Except.ok (some AbiCoderSelection.explicitV1)
      else if value == "v2" then
        Except.ok (some AbiCoderSelection.explicitV2)
      else
        Except.error (TypeError.unsupported "source abicoder pragma")
  | Solidity.SourceItem.pragma "experimental" value =>
      let value := (String.trimAscii value).toString
      if value == "ABIEncoderV2" then
        Except.ok (some AbiCoderSelection.experimentalV2)
      else
        Except.ok none
  | _ => Except.ok none

def SourceItems.abiCoderV1From?
    (selected : Option AbiCoderSelection) :
    List Solidity.SourceItem -> Except TypeError Bool
  | [] =>
      Except.ok
        (match selected with
        | some selection => selection.isV1
        | none => false)
  | item :: rest => do
      match (← SourceItem.abiCoderSelection? item) with
      | none => SourceItems.abiCoderV1From? selected rest
      | some selection =>
          match selected with
          | none => SourceItems.abiCoderV1From? (some selection) rest
          | some AbiCoderSelection.explicitV2 =>
              match selection with
              | AbiCoderSelection.experimentalV2 =>
                  SourceItems.abiCoderV1From? selected rest
              | _ =>
                  Except.error
                    (TypeError.unsupported
                      "source abicoder pragma already selected")
          | some _ =>
              Except.error
                (TypeError.unsupported
                  "source abicoder pragma already selected")

def SourceItems.abiCoderV1? (items : List Solidity.SourceItem) :
    Except TypeError Bool :=
  SourceItems.abiCoderV1From? none items

def SourceItem.contract? :
    Solidity.SourceItem -> Option Solidity.ContractDecl
  | Solidity.SourceItem.contract decl => some decl
  | _ => none

def SourceItem.freeFunction? :
    Solidity.SourceItem -> Option Solidity.FunctionDecl
  | Solidity.SourceItem.freeFunction decl => some decl
  | _ => none

def SourceItem.freeConstant? :
    Solidity.SourceItem -> Option Solidity.StateVarDecl
  | Solidity.SourceItem.freeConstant decl => some decl
  | _ => none

def SourceItem.freeError? :
    Solidity.SourceItem -> Option Solidity.ErrorDecl
  | Solidity.SourceItem.freeError decl => some decl
  | _ => none

def SourceItem.freeStruct? :
    Solidity.SourceItem -> Option Solidity.StructDecl
  | Solidity.SourceItem.freeStruct decl => some decl
  | _ => none

def SourceItem.freeEnum? :
    Solidity.SourceItem -> Option Solidity.EnumDecl
  | Solidity.SourceItem.freeEnum decl => some decl
  | _ => none

def SourceItem.freeUserValueType? :
    Solidity.SourceItem ->
    Option Solidity.UserValueTypeDecl
  | Solidity.SourceItem.freeUserValueType decl => some decl
  | _ => none

def SourceItem.using? :
    Solidity.SourceItem -> Option Solidity.UsingDecl
  | Solidity.SourceItem.usingDecl decl => some decl
  | _ => none

def SourceItem.freeEvent? :
    Solidity.SourceItem -> Option Solidity.EventDecl
  | Solidity.SourceItem.freeEvent decl => some decl
  | _ => none

def SourceItem.isUnresolvedImport :
    Solidity.SourceItem -> Bool
  | Solidity.SourceItem.importPath _ _ => true
  | _ => false

def SourceItems.hasUnresolvedImport :
    List Solidity.SourceItem -> Bool
  | [] => false
  | item :: rest =>
      SourceItem.isUnresolvedImport item ||
        SourceItems.hasUnresolvedImport rest

def SourceUnit.checkWithEvmVersion (evmVersion : EvmVersion)
    (source : Solidity.SourceUnit) :
    Except TypeError CheckedSourceUnit := do
  require (!SourceItems.hasUnresolvedImport source.items)
    (TypeError.unsupported "source import resolution")
  SourceItems.checkPragmas source.items
  let abiCoderV1 ← SourceItems.abiCoderV1? source.items
  let contracts := source.items.filterMap SourceItem.contract?
  let freeFunctions := source.items.filterMap SourceItem.freeFunction?
  let freeConstants := source.items.filterMap SourceItem.freeConstant?
  let freeErrors := source.items.filterMap SourceItem.freeError?
  let freeEvents := source.items.filterMap SourceItem.freeEvent?
  let freeStructs := source.items.filterMap SourceItem.freeStruct?
  let freeEnums := source.items.filterMap SourceItem.freeEnum?
  let freeUserValueTypes :=
    source.items.filterMap SourceItem.freeUserValueType?
  let sourceUsingDecls := source.items.filterMap SourceItem.using?
  let freeFunctionSigs := FunctionDecls.signatures freeFunctions
  let freeFunctionNames := freeFunctions.filterMap FunctionDecl.declaredName?
  let freeErrorSigs := freeErrors.map ErrorDecl.signature
  let freeEventSigs := freeEvents.map EventDecl.signature
  FunctionSigs.ensureNoDuplicateSignatures freeFunctionSigs
  let topLevelNonEventNames :=
    contracts.map Solidity.ContractDecl.name ++
      freeConstants.map Solidity.StateVarDecl.name ++
      freeErrors.map Solidity.ErrorDecl.name ++
      freeStructs.map Solidity.StructDecl.name ++
      freeEnums.map Solidity.EnumDecl.name ++
      freeUserValueTypes.map Solidity.UserValueTypeDecl.name
  ensureUniqueNames "top-level declaration" topLevelNonEventNames
  ensureNamesDisjointFrom "top-level declaration" topLevelNonEventNames
    freeFunctionNames
  ensureNamesDisjointFrom "top-level declaration"
    (topLevelNonEventNames ++ freeFunctionNames)
    (freeEvents.map Solidity.EventDecl.name)
  let sourceTypes :=
    { TypeContext.empty.withSourceTypes contracts freeStructs freeEnums
        freeUserValueTypes with
      abiCoderV1 := abiCoderV1
      evmVersion := evmVersion }
  EventSigs.ensureNoDuplicateAbiSignatures sourceTypes freeEventSigs
  let sourceEnv : CheckEnv :=
    { types := sourceTypes
      vars := StateVarDecls.namedTypes freeConstants
      constantBindings := StateVarDecls.namedConstness freeConstants
      functions := freeFunctionSigs
      usingDecls := sourceUsingDecls
      errors := freeErrorSigs
      events := freeEventSigs
      -- CF2: free functions calling always-reverting free helpers.
      alwaysRevertNames := computeAlwaysRevertNames freeFunctions
      returnTys := []
      returnNames := [] }
  let rec checkFreeStructs :
      List Solidity.StructDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StructDecl.check sourceEnv [TypeContext.pathOfName decl.name] decl
        checkFreeStructs rest
  let rec checkFreeEnums :
      List Solidity.EnumDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        EnumDecl.check decl
        checkFreeEnums rest
  let rec checkFreeUserValueTypes :
      List Solidity.UserValueTypeDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UserValueTypeDecl.check sourceEnv decl
        checkFreeUserValueTypes rest
  let rec checkFreeConstants :
      List Solidity.StateVarDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StateVarDecl.checkFileLevelConstant sourceEnv decl
        checkFreeConstants rest
  let rec checkSourceUsingDecls :
      List Solidity.UsingDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UsingDecl.checkFileLevel sourceEnv decl
        checkSourceUsingDecls rest
  let rec checkFreeFunctions :
      List Solidity.FunctionDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | fn :: rest => do
        FunctionDecl.check sourceEnv fn
        checkFreeFunctions rest
  let rec checkFreeErrors :
      List Solidity.ErrorDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | err :: rest => do
        ErrorDecl.check sourceEnv err
        checkFreeErrors rest
  let rec checkFreeEvents :
      List Solidity.EventDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | event :: rest => do
        EventDecl.check sourceEnv event
        checkFreeEvents rest
  let rec checkContracts :
      List Solidity.ContractDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | contract :: rest => do
      ContractDecl.check freeFunctionSigs freeErrorSigs freeEventSigs
          freeConstants sourceUsingDecls freeFunctions sourceTypes contract
      checkContracts rest
  require (!StateVarDecls.constantsHaveCycle freeConstants)
    (TypeError.invalidVariableDecl "constant has a cyclic dependency")
  checkFreeStructs freeStructs
  checkFreeEnums freeEnums
  checkFreeUserValueTypes freeUserValueTypes
  checkFreeConstants freeConstants
  checkSourceUsingDecls sourceUsingDecls
  UsingDecls.checkNoDuplicateOperatorBindings sourceUsingDecls
  checkFreeFunctions freeFunctions
  checkFreeEvents freeEvents
  checkFreeErrors freeErrors
  checkContracts contracts
  Except.ok { source := source }

def SourceUnit.check (source : Solidity.SourceUnit) :
    Except TypeError CheckedSourceUnit :=
  SourceUnit.checkWithEvmVersion EvmVersion.default source

def sourceUnitAccepted? (source : Solidity.SourceUnit) : Bool :=
  Result.isOk (SourceUnit.check source)

def checkSourceUnit (source : SourceUnitAst) :
    Except TypeError CheckedSourceUnit :=
  SourceUnit.check source

def checkSourceUnit? (source : SourceUnitAst) :
    Option CheckedSourceUnit :=
  Result.toOption (checkSourceUnit source)

def sourceUnitForContractDecl (decl : SourceContractDecl) :
    SourceUnitAst :=
  { items := [Solidity.SourceItem.contract decl] }

def SourceUnit.defaultContractName? (source : SourceUnitAst) : Option Name :=
  match source.items.filterMap SourceItem.contract? with
  | [decl] => some decl.name
  | _ => none

/-
The common typechecked-source layer.

`Interface.lean` intentionally remains the raw source/executable surface because
the typechecker depends on the syntax and translators defined there. Anything
that wants Solidity validity before execution should enter through this layer:
raw source units, already-checked source units, and standalone contract
declarations all normalize to a `CheckedSourceUnit` here.
-/
class TypecheckedInput (α : Type) where
  checkedSourceUnitOf : α -> Except TypeError CheckedSourceUnit
  defaultContractName? : α -> Option Name

instance typecheckedInputCheckedSourceUnit :
    TypecheckedInput CheckedSourceUnit where
  checkedSourceUnitOf checked := Except.ok checked
  defaultContractName? checked := SourceUnit.defaultContractName? checked.source

instance typecheckedInputSourceUnit : TypecheckedInput SourceUnitAst where
  checkedSourceUnitOf := checkSourceUnit
  defaultContractName? := SourceUnit.defaultContractName?

instance typecheckedInputContractDecl :
    TypecheckedInput SourceContractDecl where
  checkedSourceUnitOf decl := checkSourceUnit (sourceUnitForContractDecl decl)
  defaultContractName? decl := some decl.name

namespace TypecheckedInput

def checkedSourceUnit? {α : Type} [TypecheckedInput α] (input : α) :
    Option CheckedSourceUnit :=
  Result.toOption (checkedSourceUnitOf input)

def checkedSourceUnit {α : Type} [TypecheckedInput α] (input : α) :
    Except TypeError CheckedSourceUnit :=
  checkedSourceUnitOf input

def source? {α : Type} [TypecheckedInput α] (input : α) :
    Option SourceUnitAst := do
  let checked ← checkedSourceUnit? input
  some checked.source

def source {α : Type} [TypecheckedInput α] (input : α) :
    Except TypeError SourceUnitAst := do
  let checked ← checkedSourceUnit input
  Except.ok checked.source

def defaultContractName {α : Type} [TypecheckedInput α] (input : α) :
    Except TypeError Name :=
  match TypecheckedInput.defaultContractName? input with
  | some name => Except.ok name
  | none => Except.error (TypeError.unsupported "default contract name")

end TypecheckedInput

namespace SourceUnit

def typechecked? (source : SourceUnitAst) :
    Option CheckedSourceUnit :=
  TypecheckedInput.checkedSourceUnit? source

def typechecked (source : SourceUnitAst) :
    Except TypeError CheckedSourceUnit :=
  TypecheckedInput.checkedSourceUnit source

end SourceUnit

namespace ContractDecl

def sourceUnit (decl : SourceContractDecl) : SourceUnitAst :=
  sourceUnitForContractDecl decl

def typechecked? (decl : SourceContractDecl) :
    Option CheckedSourceUnit :=
  TypecheckedInput.checkedSourceUnit? decl

def typechecked (decl : SourceContractDecl) :
    Except TypeError CheckedSourceUnit :=
  TypecheckedInput.checkedSourceUnit decl

end ContractDecl


end TypeCheck
end Solidity
end SolidCore

import SolidCore.Spine.L00_SourceSolidity.Interface

namespace SolidCore
namespace Spine
namespace L00_SourceSolidity
namespace TypeCheck

abbrev Name := L00_SourceSolidity.Name
abbrev Ty := L00_SourceSolidity.Ty
abbrev Path := L00_SourceSolidity.Path
abbrev TypeEnv := L00_SourceSolidity.Executable.TypeEnv

structure TypeContext where
  contracts : List Path := []
  contractDecls : List (Path × L00_SourceSolidity.ContractDecl) := []
  structs : List (Path × L00_SourceSolidity.StructDecl) := []
  enums : List (Path × L00_SourceSolidity.EnumDecl) := []
  userValueTypes : List (Path × Ty) := []
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
    Option L00_SourceSolidity.StructDecl :=
  lookupPath? path ctx.structs

def lookupContractDecl? (ctx : TypeContext) (path : Path) :
    Option L00_SourceSolidity.ContractDecl :=
  lookupPath? path ctx.contractDecls

def lookupEnum? (ctx : TypeContext) (path : Path) :
    Option L00_SourceSolidity.EnumDecl :=
  lookupPath? path ctx.enums

def lookupUserValueType? (ctx : TypeContext) (path : Path) :
    Option Ty :=
  lookupPath? path ctx.userValueTypes

def isContractPath (ctx : TypeContext) (path : Path) : Bool :=
  match lookupContract? ctx path with
  | some _ => true
  | none => false

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

def withSourceTypes (ctx : TypeContext)
    (contracts : List L00_SourceSolidity.ContractDecl)
    (structs : List L00_SourceSolidity.StructDecl)
    (enums : List L00_SourceSolidity.EnumDecl)
    (userValueTypes : List L00_SourceSolidity.UserValueTypeDecl) :
    TypeContext :=
  { ctx with
    contracts :=
      contracts.map (fun decl => pathOfName decl.name) ++ ctx.contracts
    contractDecls :=
      contracts.map (fun decl => (pathOfName decl.name, decl)) ++
        ctx.contractDecls
    structs :=
      structs.map (fun decl => (pathOfName decl.name, decl)) ++ ctx.structs
    enums := enums.map (fun decl => (pathOfName decl.name, decl)) ++ ctx.enums
    userValueTypes :=
      userValueTypes.map
        (fun decl => (pathOfName decl.name, decl.underlying)) ++
        ctx.userValueTypes }

def contractStructEntries (contractName : Name) :
    List L00_SourceSolidity.StructDecl ->
    List (Path × L00_SourceSolidity.StructDecl)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl) ::
        (qualifiedPath contractName decl.name, decl) ::
        contractStructEntries contractName rest

def contractEnumEntries (contractName : Name) :
    List L00_SourceSolidity.EnumDecl ->
    List (Path × L00_SourceSolidity.EnumDecl)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl) ::
        (qualifiedPath contractName decl.name, decl) ::
        contractEnumEntries contractName rest

def contractUserValueTypeEntries (contractName : Name) :
    List L00_SourceSolidity.UserValueTypeDecl -> List (Path × Ty)
  | [] => []
  | decl :: rest =>
      (pathOfName decl.name, decl.underlying) ::
        (qualifiedPath contractName decl.name, decl.underlying) ::
        contractUserValueTypeEntries contractName rest

def withContractTypes (ctx : TypeContext) (contractName : Name)
    (structs : List L00_SourceSolidity.StructDecl)
    (enums : List L00_SourceSolidity.EnumDecl)
    (userValueTypes : List L00_SourceSolidity.UserValueTypeDecl) :
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
  | invalidDataLocation : Ty -> Option L00_SourceSolidity.DataLocation ->
      TypeError
  | expectedType : Ty -> Ty -> TypeError
  | expectedBool : Ty -> TypeError
  | expectedNumeric : Ty -> TypeError
  | expectedInteger : Ty -> TypeError
  | expectedLValue : L00_SourceSolidity.Expr -> TypeError
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

end Result

def require (ok : Bool) (err : TypeError) : Except TypeError Unit :=
  if ok then Except.ok () else Except.error err

def requireEqTy (expected actual : Ty) : Except TypeError Unit :=
  require (actual == expected) (TypeError.expectedType expected actual)

def Ty.isBool : Ty -> Bool
  | L00_SourceSolidity.Ty.bool => true
  | _ => false

def Ty.isUnsignedInteger : Ty -> Bool
  | L00_SourceSolidity.Ty.uint _ => true
  | _ => false

def Ty.isSignedInteger : Ty -> Bool
  | L00_SourceSolidity.Ty.int _ => true
  | _ => false

def Ty.isInteger (ty : Ty) : Bool :=
  Ty.isUnsignedInteger ty || Ty.isSignedInteger ty

def Ty.isNumeric : Ty -> Bool
  | L00_SourceSolidity.Ty.uint _ => true
  | L00_SourceSolidity.Ty.int _ => true
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | _ => false

def Ty.isArithmeticOperand : Ty -> Bool
  | L00_SourceSolidity.Ty.uint _ => true
  | L00_SourceSolidity.Ty.int _ => true
  | _ => false

def Ty.isFixedBytesOperand : Ty -> Bool
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | _ => false

def Ty.isBitwiseOperand (ty : Ty) : Bool :=
  Ty.isArithmeticOperand ty || Ty.isFixedBytesOperand ty

def Ty.isRelationalOperand (ty : Ty) : Bool :=
  Ty.isArithmeticOperand ty || Ty.isFixedBytesOperand ty

def Ty.isShiftLeftOperand (ty : Ty) : Bool :=
  Ty.isArithmeticOperand ty || Ty.isFixedBytesOperand ty

def Ty.integerBits? : Ty -> Option Nat
  | L00_SourceSolidity.Ty.uint bits => some bits
  | L00_SourceSolidity.Ty.int bits => some bits
  | _ => none

def Ty.isBuiltInValueTypeShape : Ty -> Bool
  | L00_SourceSolidity.Ty.bool => true
  | L00_SourceSolidity.Ty.address _ => true
  | L00_SourceSolidity.Ty.uint _ => true
  | L00_SourceSolidity.Ty.int _ => true
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | _ => false

def TypeContext.isValueTypeShape (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.bool => true
  | L00_SourceSolidity.Ty.address _ => true
  | L00_SourceSolidity.Ty.uint _ => true
  | L00_SourceSolidity.Ty.int _ => true
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | L00_SourceSolidity.Ty.user path =>
      types.isContractPath path || types.isEnumPath path ||
        types.isUserValueTypePath path
  | L00_SourceSolidity.Ty.function _ _ _ _ => true
  | _ => false

def TypeContext.isConstantStateVarTypeShape
    (types : TypeContext) (ty : Ty) : Bool :=
  TypeContext.isValueTypeShape types ty ||
    ty == L00_SourceSolidity.Ty.bytes ||
      ty == L00_SourceSolidity.Ty.string

def TypeContext.isImmutableStateVarTypeShape
    (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.function _ _ _
      L00_SourceSolidity.Visibility.external_ => false
  | ty => TypeContext.isValueTypeShape types ty

def Ty.isMappingKeyShape (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.bool => true
  | L00_SourceSolidity.Ty.address _ => true
  | L00_SourceSolidity.Ty.uint _ => true
  | L00_SourceSolidity.Ty.int _ => true
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | L00_SourceSolidity.Ty.bytes => true
  | L00_SourceSolidity.Ty.string => true
  | L00_SourceSolidity.Ty.user path =>
      types.isContractPath path || types.isEnumPath path ||
        types.isUserValueTypePath path
  | _ => false

def Ty.needsDataLocation (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.bytes => true
  | L00_SourceSolidity.Ty.string => true
  | L00_SourceSolidity.Ty.array _ _ => true
  | L00_SourceSolidity.Ty.mapping _ _ => true
  | L00_SourceSolidity.Ty.user path => types.isStructPath path
  | _ => false

mutual

def Ty.isExternalFunctionAbiTypeShape (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, L00_SourceSolidity.Ty.bool => true
  | _ + 1, L00_SourceSolidity.Ty.address _ => true
  | _ + 1, L00_SourceSolidity.Ty.uint _ => true
  | _ + 1, L00_SourceSolidity.Ty.int _ => true
  | _ + 1, L00_SourceSolidity.Ty.bytesN _ => true
  | _ + 1, L00_SourceSolidity.Ty.fixedBytes _ => true
  | _ + 1, L00_SourceSolidity.Ty.bytes => true
  | _ + 1, L00_SourceSolidity.Ty.string => true
  | fuel + 1, L00_SourceSolidity.Ty.array element _ =>
      Ty.isExternalFunctionAbiTypeShape types fuel element
  | fuel + 1, L00_SourceSolidity.Ty.tuple tys =>
      Tys.allExternalFunctionAbiTypeShape types fuel tys
  | fuel + 1, L00_SourceSolidity.Ty.user path =>
      if types.isContractPath path || types.isEnumPath path then
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
  | fuel + 1, L00_SourceSolidity.Ty.function params returns _ visibility =>
      visibility == L00_SourceSolidity.Visibility.external_ &&
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
    (fuel : Nat) : List L00_SourceSolidity.StructField -> Bool
  | [] => true
  | field :: rest =>
      Ty.isExternalFunctionAbiTypeShape types fuel field.ty &&
        StructFields.allExternalFunctionAbiTypeShape types fuel rest

end

mutual

def Ty.isValid (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.uint bits =>
      bits > 0 && bits <= 256 && bits % 8 == 0
  | L00_SourceSolidity.Ty.int bits =>
      bits > 0 && bits <= 256 && bits % 8 == 0
  | L00_SourceSolidity.Ty.bytesN size => size > 0 && size <= 32
  | L00_SourceSolidity.Ty.fixedBytes size => size > 0 && size <= 32
  | L00_SourceSolidity.Ty.array element none => Ty.isValid types element
  | L00_SourceSolidity.Ty.array element (some size) =>
      size > 0 && Ty.isValid types element
  | L00_SourceSolidity.Ty.mapping key value =>
      Ty.isValid types key && Ty.isValid types value &&
        Ty.isMappingKeyShape types key
  | L00_SourceSolidity.Ty.tuple tys => Tys.allValid types tys
  | L00_SourceSolidity.Ty.user path => types.isKnownPath path
  | L00_SourceSolidity.Ty.function params returns _ visibility =>
      Tys.allValid types params && Tys.allValid types returns &&
        (visibility == L00_SourceSolidity.Visibility.internal_ ||
          (visibility == L00_SourceSolidity.Visibility.external_ &&
            Tys.allExternalFunctionAbiTypeShape types 64 params &&
              Tys.allExternalFunctionAbiTypeShape types 64 returns))
  | _ => true

def Tys.allValid (types : TypeContext) : List Ty -> Bool
  | [] => true
  | ty :: rest => Ty.isValid types ty && Tys.allValid types rest

end

mutual

def Ty.containsMapping (types : TypeContext) : Nat -> Ty -> Bool
  | 0, _ => false
  | _ + 1, L00_SourceSolidity.Ty.mapping _ _ => true
  | fuel + 1, L00_SourceSolidity.Ty.array element _ =>
      Ty.containsMapping types fuel element
  | fuel + 1, L00_SourceSolidity.Ty.tuple tys =>
      Tys.containsMapping types fuel tys
  | fuel + 1, L00_SourceSolidity.Ty.user path =>
      match types.lookupStruct? path with
      | some structDecl => StructFields.containsMapping types fuel structDecl.fields
      | none => false
  | fuel + 1, L00_SourceSolidity.Ty.function params returns _ _ =>
      Tys.containsMapping types fuel params ||
        Tys.containsMapping types fuel returns
  | _, _ => false

def Tys.containsMapping (types : TypeContext) (fuel : Nat) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.containsMapping types fuel ty || Tys.containsMapping types fuel rest

def StructFields.containsMapping (types : TypeContext) (fuel : Nat) :
    List L00_SourceSolidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      Ty.containsMapping types fuel field.ty ||
        StructFields.containsMapping types fuel rest

end

mutual

def Ty.omittedFromStructPublicGetter? (types : TypeContext) :
    Nat -> Ty -> Bool
  | 0, _ => true
  | _ + 1, L00_SourceSolidity.Ty.mapping _ _ => true
  | _ + 1, L00_SourceSolidity.Ty.array _ _ => true
  | fuel + 1, L00_SourceSolidity.Ty.tuple tys =>
      Tys.omittedFromStructPublicGetter? types fuel tys
  | fuel + 1, L00_SourceSolidity.Ty.user path =>
      match types.lookupStruct? path with
      | some structDecl =>
          StructFields.omittedFromStructPublicGetter?
            types fuel structDecl.fields
      | none => false
  | _ + 1, _ => false

def Tys.omittedFromStructPublicGetter? (types : TypeContext)
    (fuel : Nat) : List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.omittedFromStructPublicGetter? types fuel ty ||
        Tys.omittedFromStructPublicGetter? types fuel rest

def StructFields.omittedFromStructPublicGetter?
    (types : TypeContext) (fuel : Nat) :
    List L00_SourceSolidity.StructField -> Bool
  | [] => false
  | field :: rest =>
      Ty.omittedFromStructPublicGetter? types fuel field.ty ||
        StructFields.omittedFromStructPublicGetter? types fuel rest

end

def structGetterReturnTys (types : TypeContext) :
    List L00_SourceSolidity.StructField -> List Ty
  | [] => []
  | field :: rest =>
      if Ty.omittedFromStructPublicGetter? types 64 field.ty then
        structGetterReturnTys types rest
      else
        field.ty :: structGetterReturnTys types rest

def Ty.publicGetterShape? (types : TypeContext) :
    Nat -> Ty -> Option (List Ty × List Ty)
  | 0, _ => none
  | fuel + 1, L00_SourceSolidity.Ty.mapping key value => do
      let tail ← Ty.publicGetterShape? types fuel value
      some (key :: tail.fst, tail.snd)
  | fuel + 1, L00_SourceSolidity.Ty.array element _ => do
      let tail ← Ty.publicGetterShape? types fuel element
      some (L00_SourceSolidity.Ty.uint 256 :: tail.fst, tail.snd)
  | _ + 1, L00_SourceSolidity.Ty.user path =>
      match types.lookupStruct? path with
      | some structDecl =>
          some ([], structGetterReturnTys types structDecl.fields)
      | none => some ([], [L00_SourceSolidity.Ty.user path])
  | _ + 1, ty => some ([], [ty])

mutual

def TypeContext.abiCanonicalFuel? (types : TypeContext) :
    Nat -> Ty -> Option String
  | 0, _ => none
  | _ + 1, L00_SourceSolidity.Ty.bool => some "bool"
  | _ + 1, L00_SourceSolidity.Ty.address _ => some "address"
  | _ + 1, L00_SourceSolidity.Ty.uint bits =>
      if bits == 0 then
        some "uint256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("uint" ++ toString bits)
      else
        none
  | _ + 1, L00_SourceSolidity.Ty.int bits =>
      if bits == 0 then
        some "int256"
      else if bits % 8 == 0 && bits <= 256 then
        some ("int" ++ toString bits)
      else
        none
  | _ + 1, L00_SourceSolidity.Ty.bytesN size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | _ + 1, L00_SourceSolidity.Ty.fixedBytes size =>
      if 0 < size && size <= 32 then
        some ("bytes" ++ toString size)
      else
        none
  | _ + 1, L00_SourceSolidity.Ty.bytes => some "bytes"
  | _ + 1, L00_SourceSolidity.Ty.string => some "string"
  | fuel + 1, L00_SourceSolidity.Ty.array ty none => do
      let base ← TypeContext.abiCanonicalFuel? types fuel ty
      some (base ++ "[]")
  | fuel + 1, L00_SourceSolidity.Ty.array ty (some size) => do
      let base ← TypeContext.abiCanonicalFuel? types fuel ty
      some (base ++ "[" ++ toString size ++ "]")
  | fuel + 1, L00_SourceSolidity.Ty.tuple tys => do
      let elements ← TypeContext.abiCanonicalListFuel? types fuel tys
      some ("(" ++
        L00_SourceSolidity.Executable.joinStringsWith "," elements ++ ")")
  | fuel + 1, L00_SourceSolidity.Ty.user path =>
      match types.lookupContractDecl? path with
      | some _ => some "address"
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
  | _ + 1, L00_SourceSolidity.Ty.function _ _ _ visibility =>
      if visibility == L00_SourceSolidity.Visibility.external_ then
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
    (decl : L00_SourceSolidity.StructDecl) : Option String := do
  let elements ← StructFields.abiCanonicalFuel? types fuel decl.fields
  some ("(" ++
    L00_SourceSolidity.Executable.joinStringsWith "," elements ++ ")")

def StructFields.abiCanonicalFuel? (types : TypeContext) (fuel : Nat) :
    List L00_SourceSolidity.StructField -> Option (List String)
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
    (actual expected : L00_SourceSolidity.StateMutability) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | L00_SourceSolidity.StateMutability.pure,
      L00_SourceSolidity.StateMutability.view => true
    | L00_SourceSolidity.StateMutability.pure,
      L00_SourceSolidity.StateMutability.nonpayable => true
    | L00_SourceSolidity.StateMutability.view,
      L00_SourceSolidity.StateMutability.nonpayable => true
    | L00_SourceSolidity.StateMutability.payable,
      L00_SourceSolidity.StateMutability.nonpayable => true
    | _, _ => false

def Ty.canImplicitlyConvert (actual expected : Ty) : Bool :=
  if actual == expected then
    true
  else
    match actual, expected with
    | L00_SourceSolidity.Ty.address true,
      L00_SourceSolidity.Ty.address false => true
    | L00_SourceSolidity.Ty.uint actualBits,
      L00_SourceSolidity.Ty.uint expectedBits => actualBits <= expectedBits
    | L00_SourceSolidity.Ty.int actualBits,
      L00_SourceSolidity.Ty.int expectedBits => actualBits <= expectedBits
    | L00_SourceSolidity.Ty.uint actualBits,
      L00_SourceSolidity.Ty.int expectedBits => actualBits < expectedBits
    | L00_SourceSolidity.Ty.bytesN actualSize,
      L00_SourceSolidity.Ty.bytesN expectedSize => actualSize <= expectedSize
    | L00_SourceSolidity.Ty.fixedBytes actualSize,
      L00_SourceSolidity.Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | L00_SourceSolidity.Ty.bytesN actualSize,
      L00_SourceSolidity.Ty.fixedBytes expectedSize =>
        actualSize <= expectedSize
    | L00_SourceSolidity.Ty.fixedBytes actualSize,
      L00_SourceSolidity.Ty.bytesN expectedSize =>
        actualSize <= expectedSize
    | L00_SourceSolidity.Ty.function actualParams actualReturns
        actualMutability actualVisibility,
      L00_SourceSolidity.Ty.function expectedParams expectedReturns
        expectedMutability expectedVisibility =>
        actualParams == expectedParams &&
          actualReturns == expectedReturns &&
          actualVisibility == expectedVisibility &&
          StateMutability.canImplicitlyConvertFunction
            actualMutability expectedMutability
    | _, _ => false

def Ty.fixedBytesSize? : Ty -> Option Nat
  | L00_SourceSolidity.Ty.bytesN size =>
      if 0 < size && size <= 32 then some size else none
  | L00_SourceSolidity.Ty.fixedBytes size =>
      if 0 < size && size <= 32 then some size else none
  | _ => none

def Ty.isFixedBytes (ty : Ty) : Bool :=
  match Ty.fixedBytesSize? ty with
  | some _ => true
  | none => false

def Ty.uintBits? : Ty -> Option Nat
  | L00_SourceSolidity.Ty.uint bits =>
      if bits > 0 && bits <= 256 && bits % 8 == 0 then some bits else none
  | _ => none

def Ty.intBits? : Ty -> Option Nat
  | L00_SourceSolidity.Ty.int bits =>
      if bits > 0 && bits <= 256 && bits % 8 == 0 then some bits else none
  | _ => none

def Ty.isSignedIntegerTy : Ty -> Bool
  | L00_SourceSolidity.Ty.int _ => true
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

def Ty.fixedBytesIntegerSameSize (fixedTy intTy : Ty) : Bool :=
  match fixedTy.fixedBytesSize?, intTy.integerBits? with
  | some size, some bits => size * 8 == bits
  | _, _ => false

def TypeContext.isContractTy (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.user path => types.isContractPath path
  | _ => false

def TypeContext.isEnumTy (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.user path => types.isEnumPath path
  | _ => false

def TypeContext.isUserValueTy (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.user path => types.isUserValueTypePath path
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

def TypeContext.canImplicitlyConvert (types : TypeContext)
    (actual expected : Ty) : Bool :=
  if Ty.canImplicitlyConvert actual expected then
    true
  else
    match actual, expected with
    | L00_SourceSolidity.Ty.user actualPath,
      L00_SourceSolidity.Ty.user expectedPath =>
        types.isContractPath actualPath &&
          types.isContractPath expectedPath &&
          TypeContext.contractHasAncestorPathFuel types 64
            actualPath expectedPath
    | _, _ => false

def typeConversionLiteralFits (target : Ty)
    (expr : L00_SourceSolidity.Expr) : Bool :=
  match L00_SourceSolidity.Executable.Expr.toCoreNumericLiteralAs? target expr with
  | some _ => true
  | none =>
      match L00_SourceSolidity.Executable.Expr.toCoreFixedBytesLiteralAs?
          target expr with
      | some _ => true
      | none =>
          match target with
          | L00_SourceSolidity.Ty.address false =>
              match L00_SourceSolidity.Executable.Expr.toCoreAddressLiteral?
                  expr with
              | some _ => true
              | none => false
          | _ => false

def implicitLiteralFits (target : Ty)
    (expr : L00_SourceSolidity.Expr) : Bool :=
  match L00_SourceSolidity.Executable.Expr.toCoreNumericLiteralAs? target expr with
  | some _ => true
  | none =>
      match L00_SourceSolidity.Executable.Expr.toCoreFixedBytesLiteralAs?
          target expr with
      | some _ => true
      | none => false

def Ty.canExplicitlyConvert (types : TypeContext)
    (sourceExpr : L00_SourceSolidity.Expr) (actual target : Ty) : Bool :=
  if actual == target then
    true
  else
    match actual, target with
    | _, L00_SourceSolidity.Ty.address true => false
    | L00_SourceSolidity.Ty.address _, L00_SourceSolidity.Ty.address false => true
    | L00_SourceSolidity.Ty.uint 160, L00_SourceSolidity.Ty.address false => true
    | L00_SourceSolidity.Ty.bytesN 20, L00_SourceSolidity.Ty.address false => true
    | L00_SourceSolidity.Ty.fixedBytes 20, L00_SourceSolidity.Ty.address false => true
    | L00_SourceSolidity.Ty.user path, L00_SourceSolidity.Ty.address false =>
        types.isContractPath path
    | _, L00_SourceSolidity.Ty.address false =>
        typeConversionLiteralFits target sourceExpr
    | _, L00_SourceSolidity.Ty.uint _ =>
        Ty.integerExplicitConversionAllowed actual target ||
          Ty.fixedBytesIntegerSameSize actual target ||
          (match actual with
          | L00_SourceSolidity.Ty.address _ =>
              target == L00_SourceSolidity.Ty.uint 160
          | _ => false) ||
          typeConversionLiteralFits target sourceExpr
    | _, L00_SourceSolidity.Ty.int _ =>
        Ty.integerExplicitConversionAllowed actual target ||
          Ty.fixedBytesIntegerSameSize actual target ||
          typeConversionLiteralFits target sourceExpr
    | _, L00_SourceSolidity.Ty.bytesN _ =>
        (actual.isFixedBytes || actual == L00_SourceSolidity.Ty.bytes ||
          Ty.fixedBytesIntegerSameSize target actual) ||
          typeConversionLiteralFits target sourceExpr
    | _, L00_SourceSolidity.Ty.fixedBytes _ =>
        (actual.isFixedBytes || actual == L00_SourceSolidity.Ty.bytes ||
          Ty.fixedBytesIntegerSameSize target actual) ||
          typeConversionLiteralFits target sourceExpr
    | L00_SourceSolidity.Ty.address _, L00_SourceSolidity.Ty.user path =>
        types.isContractPath path
    | L00_SourceSolidity.Ty.user actualPath, L00_SourceSolidity.Ty.user targetPath =>
        if types.isContractPath actualPath && types.isContractPath targetPath then
          types.contractsRelated actualPath targetPath
        else if types.isEnumPath targetPath then
          actual.isInteger
        else
          false
    | _, L00_SourceSolidity.Ty.user path =>
        if types.isEnumPath path then
          actual.isInteger || typeConversionLiteralFits (L00_SourceSolidity.Ty.uint 8) sourceExpr
        else
          false
    | _, _ => false

def checkTy (types : TypeContext) (ty : Ty) : Except TypeError Unit :=
  require (Ty.isValid types ty) (TypeError.invalidType ty)

def checkLocationForTy (types : TypeContext) (ty : Ty)
    (location : Option L00_SourceSolidity.DataLocation) :
    Except TypeError Unit := do
  checkTy types ty
  if !Ty.needsDataLocation types ty && location.isSome then
    Except.error (TypeError.invalidDataLocation ty location)
  else if Ty.needsDataLocation types ty && location.isNone then
    Except.error (TypeError.invalidDataLocation ty location)
  else if Ty.containsMapping types 64 ty then
    match location with
    | some L00_SourceSolidity.DataLocation.storage => Except.ok ()
    | _ => Except.error (TypeError.invalidDataLocation ty location)
  else
    Except.ok ()

structure FunctionSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  paramStorageRefs : List Bool := []
  returns : List Ty := []
  visibility : Option L00_SourceSolidity.Visibility := none
  mutability : L00_SourceSolidity.StateMutability :=
    L00_SourceSolidity.StateMutability.nonpayable
  deriving Repr

structure ModifierSig where
  name : Name
  params : List Ty := []
  paramNames : List (Option Name) := []
  paramStorageRefs : List Bool := []
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
  deriving Repr

structure CheckEnv where
  types : TypeContext := {}
  vars : TypeEnv := []
  stateNames : List Name := []
  localNames : List Name := []
  localStorageRefs : List Name := []
  localDataLocations : List (Name × L00_SourceSolidity.DataLocation) := []
  constantBindings : List (Name × Bool) := []
  immutableNames : List Name := []
  functions : List FunctionSig := []
  superFunctions : List FunctionSig := []
  modifiers : List ModifierSig := []
  modifierDecls : List L00_SourceSolidity.ModifierDecl := []
  usingDecls : List L00_SourceSolidity.UsingDecl := []
  errors : List ErrorSig := []
  events : List EventSig := []
  contractKind : Option L00_SourceSolidity.ContractKind := none
  currentContract : Option Path := none
  ancestorPaths : List Path := []
  currentMutability : Option L00_SourceSolidity.StateMutability := none
  returnTys : List Ty := []
  loopDepth : Nat := 0
  inModifier : Bool := false
  inUnchecked : Bool := false
  inConstructor : Bool := false
  deriving Repr

def CheckEnv.lookupVar? (env : CheckEnv) (name : Name) : Option Ty :=
  L00_SourceSolidity.Executable.TypeEnv.lookup? env.vars name

def CheckEnv.isStateName (env : CheckEnv) (name : Name) : Bool :=
  L00_SourceSolidity.Executable.nameIn name env.stateNames

def CheckEnv.isLocalName (env : CheckEnv) (name : Name) : Bool :=
  L00_SourceSolidity.Executable.nameIn name env.localNames

def CheckEnv.isLocalStorageRef (env : CheckEnv) (name : Name) : Bool :=
  L00_SourceSolidity.Executable.nameIn name env.localStorageRefs

def CheckEnv.lookupLocalDataLocation? (env : CheckEnv)
    (name : Name) : Option L00_SourceSolidity.DataLocation :=
  let rec go : List (Name × L00_SourceSolidity.DataLocation) ->
      Option L00_SourceSolidity.DataLocation
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
    L00_SourceSolidity.Executable.nameIn name env.immutableNames

def CheckEnv.extendDataLocations (env : CheckEnv)
    (locations : List (Name × L00_SourceSolidity.DataLocation)) :
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
  env.contractKind == some L00_SourceSolidity.ContractKind.library

def CheckEnv.enterLoop (env : CheckEnv) : CheckEnv :=
  { env with loopDepth := env.loopDepth + 1 }

def CheckEnv.enterModifier (env : CheckEnv) : CheckEnv :=
  { env with inModifier := true, inConstructor := false }

def CheckEnv.enterUnchecked (env : CheckEnv) : CheckEnv :=
  { env with inUnchecked := true }

def lookupModifierDeclIn? (target : Name) :
    List L00_SourceSolidity.ModifierDecl ->
    Option L00_SourceSolidity.ModifierDecl
  | [] => none
  | decl :: rest =>
      if decl.name == target then
        some decl
      else
        lookupModifierDeclIn? target rest

def CheckEnv.lookupModifierDecl? (env : CheckEnv) (target : Name) :
    Option L00_SourceSolidity.ModifierDecl :=
  lookupModifierDeclIn? target env.modifierDecls

def CheckEnv.isCurrentOrAncestorContract (env : CheckEnv)
    (path : Path) : Bool :=
  match env.currentContract with
  | some current =>
      TypeContext.pathMatches current path ||
        TypeContext.pathIn path env.ancestorPaths
  | none => false

def mutabilityAllowsStateRead :
    Option L00_SourceSolidity.StateMutability -> Bool
  | some L00_SourceSolidity.StateMutability.pure => false
  | _ => true

def mutabilityAllowsStateWrite :
    Option L00_SourceSolidity.StateMutability -> Bool
  | some L00_SourceSolidity.StateMutability.pure => false
  | some L00_SourceSolidity.StateMutability.view => false
  | _ => true

def mutabilityAllowsLogOrCreate :
    Option L00_SourceSolidity.StateMutability -> Bool :=
  mutabilityAllowsStateWrite

def mutabilityAllowsCall
    (caller : Option L00_SourceSolidity.StateMutability)
    (callee : L00_SourceSolidity.StateMutability) : Bool :=
  match caller with
  | some L00_SourceSolidity.StateMutability.pure =>
      callee == L00_SourceSolidity.StateMutability.pure
  | some L00_SourceSolidity.StateMutability.view =>
      callee == L00_SourceSolidity.StateMutability.pure ||
        callee == L00_SourceSolidity.StateMutability.view
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
    (callee : L00_SourceSolidity.StateMutability) :
    Except TypeError Unit :=
  require (mutabilityAllowsCall env.currentMutability callee)
    (TypeError.mutabilityViolation
      "call mutability exceeds current function mutability")

def callMemberMutability? (member : Name) :
    Option L00_SourceSolidity.StateMutability :=
  if member == "staticcall" then
    some L00_SourceSolidity.StateMutability.view
  else if member == "call" || member == "delegatecall" ||
      member == "send" || member == "transfer" then
    some L00_SourceSolidity.StateMutability.nonpayable
  else
    none

def requireCallExprMutabilityAllowed (env : CheckEnv)
    (fn : L00_SourceSolidity.Expr) : Except TypeError Unit :=
  match fn with
  | L00_SourceSolidity.Expr.member _ member =>
      match callMemberMutability? member with
      | some mutability => requireCallMutabilityAllowed env mutability
      | none => Except.ok ()
  | _ => Except.ok ()

def builtinIdentCallMutability? (name : Name) :
    Option L00_SourceSolidity.StateMutability :=
  if name == "blockhash" || name == "blobhash" then
    some L00_SourceSolidity.StateMutability.view
  else
    none

def requireBuiltinIdentCallAllowed (env : CheckEnv) (name : Name) :
    Except TypeError Unit :=
  match builtinIdentCallMutability? name with
  | some mutability => requireCallMutabilityAllowed env mutability
  | none => Except.ok ()

def namesUniqueFrom (seen : List Name) : List Name -> Bool
  | [] => true
  | name :: rest =>
      !L00_SourceSolidity.Executable.nameIn name seen &&
        namesUniqueFrom (name :: seen) rest

def namesUnique (names : List Name) : Bool :=
  namesUniqueFrom [] names

def ensureUniqueNames (what : String) (names : List Name) :
    Except TypeError Unit :=
  match names with
  | [] => Except.ok ()
  | name :: rest =>
      if L00_SourceSolidity.Executable.nameIn name rest then
        Except.error (TypeError.duplicateName what name)
      else
        ensureUniqueNames what rest

def ensureNamesDisjointFrom (what : String) (reserved : List Name) :
    List Name -> Except TypeError Unit
  | [] => Except.ok ()
  | name :: rest => do
      require (!L00_SourceSolidity.Executable.nameIn name reserved)
        (TypeError.duplicateName what name)
      ensureNamesDisjointFrom what reserved rest

def Parameter.check (types : TypeContext)
    (param : L00_SourceSolidity.Parameter) :
    Except TypeError Unit :=
  checkLocationForTy types param.ty param.location

def Parameter.hasStorageLocation
    (param : L00_SourceSolidity.Parameter) : Bool :=
  param.location == some L00_SourceSolidity.DataLocation.storage

def Parameter.isStorageRef (types : TypeContext)
    (param : L00_SourceSolidity.Parameter) : Bool :=
  Ty.needsDataLocation types param.ty &&
    Parameter.hasStorageLocation param

def Parameters.check (types : TypeContext) :
    List L00_SourceSolidity.Parameter ->
    Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      Parameter.check types param
      Parameters.check types rest

def Parameters.namedTypes : List L00_SourceSolidity.Parameter ->
    List (Name × Ty)
  | [] => []
  | param :: rest =>
      match param.name with
      | some name => (name, param.ty) :: Parameters.namedTypes rest
      | none => Parameters.namedTypes rest

def Parameters.namedTypeStorageRefs (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> List (Name × Ty × Bool)
  | [] => []
  | param :: rest =>
      match param.name with
      | some name =>
          (name, param.ty, Parameter.isStorageRef types param) ::
            Parameters.namedTypeStorageRefs types rest
      | none => Parameters.namedTypeStorageRefs types rest

def Parameters.namedDataLocations (types : TypeContext) :
    List L00_SourceSolidity.Parameter ->
    List (Name × L00_SourceSolidity.DataLocation)
  | [] => []
  | param :: rest =>
      match param.name, param.location with
      | some name, some location =>
          if Ty.needsDataLocation types param.ty then
            (name, location) :: Parameters.namedDataLocations types rest
          else
            Parameters.namedDataLocations types rest
      | _, _ => Parameters.namedDataLocations types rest

def Parameters.tys (params : List L00_SourceSolidity.Parameter) : List Ty :=
  params.map L00_SourceSolidity.Parameter.ty

def Parameters.storageRefFlags (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> List Bool
  | [] => []
  | param :: rest =>
      Parameter.isStorageRef types param ::
        Parameters.storageRefFlags types rest

def Parameters.storageLocationFlags :
    List L00_SourceSolidity.Parameter -> List Bool
  | [] => []
  | param :: rest =>
      Parameter.hasStorageLocation param ::
        Parameters.storageLocationFlags rest

def Parameters.anyStorageRef (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> Bool
  | [] => false
  | param :: rest =>
      Parameter.isStorageRef types param ||
        Parameters.anyStorageRef types rest

def Parameters.anyCalldata : List L00_SourceSolidity.Parameter -> Bool
  | [] => false
  | param :: rest =>
      param.location == some L00_SourceSolidity.DataLocation.calldata ||
        Parameters.anyCalldata rest

def Parameters.firstMappingContainingTy? (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> Option Ty
  | [] => none
  | param :: rest =>
      if Ty.containsMapping types 64 param.ty then
        some param.ty
      else
        Parameters.firstMappingContainingTy? types rest

def Parameters.firstNonAbiEncodableTy? (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> Option Ty
  | [] => none
  | param :: rest =>
      if TypeContext.isAbiEncodable types param.ty then
        Parameters.firstNonAbiEncodableTy? types rest
      else
        some param.ty

def FunctionDecl.signature? (fn : L00_SourceSolidity.FunctionDecl) :
    Option FunctionSig :=
  match fn.kind, fn.name with
  | L00_SourceSolidity.FunctionKind.function, some name =>
      some
        { name := name
          params := Parameters.tys fn.params
          paramNames := fn.params.map L00_SourceSolidity.Parameter.name
          paramStorageRefs := Parameters.storageLocationFlags fn.params
          returns := Parameters.tys fn.returns
          visibility := fn.visibility
          mutability := fn.mutability }
  | _, _ => none

def FunctionDecls.signatures : List L00_SourceSolidity.FunctionDecl ->
    List FunctionSig
  | [] => []
  | fn :: rest =>
      match FunctionDecl.signature? fn with
      | some sig => sig :: FunctionDecls.signatures rest
      | none => FunctionDecls.signatures rest

def FunctionDecl.constructorSignature? (fn : L00_SourceSolidity.FunctionDecl) :
    Option FunctionSig :=
  if fn.kind == L00_SourceSolidity.FunctionKind.constructor then
    some
      { name := "constructor"
        params := Parameters.tys fn.params
        paramNames := fn.params.map L00_SourceSolidity.Parameter.name
        paramStorageRefs := Parameters.storageLocationFlags fn.params
        returns := []
        visibility := none
        mutability := fn.mutability }
  else
    none

def ContractItems.constructorSignature? :
    List L00_SourceSolidity.ContractItem -> Option FunctionSig
  | [] => none
  | L00_SourceSolidity.ContractItem.function fn :: rest =>
      match FunctionDecl.constructorSignature? fn with
      | some sig => some sig
      | none => ContractItems.constructorSignature? rest
  | _ :: rest => ContractItems.constructorSignature? rest

def ContractDecl.defaultConstructorSignature
    (decl : L00_SourceSolidity.ContractDecl) : FunctionSig :=
  { name := decl.name
    params := []
    paramNames := []
    returns := []
    visibility := none
    mutability := L00_SourceSolidity.StateMutability.nonpayable }

def ContractDecl.constructorSignature
    (decl : L00_SourceSolidity.ContractDecl) : FunctionSig :=
  match ContractItems.constructorSignature? decl.items with
  | some sig => sig
  | none => ContractDecl.defaultConstructorSignature decl

def ModifierDecl.signature (modifier : L00_SourceSolidity.ModifierDecl) :
    ModifierSig :=
  { name := modifier.name
    params := Parameters.tys modifier.params
    paramNames := modifier.params.map L00_SourceSolidity.Parameter.name
    paramStorageRefs := Parameters.storageLocationFlags modifier.params }

def EventDecl.signature (event : L00_SourceSolidity.EventDecl) : EventSig :=
  { name := event.name
    params := event.params.map (fun param => param.ty)
    paramNames := event.params.map L00_SourceSolidity.EventParam.name }

def ErrorDecl.signature (err : L00_SourceSolidity.ErrorDecl) : ErrorSig :=
  { name := err.name
    params := Parameters.tys err.params
    paramNames := err.params.map L00_SourceSolidity.Parameter.name }

def EnumDecl.hasCase (decl : L00_SourceSolidity.EnumDecl)
    (target : Name) : Bool :=
  L00_SourceSolidity.Executable.nameIn target decl.cases

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

def resultTyFromReturns : List Ty -> Ty
  | [] => L00_SourceSolidity.Ty.tuple []
  | [ty] => ty
  | tys => L00_SourceSolidity.Ty.tuple tys

def FunctionSig.sameSignature (a b : FunctionSig) : Bool :=
  a.name == b.name && a.params == b.params

def FunctionSig.externallyCallable (sig : FunctionSig) : Bool :=
  sig.visibility == some L00_SourceSolidity.Visibility.public_ ||
    sig.visibility == some L00_SourceSolidity.Visibility.external_

def FunctionSig.abiParamTypes? (types : TypeContext)
    (sig : FunctionSig) : Option (List String) :=
  TypeContext.abiCanonicalList? types sig.params

def FunctionSig.sameExternalAbiSignature
    (types : TypeContext) (a b : FunctionSig) : Bool :=
  if a.name == b.name && a.externallyCallable && b.externallyCallable then
    match a.abiParamTypes? types, b.abiParamTypes? types with
    | some aParams, some bParams => aParams == bParams
    | _, _ => false
  else
    false

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

def FunctionSigs.resolveLoop (target : Name) (args : List ArgInfo) :
    Option FunctionSig -> List FunctionSig ->
    Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target && sig.matchesArgs args then
        match found? with
        | none => FunctionSigs.resolveLoop target args (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        FunctionSigs.resolveLoop target args found? rest

def FunctionSigs.resolve (functions : List FunctionSig)
    (target : Name) (args : List ArgInfo) : Except TypeError FunctionSig :=
  FunctionSigs.resolveLoop target args none functions

def FunctionSig.internallyCallable (sig : FunctionSig) : Bool :=
  !(sig.visibility == some L00_SourceSolidity.Visibility.external_)

def FunctionSig.nonPrivate (sig : FunctionSig) : Bool :=
  !(sig.visibility == some L00_SourceSolidity.Visibility.private_)

def FunctionSig.internalFunctionValueTy? (sig : FunctionSig) :
    Option Ty :=
  if sig.internallyCallable then
    some
      (L00_SourceSolidity.Ty.function sig.params sig.returns
        sig.mutability L00_SourceSolidity.Visibility.internal_)
  else
    none

def FunctionSig.internalFunctionValueAssignableTo
    (types : TypeContext) (expected : Ty) (sig : FunctionSig) : Bool :=
  match FunctionSig.internalFunctionValueTy? sig with
  | some actual => TypeContext.canImplicitlyConvert types actual expected
  | none => false

namespace FunctionSigs

def resolveInternalFunctionValueLoop (types : TypeContext)
    (target : Name) (expected : Ty) :
    Option FunctionSig -> List FunctionSig ->
    Except TypeError FunctionSig
  | none, [] => Except.error (TypeError.unknownFunction target)
  | some found, [] => Except.ok found
  | found?, sig :: rest =>
      if sig.name == target &&
          FunctionSig.internalFunctionValueAssignableTo
            types expected sig then
        match found? with
        | none =>
            resolveInternalFunctionValueLoop types target expected
              (some sig) rest
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveInternalFunctionValueLoop types target expected found? rest

def resolveInternalFunctionValueAssignableTo (types : TypeContext)
    (functions : List FunctionSig) (target : Name) (expected : Ty) :
    Except TypeError FunctionSig :=
  resolveInternalFunctionValueLoop types target expected none functions

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
        | some _ => Except.error (TypeError.ambiguousFunction target)
      else
        resolveInternalFunctionValueByNameLoop target found? rest

def resolveInternalFunctionValueByName
    (functions : List FunctionSig) (target : Name) :
    Except TypeError FunctionSig :=
  resolveInternalFunctionValueByNameLoop target none functions

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

end FunctionSigs

def ContractDecl.directFunctionSigs
    (decl : L00_SourceSolidity.ContractDecl) : List FunctionSig :=
  decl.items.filterMap
    (fun item =>
      match item with
      | L00_SourceSolidity.ContractItem.function fn =>
          FunctionDecl.signature? fn
      | _ => none)

def StateVarDecl.publicGetterFunctionSig?
    (types : TypeContext) (decl : L00_SourceSolidity.StateVarDecl) :
    Option FunctionSig :=
  match decl.visibility with
  | some L00_SourceSolidity.Visibility.public_ => do
      let shape ← Ty.publicGetterShape? types 64 decl.ty
      some
        { name := decl.name
          params := shape.fst
          paramNames := List.replicate shape.fst.length none
          paramStorageRefs := List.replicate shape.fst.length false
          returns := shape.snd
          visibility := some L00_SourceSolidity.Visibility.external_
          mutability := L00_SourceSolidity.StateMutability.view }
  | _ => none

def ContractDecl.directPublicGetterSigs
    (types : TypeContext) (decl : L00_SourceSolidity.ContractDecl) :
    List FunctionSig :=
  decl.items.filterMap
    (fun item =>
      match item with
      | L00_SourceSolidity.ContractItem.stateVar stateVar =>
          StateVarDecl.publicGetterFunctionSig? types stateVar
      | _ => none)

def ContractDecl.directExternalFunctionSigs
    (types : TypeContext) (decl : L00_SourceSolidity.ContractDecl) :
    List FunctionSig :=
  ContractDecl.directFunctionSigs decl ++
    ContractDecl.directPublicGetterSigs types decl

def ContractDecl.directModifierDecls
    (decl : L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.ModifierDecl :=
  decl.items.filterMap
    (fun item =>
      match item with
      | L00_SourceSolidity.ContractItem.modifierDecl modifier =>
          some modifier
      | _ => none)

namespace ModifierDecls

def containsName (name : Name) :
    List L00_SourceSolidity.ModifierDecl -> Bool
  | [] => false
  | modifier :: rest =>
      modifier.name == name || containsName name rest

def addIfNewName (modifiers : List L00_SourceSolidity.ModifierDecl)
    (modifier : L00_SourceSolidity.ModifierDecl) :
    List L00_SourceSolidity.ModifierDecl :=
  if containsName modifier.name modifiers then
    modifiers
  else
    modifiers ++ [modifier]

def addAllIfNewName (modifiers : List L00_SourceSolidity.ModifierDecl) :
    List L00_SourceSolidity.ModifierDecl ->
    List L00_SourceSolidity.ModifierDecl
  | [] => modifiers
  | modifier :: rest =>
      addAllIfNewName (addIfNewName modifiers modifier) rest

def signatures (modifiers : List L00_SourceSolidity.ModifierDecl) :
    List ModifierSig :=
  modifiers.map ModifierDecl.signature

end ModifierDecls

def ContractDecl.modifierDeclsFromOrderFrom
    (modifiers : List L00_SourceSolidity.ModifierDecl) :
    List L00_SourceSolidity.ContractDecl ->
    List L00_SourceSolidity.ModifierDecl
  | [] => modifiers
  | decl :: rest =>
      ContractDecl.modifierDeclsFromOrderFrom
        (ModifierDecls.addAllIfNewName modifiers
          (ContractDecl.directModifierDecls decl))
        rest

def ContractDecl.modifierDeclsFromOrder
    (order : List L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.ModifierDecl :=
  ContractDecl.modifierDeclsFromOrderFrom [] order

def ContractDecl.externalFunctionSigsFromOrderFrom (types : TypeContext)
    (sigs : List FunctionSig) :
    List L00_SourceSolidity.ContractDecl -> List FunctionSig
  | [] => sigs
  | decl :: rest =>
      ContractDecl.externalFunctionSigsFromOrderFrom types
        (FunctionSigs.addExternalAllIfNewSignature sigs
          (ContractDecl.directExternalFunctionSigs types decl))
        rest

def ContractDecl.externalFunctionSigsFromOrder (types : TypeContext)
    (order : List L00_SourceSolidity.ContractDecl) : List FunctionSig :=
  ContractDecl.externalFunctionSigsFromOrderFrom types [] order

def ContractDecl.nonPrivateFunctionSigsFromOrderFrom
    (sigs : List FunctionSig) :
    List L00_SourceSolidity.ContractDecl -> List FunctionSig
  | [] => sigs
  | decl :: rest =>
      ContractDecl.nonPrivateFunctionSigsFromOrderFrom
        (FunctionSigs.addNonPrivateAllIfNewSignature sigs
          (ContractDecl.directFunctionSigs decl))
        rest

def ContractDecl.nonPrivateFunctionSigsFromOrder
    (order : List L00_SourceSolidity.ContractDecl) : List FunctionSig :=
  ContractDecl.nonPrivateFunctionSigsFromOrderFrom [] order

def TypeContext.lookupContractExternalFunctionSigs?
    (types : TypeContext) (path : Path) : Option (List FunctionSig) := do
  let decl ← types.lookupContractDecl? path
  let order ←
    L00_SourceSolidity.Executable.ContractDecl.dispatchOrder?
      (types.contractDecls.map Prod.snd) decl
  some (ContractDecl.externalFunctionSigsFromOrder types order)

def TypeContext.resolveContractMemberFunction
    (types : TypeContext) (path : Path) (member : Name)
    (args : List ArgInfo) : Except TypeError FunctionSig :=
  match types.lookupContractExternalFunctionSigs? path with
  | some sigs => FunctionSigs.resolve sigs member args
  | none => Except.error (TypeError.unknownFunction member)

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

def Expr.directIdentName? : L00_SourceSolidity.Expr -> Option Name
  | L00_SourceSolidity.Expr.ident name => some name
  | _ => none

structure CheckedExpr where
  source : L00_SourceSolidity.Expr
  ty : Ty
  lvalue : Bool := false
  stateLValue : Bool := false
  dataLocation? : Option L00_SourceSolidity.DataLocation := none
  arraySlice : Bool := false
  deriving Repr

def CheckedExpr.locationIsCalldata (expr : CheckedExpr) : Bool :=
  expr.dataLocation? == some L00_SourceSolidity.DataLocation.calldata

def CheckedExpr.expectWritableLocation (expr : CheckedExpr)
    (target : L00_SourceSolidity.Expr) : Except TypeError Unit :=
  require
    (!(expr.locationIsCalldata && (Expr.directIdentName? target).isNone))
    (TypeError.invalidDataLocation expr.ty
      (some L00_SourceSolidity.DataLocation.calldata))

def CheckedExpr.expectStorageMutationTarget (expr : CheckedExpr)
    (target : L00_SourceSolidity.Expr) : Except TypeError Unit := do
  require expr.lvalue (TypeError.expectedLValue target)
  require
    (expr.dataLocation? == some L00_SourceSolidity.DataLocation.storage)
    (TypeError.invalidDataLocation expr.ty expr.dataLocation?)

def CheckedExpr.expectBool (expr : CheckedExpr) : Except TypeError Unit :=
  require expr.ty.isBool (TypeError.expectedBool expr.ty)

def CheckedExpr.expectInteger (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isInteger (TypeError.expectedInteger expr.ty)

def CheckedExpr.expectNumeric (expr : CheckedExpr) :
    Except TypeError Unit :=
  require expr.ty.isNumeric (TypeError.expectedNumeric expr.ty)

def CheckedExpr.expectAssignableTo (expr : CheckedExpr) (expected : Ty) :
    Except TypeError Unit :=
  require
    (Ty.canImplicitlyConvert expr.ty expected ||
      implicitLiteralFits expected expr.source)
    (TypeError.expectedType expected expr.ty)

def CheckedExpr.expectAssignableToIn (types : TypeContext)
    (expr : CheckedExpr) (expected : Ty) :
    Except TypeError Unit :=
  require
    (TypeContext.canImplicitlyConvert types expr.ty expected ||
      implicitLiteralFits expected expr.source)
    (TypeError.expectedType expected expr.ty)

abbrev TupleAssignmentTarget :=
  Option (L00_SourceSolidity.Expr × CheckedExpr)

def checkTupleAssignmentTargetAgainstChecked (env : CheckEnv)
    (target : L00_SourceSolidity.Expr) (targetChecked rhsChecked : CheckedExpr) :
    Except TypeError Ty := do
  match Expr.directIdentName? target with
  | some name =>
      require (!env.isLocalStorageRef name || rhsChecked.stateLValue)
        (TypeError.invalidDataLocation targetChecked.ty
          (some L00_SourceSolidity.DataLocation.storage))
  | none => Except.ok ()
  rhsChecked.expectAssignableToIn env.types targetChecked.ty
  Except.ok targetChecked.ty

def checkTupleAssignmentTargetAgainstTy (env : CheckEnv)
    (rhsChecked : CheckedExpr) (target : L00_SourceSolidity.Expr)
    (targetChecked : CheckedExpr) (rhsTy : Ty) :
    Except TypeError Ty := do
  match Expr.directIdentName? target with
  | some name =>
      require (!env.isLocalStorageRef name || rhsChecked.stateLValue)
        (TypeError.invalidDataLocation targetChecked.ty
          (some L00_SourceSolidity.DataLocation.storage))
  | none => Except.ok ()
  require
    (TypeContext.canImplicitlyConvert env.types rhsTy targetChecked.ty)
    (TypeError.expectedType targetChecked.ty rhsTy)
  Except.ok targetChecked.ty

def checkTupleAssignmentTargetsWithValues (env : CheckEnv) :
    List TupleAssignmentTarget -> List CheckedExpr ->
    Except TypeError (List Ty)
  | [], [] => Except.ok []
  | none :: targetRest, _ :: valueRest =>
      checkTupleAssignmentTargetsWithValues env targetRest valueRest
  | some (target, targetChecked) :: targetRest,
      value :: valueRest => do
      let ty ←
        checkTupleAssignmentTargetAgainstChecked env target targetChecked
          value
      let tail ←
        checkTupleAssignmentTargetsWithValues env targetRest valueRest
      Except.ok (ty :: tail)
  | targets, values =>
      Except.error
        (TypeError.arityMismatch
          "tuple assignment" targets.length values.length)

def checkTupleAssignmentTargetsWithTys (env : CheckEnv)
    (rhsChecked : CheckedExpr) :
    List TupleAssignmentTarget -> List Ty -> Except TypeError (List Ty)
  | [], [] => Except.ok []
  | none :: targetRest, _ :: tyRest =>
      checkTupleAssignmentTargetsWithTys env rhsChecked targetRest tyRest
  | some (target, targetChecked) :: targetRest,
      rhsTy :: tyRest => do
      let ty ←
        checkTupleAssignmentTargetAgainstTy env rhsChecked target
          targetChecked rhsTy
      let tail ←
        checkTupleAssignmentTargetsWithTys env rhsChecked targetRest tyRest
      Except.ok (ty :: tail)
  | targets, tys =>
      Except.error
        (TypeError.arityMismatch
          "tuple assignment" targets.length tys.length)

def Arg.name? : L00_SourceSolidity.Arg -> Option Name
  | L00_SourceSolidity.Arg.positional _ => none
  | L00_SourceSolidity.Arg.named name _ => some name

namespace Args

def anyNamed : List L00_SourceSolidity.Arg -> Bool
  | [] => false
  | L00_SourceSolidity.Arg.named _ _ :: _ => true
  | L00_SourceSolidity.Arg.positional _ :: rest => anyNamed rest

def positionalExprs? : List L00_SourceSolidity.Arg ->
    Option (List L00_SourceSolidity.Expr)
  | [] => some []
  | L00_SourceSolidity.Arg.positional expr :: rest => do
      let tail ← positionalExprs? rest
      some (expr :: tail)
  | L00_SourceSolidity.Arg.named _ _ :: _ => none

end Args

def checkedArgInfos : List L00_SourceSolidity.Arg -> List CheckedExpr ->
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

def checkedArgInfosFull : List L00_SourceSolidity.Arg -> List CheckedExpr ->
    List CheckedArgInfo
  | [], [] => []
  | arg :: argRest, checked :: checkedRest =>
      (Arg.name? arg, checked) :: checkedArgInfosFull argRest checkedRest
  | _, _ => []

def Ty.commonImplicit? (left right : Ty) : Option Ty :=
  if left == right then
    some left
  else
    match left, right with
    | L00_SourceSolidity.Ty.address _,
      L00_SourceSolidity.Ty.address _ =>
        some (L00_SourceSolidity.Ty.address false)
    | L00_SourceSolidity.Ty.uint leftBits,
      L00_SourceSolidity.Ty.uint rightBits =>
        some (L00_SourceSolidity.Ty.uint (max leftBits rightBits))
    | L00_SourceSolidity.Ty.int leftBits,
      L00_SourceSolidity.Ty.int rightBits =>
        some (L00_SourceSolidity.Ty.int (max leftBits rightBits))
    | L00_SourceSolidity.Ty.bytesN leftSize,
      L00_SourceSolidity.Ty.bytesN rightSize =>
        some (L00_SourceSolidity.Ty.bytesN (max leftSize rightSize))
    | L00_SourceSolidity.Ty.fixedBytes leftSize,
      L00_SourceSolidity.Ty.fixedBytes rightSize =>
        some (L00_SourceSolidity.Ty.fixedBytes (max leftSize rightSize))
    | L00_SourceSolidity.Ty.bytesN leftSize,
      L00_SourceSolidity.Ty.fixedBytes rightSize =>
        some (L00_SourceSolidity.Ty.fixedBytes (max leftSize rightSize))
    | L00_SourceSolidity.Ty.fixedBytes leftSize,
      L00_SourceSolidity.Ty.bytesN rightSize =>
        some (L00_SourceSolidity.Ty.fixedBytes (max leftSize rightSize))
    | _, _ =>
        if Ty.canImplicitlyConvert left right then
          some right
        else if Ty.canImplicitlyConvert right left then
          some left
        else
          none

def Expr.isDirectLiteral : L00_SourceSolidity.Expr -> Bool
  | L00_SourceSolidity.Expr.literal _ => true
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
  left.expectAssignableTo ty
  right.expectAssignableTo ty

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

def CheckedExprs.relationalTy (left right : CheckedExpr) :
    Except TypeError Ty :=
  CheckedExprs.commonCheckedTyFor "relational expression"
    Ty.isRelationalOperand TypeError.expectedNumeric left right

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

def checkedExprParamsAccept (types : TypeContext) :
    List CheckedExpr -> List Ty -> Bool
  | [], [] => true
  | actual :: actualRest, expected :: expectedRest =>
      (TypeContext.canImplicitlyConvert types actual.ty expected ||
        implicitLiteralFits expected actual.source) &&
        checkedExprParamsAccept types actualRest expectedRest
  | _, _ => false

def checkedExprParamsAcceptStorageRefs (types : TypeContext) :
    List CheckedExpr -> List Ty -> List Bool -> Bool
  | [], [], [] => true
  | actual :: actualRest, expected :: expectedRest,
      needsStorage :: storageRest =>
      (TypeContext.canImplicitlyConvert types actual.ty expected ||
        implicitLiteralFits expected actual.source) &&
        (!needsStorage || actual.stateLValue) &&
        checkedExprParamsAcceptStorageRefs types actualRest expectedRest
          storageRest
  | actual, expected, [] => checkedExprParamsAccept types actual expected
  | _, _, _ => false

def FunctionSig.matchesCheckedArgs
    (types : TypeContext) (sig : FunctionSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered =>
      checkedExprParamsAcceptStorageRefs types ordered sig.params
        sig.paramStorageRefs
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
        | some _ => Except.error (TypeError.ambiguousFunction target)
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

def ModifierSig.matchesCheckedArgs
    (types : TypeContext) (sig : ModifierSig)
    (args : List CheckedArgInfo) : Bool :=
  match CheckedArgInfos.ordered? sig.paramNames args with
  | some ordered =>
      checkedExprParamsAcceptStorageRefs types ordered sig.params
        sig.paramStorageRefs
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
    match sig.params, sig.paramNames, sig.paramStorageRefs with
    | selfTy :: params, _ :: paramNames,
        selfNeedsStorage :: paramStorageRefs =>
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
    | selfTy :: params, _ :: paramNames, [] =>
        if TypeContext.canImplicitlyConvert types receiver.ty selfTy ||
            implicitLiteralFits selfTy receiver.source then
          some { sig with params := params, paramNames := paramNames }
        else
          none
    | _, _, _ => none
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
    (binding : L00_SourceSolidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some _ => Except.ok []
  | none =>
      let (libraryPath, functionName) ←
        match L00_SourceSolidity.Executable.pathInitLast? binding.function with
        | some parts => Except.ok parts
        | none => Except.error (TypeError.unknownFunction member)
      if functionName == member then
        if libraryPath.segments.isEmpty then
          Except.ok
            (FunctionSigs.usingMemberCandidates env.types receiver member
              ((FunctionSigs.nonPrivate env.functions).filter
                (fun sig => sig.name == functionName)))
        else
          let libraryDecl ←
            match env.types.lookupContractDecl? libraryPath with
            | some libraryDecl => Except.ok libraryDecl
            | none => Except.error (TypeError.unknownType libraryPath)
          require (libraryDecl.kind == L00_SourceSolidity.ContractKind.library)
            (TypeError.invalidContractHeader "using target is not a library")
          Except.ok
            (FunctionSigs.usingMemberCandidates env.types receiver member
              ((FunctionSigs.nonPrivate
                (ContractDecl.directFunctionSigs libraryDecl)).filter
                  (fun sig => sig.name == functionName)))
      else
        Except.ok []

def UsingFunctions.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name) :
    List L00_SourceSolidity.UsingFunction ->
    Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | binding :: rest => do
      let head ← UsingFunction.memberCandidates env receiver member binding
      let tail ← UsingFunctions.memberCandidates env receiver member rest
      Except.ok (head ++ tail)

def UsingDecl.appliesToReceiver
    (decl : L00_SourceSolidity.UsingDecl) (receiverTy : Ty) : Bool :=
  match decl.target with
  | some targetTy => receiverTy == targetTy
  | none => true

def UsingDecl.appliesToBinaryOperands
    (decl : L00_SourceSolidity.UsingDecl) (lhsTy rhsTy : Ty) : Bool :=
  match decl.target with
  | some targetTy => lhsTy == targetTy || rhsTy == targetTy
  | none => true

def BinaryOp.userDefinedOperatorResultTy? (targetTy : Ty) :
    L00_SourceSolidity.BinaryOp -> Option Ty
  | L00_SourceSolidity.BinaryOp.add
  | L00_SourceSolidity.BinaryOp.sub
  | L00_SourceSolidity.BinaryOp.mul
  | L00_SourceSolidity.BinaryOp.div
  | L00_SourceSolidity.BinaryOp.mod
  | L00_SourceSolidity.BinaryOp.bitAnd
  | L00_SourceSolidity.BinaryOp.bitOr
  | L00_SourceSolidity.BinaryOp.bitXor => some targetTy
  | L00_SourceSolidity.BinaryOp.lt
  | L00_SourceSolidity.BinaryOp.gt
  | L00_SourceSolidity.BinaryOp.le
  | L00_SourceSolidity.BinaryOp.ge
  | L00_SourceSolidity.BinaryOp.eq
  | L00_SourceSolidity.BinaryOp.ne => some L00_SourceSolidity.Ty.bool
  | _ => none

def UnaryOp.userDefinedOperatorResultTy? (targetTy : Ty) :
    L00_SourceSolidity.UnaryOp -> Option Ty
  | L00_SourceSolidity.UnaryOp.bitNot
  | L00_SourceSolidity.UnaryOp.neg => some targetTy
  | _ => none

def UsingOperator.userDefinedResultTy? (targetTy : Ty) :
    L00_SourceSolidity.UsingOperator -> Option Ty
  | L00_SourceSolidity.UsingOperator.binary op =>
      BinaryOp.userDefinedOperatorResultTy? targetTy op
  | L00_SourceSolidity.UsingOperator.unary op =>
      UnaryOp.userDefinedOperatorResultTy? targetTy op

def FunctionSig.hasParamTy (targetTy : Ty) : List Ty -> Bool
  | [] => false
  | ty :: rest => ty == targetTy || FunctionSig.hasParamTy targetTy rest

def FunctionSig.matchesUserDefinedBinaryOperator
    (types : TypeContext) (targetTy : Ty)
    (op : L00_SourceSolidity.BinaryOp) (lhs rhs : CheckedExpr)
    (sig : FunctionSig) : Bool :=
  match BinaryOp.userDefinedOperatorResultTy? targetTy op with
  | some resultTy =>
      sig.mutability == L00_SourceSolidity.StateMutability.pure &&
        sig.returns == [resultTy] &&
        FunctionSig.hasParamTy targetTy sig.params &&
        sig.matchesCheckedArgs types [(none, lhs), (none, rhs)]
  | none => false

def FunctionSig.matchesUserDefinedUnaryOperator
    (types : TypeContext) (targetTy : Ty)
    (op : L00_SourceSolidity.UnaryOp) (operand : CheckedExpr)
    (sig : FunctionSig) : Bool :=
  match UnaryOp.userDefinedOperatorResultTy? targetTy op with
  | some resultTy =>
      sig.mutability == L00_SourceSolidity.StateMutability.pure &&
        sig.returns == [resultTy] &&
        FunctionSig.hasParamTy targetTy sig.params &&
        sig.matchesCheckedArgs types [(none, operand)]
  | none => false

def FunctionSig.matchesUserDefinedOperatorDecl (targetTy : Ty)
    (operator : L00_SourceSolidity.UsingOperator)
    (sig : FunctionSig) : Bool :=
  match operator with
  | L00_SourceSolidity.UsingOperator.binary op =>
      match BinaryOp.userDefinedOperatorResultTy? targetTy op with
      | some resultTy =>
          sig.mutability == L00_SourceSolidity.StateMutability.pure &&
            sig.params.length == 2 &&
            FunctionSig.hasParamTy targetTy sig.params &&
            sig.returns == [resultTy]
      | none => false
  | L00_SourceSolidity.UsingOperator.unary op =>
      match UnaryOp.userDefinedOperatorResultTy? targetTy op with
      | some resultTy =>
          sig.mutability == L00_SourceSolidity.StateMutability.pure &&
            sig.params.length == 1 &&
            FunctionSig.hasParamTy targetTy sig.params &&
            sig.returns == [resultTy]
      | none => false

def UsingFunction.binaryOperatorCandidates (env : CheckEnv)
    (targetTy : Ty) (op : L00_SourceSolidity.BinaryOp)
    (lhs rhs : CheckedExpr)
    (binding : L00_SourceSolidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some (L00_SourceSolidity.UsingOperator.binary bindingOp) =>
      if bindingOp == op then
        let (libraryPath, functionName) ←
          match L00_SourceSolidity.Executable.pathInitLast? binding.function with
          | some parts => Except.ok parts
          | none => Except.error (TypeError.unknownFunction "operator")
        if libraryPath.segments.isEmpty then
          Except.ok
            ((FunctionSigs.nonPrivate env.functions).filter
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
    (targetTy : Ty) (op : L00_SourceSolidity.BinaryOp)
    (lhs rhs : CheckedExpr) :
    List L00_SourceSolidity.UsingFunction ->
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
    (targetTy : Ty) (op : L00_SourceSolidity.UnaryOp)
    (operand : CheckedExpr)
    (binding : L00_SourceSolidity.UsingFunction) :
    Except TypeError (List FunctionSig) := do
  match binding.operator? with
  | some (L00_SourceSolidity.UsingOperator.unary bindingOp) =>
      if bindingOp == op then
        let (libraryPath, functionName) ←
          match L00_SourceSolidity.Executable.pathInitLast? binding.function with
          | some parts => Except.ok parts
          | none => Except.error (TypeError.unknownFunction "operator")
        if libraryPath.segments.isEmpty then
          Except.ok
            ((FunctionSigs.nonPrivate env.functions).filter
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
    (targetTy : Ty) (op : L00_SourceSolidity.UnaryOp)
    (operand : CheckedExpr) :
    List L00_SourceSolidity.UsingFunction ->
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
    (op : L00_SourceSolidity.BinaryOp) (lhs rhs : CheckedExpr)
    (decl : L00_SourceSolidity.UsingDecl) :
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
    (op : L00_SourceSolidity.UnaryOp) (operand : CheckedExpr)
    (decl : L00_SourceSolidity.UsingDecl) :
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
    (op : L00_SourceSolidity.BinaryOp) (lhs rhs : CheckedExpr) :
    List L00_SourceSolidity.UsingDecl -> Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | decl :: rest => do
      let head ← UsingDecl.binaryOperatorCandidates env op lhs rhs decl
      let tail ←
        UsingDecls.binaryOperatorCandidates env op lhs rhs rest
      Except.ok (head ++ tail)

def UsingDecls.unaryOperatorCandidates (env : CheckEnv)
    (op : L00_SourceSolidity.UnaryOp) (operand : CheckedExpr) :
    List L00_SourceSolidity.UsingDecl -> Except TypeError (List FunctionSig)
  | [] => Except.ok []
  | decl :: rest => do
      let head ← UsingDecl.unaryOperatorCandidates env op operand decl
      let tail ←
        UsingDecls.unaryOperatorCandidates env op operand rest
      Except.ok (head ++ tail)

def UsingDecl.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name)
    (decl : L00_SourceSolidity.UsingDecl) :
    Except TypeError (List FunctionSig) := do
  if UsingDecl.appliesToReceiver decl receiver.ty then
    if decl.functions.isEmpty then
      let libraryDecl ←
        match env.types.lookupContractDecl? decl.library with
        | some libraryDecl => Except.ok libraryDecl
        | none => Except.error (TypeError.unknownType decl.library)
      require (libraryDecl.kind == L00_SourceSolidity.ContractKind.library)
        (TypeError.invalidContractHeader "using target is not a library")
      Except.ok
        (FunctionSigs.usingMemberCandidates env.types receiver member
          (FunctionSigs.nonPrivate
            (ContractDecl.directFunctionSigs libraryDecl)))
    else
      UsingFunctions.memberCandidates env receiver member decl.functions
  else
    Except.ok []

def UsingDecls.memberCandidates (env : CheckEnv)
    (receiver : CheckedExpr) (member : Name) :
    List L00_SourceSolidity.UsingDecl -> Except TypeError (List FunctionSig)
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
    (op : L00_SourceSolidity.BinaryOp) (lhs rhs : CheckedExpr) :
    Except TypeError (Option FunctionSig) := do
  let candidates ←
    UsingDecls.binaryOperatorCandidates env op lhs rhs env.usingDecls
  match candidates with
  | [] => Except.ok none
  | [sig] => Except.ok (some sig)
  | _ => Except.error (TypeError.ambiguousFunction "operator")

def CheckEnv.resolveUsingUnaryOperator? (env : CheckEnv)
    (op : L00_SourceSolidity.UnaryOp) (operand : CheckedExpr) :
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
  require (libraryDecl.kind == L00_SourceSolidity.ContractKind.library)
    (TypeError.invalidContractHeader "library call target is not a library")
  FunctionSigs.resolveChecked types
    (FunctionSigs.nonPrivate (ContractDecl.directFunctionSigs libraryDecl))
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
    (FunctionSigs.nonPrivate (ContractDecl.directFunctionSigs baseDecl))
    member args

def literalTy? : L00_SourceSolidity.Literal -> Option Ty
  | L00_SourceSolidity.Literal.unitNumber text unit => do
      let _ ← L00_SourceSolidity.Executable.parseUnitNumberNat? text unit
      some (L00_SourceSolidity.Ty.uint 256)
  | literal => L00_SourceSolidity.Executable.Literal.abiTy? literal

def CallOptions.names : List L00_SourceSolidity.CallOption -> List Name
  | [] => []
  | L00_SourceSolidity.CallOption.named name _ :: rest =>
      name :: CallOptions.names rest

def CallOptions.hasValue : List L00_SourceSolidity.CallOption -> Bool
  | [] => false
  | L00_SourceSolidity.CallOption.named name _ :: rest =>
      name == "value" || CallOptions.hasValue rest

def CallOptions.hasGas : List L00_SourceSolidity.CallOption -> Bool
  | [] => false
  | L00_SourceSolidity.CallOption.named name _ :: rest =>
      name == "gas" || CallOptions.hasGas rest

def CallOptions.nameAllowed (allowed : List Name) (name : Name) : Bool :=
  L00_SourceSolidity.Executable.nameIn name allowed

def CallOptions.allNamesAllowed (allowed : List Name) :
    List L00_SourceSolidity.CallOption -> Bool
  | [] => true
  | L00_SourceSolidity.CallOption.named name _ :: rest =>
      CallOptions.nameAllowed allowed name &&
        CallOptions.allNamesAllowed allowed rest

def requireCallOptionsAllowedNames (allowed : List Name)
    (options : List L00_SourceSolidity.CallOption) :
    Except TypeError Unit :=
  require (CallOptions.allNamesAllowed allowed options)
    (TypeError.unsupported "call option is not allowed here")

def Ty.isAddressLike (types : TypeContext) : Ty -> Bool
  | L00_SourceSolidity.Ty.address _ => true
  | L00_SourceSolidity.Ty.user path => types.isContractPath path
  | _ => false

def Ty.isPayableAddress : Ty -> Bool
  | L00_SourceSolidity.Ty.address true => true
  | _ => false

def Ty.hasLengthMember : Ty -> Bool
  | L00_SourceSolidity.Ty.bytes => true
  | L00_SourceSolidity.Ty.bytesN _ => true
  | L00_SourceSolidity.Ty.fixedBytes _ => true
  | L00_SourceSolidity.Ty.array _ _ => true
  | _ => false

def Ty.hasArrayMutationMemberSurface : Ty -> Bool
  | L00_SourceSolidity.Ty.bytes => true
  | L00_SourceSolidity.Ty.array _ _ => true
  | _ => false

def Ty.dynamicStorageArrayElement? : Ty -> Option Ty
  | L00_SourceSolidity.Ty.bytes =>
      some (L00_SourceSolidity.Ty.bytesN 1)
  | L00_SourceSolidity.Ty.array element none => some element
  | _ => none

def lowLevelCallMember (member : Name) : Bool :=
  member == "call" || member == "staticcall" ||
    member == "delegatecall" || member == "send" || member == "transfer"

def lowLevelCallReturnTy : Ty :=
  L00_SourceSolidity.Ty.tuple
    [L00_SourceSolidity.Ty.bool, L00_SourceSolidity.Ty.bytes]

def checkCallTargetExpr (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Except TypeError CheckedExpr :=
  match expr with
  | L00_SourceSolidity.Expr.ident "this" => do
      requireStateReadAllowed env
      match env.currentContract with
      | some path =>
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.user path
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unknownIdentifier "this")
  | L00_SourceSolidity.Expr.ident name =>
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          let isStorageRef := env.isLocalStorageRef name
          let isConstant := env.isConstantName name
          let isImmutable := env.isImmutableName name
          let dataLocation? :=
            if Ty.needsDataLocation env.types ty then
              if isState || isStorageRef then
                some L00_SourceSolidity.DataLocation.storage
              else
                env.lookupLocalDataLocation? name
            else
              none
          if isState || isStorageRef then
            requireStateReadAllowed env
          else
            Except.ok ()
          Except.ok
            { source := expr
              ty := ty
              lvalue := !isConstant && (!isImmutable || env.inConstructor)
              stateLValue := isState || isStorageRef
              dataLocation? := dataLocation? }
      | none => Except.error (TypeError.unknownIdentifier name)
  | _ =>
      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
      | none => Except.error (TypeError.unsupported "call target")

def requireValueOptionAllowed
    (mutability : L00_SourceSolidity.StateMutability)
    (options : List L00_SourceSolidity.CallOption) :
    Except TypeError Unit :=
  if CallOptions.hasValue options &&
      !(mutability == L00_SourceSolidity.StateMutability.payable) then
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
    Except TypeError Unit :=
  require (TypeContext.isAbiEncodable types expr.ty)
    (TypeError.invalidAbiType expr.ty)

def CheckedExpr.expectBytesLike (expr : CheckedExpr) :
    Except TypeError Unit :=
  expr.expectAssignableTo L00_SourceSolidity.Ty.bytes

def CheckedExpr.expectStringLike (expr : CheckedExpr) :
    Except TypeError Unit :=
  expr.expectAssignableTo L00_SourceSolidity.Ty.string

def checkAbiEncodableArgs (types : TypeContext) :
    List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      expr.expectAbiEncodable types
      checkAbiEncodableArgs types rest

def checkBytesConcatArgs : List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      require (L00_SourceSolidity.Executable.Ty.isBytesConcatArg expr.ty)
        (TypeError.invalidAbiType expr.ty)
      checkBytesConcatArgs rest

def checkStringConcatArgs : List CheckedExpr -> Except TypeError Unit
  | [] => Except.ok ()
  | expr :: rest => do
      require (L00_SourceSolidity.Executable.Ty.isStringConcatArg expr.ty)
        (TypeError.invalidAbiType expr.ty)
      checkStringConcatArgs rest

def checkAbiDecodeTupleItems (types : TypeContext) :
    List L00_SourceSolidity.TupleItem -> Except TypeError (List Ty)
  | [] => Except.ok []
  | L00_SourceSolidity.TupleItem.value
      (L00_SourceSolidity.Expr.typeName ty) :: rest => do
      checkTy types ty
      require (TypeContext.isAbiEncodable types ty)
        (TypeError.invalidAbiType ty)
      let tail ← checkAbiDecodeTupleItems types rest
      Except.ok (ty :: tail)
  | _ :: _ =>
      Except.error
        (TypeError.invalidAbiCall "abi.decode expects type names")

def checkAbiDecodeTypesExpr (types : TypeContext) :
    L00_SourceSolidity.Expr -> Except TypeError (List Ty)
  | L00_SourceSolidity.Expr.typeName ty => do
      checkTy types ty
      require (TypeContext.isAbiEncodable types ty)
        (TypeError.invalidAbiType ty)
      Except.ok [ty]
  | L00_SourceSolidity.Expr.tuple items =>
      checkAbiDecodeTupleItems types items
  | _ =>
      Except.error
        (TypeError.invalidAbiCall "abi.decode expects a type expression")

def checkBuiltinIdentCall (env : CheckEnv) (name : Name)
    (argInfos : List ArgInfo) (checkedArgs : List CheckedExpr) :
    Except TypeError (Option Ty) :=
  if name == "gasleft" then do
    requireNoNamedArgs "gasleft" argInfos
    require (checkedArgs.length == 0)
      (TypeError.arityMismatch "gasleft" 0 checkedArgs.length)
    Except.ok (some (L00_SourceSolidity.Ty.uint 256))
  else if name == "blockhash" || name == "blobhash" then do
    requireNoNamedArgs name argInfos
    requireCallMutabilityAllowed env L00_SourceSolidity.StateMutability.view
    match checkedArgs with
    | [number] => do
        number.expectInteger
        Except.ok (some (L00_SourceSolidity.Ty.bytesN 32))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "addmod" || name == "mulmod" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [lhs, rhs, modulus] => do
        lhs.expectInteger
        rhs.expectInteger
        modulus.expectInteger
        Except.ok (some (L00_SourceSolidity.Ty.uint 256))
    | _ => Except.error (TypeError.arityMismatch name 3 checkedArgs.length)
  else if name == "keccak256" || name == "sha256" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [payload] => do
        payload.expectBytesLike
        Except.ok (some (L00_SourceSolidity.Ty.bytesN 32))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "erc7201" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [id] => do
        id.expectStringLike
        Except.ok (some (L00_SourceSolidity.Ty.uint 256))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "ripemd160" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [payload] => do
        payload.expectBytesLike
        Except.ok (some (L00_SourceSolidity.Ty.bytesN 20))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "ecrecover" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [hash, v, r, s] => do
        hash.expectAssignableTo (L00_SourceSolidity.Ty.bytesN 32)
        v.expectAssignableTo (L00_SourceSolidity.Ty.uint 8)
        r.expectAssignableTo (L00_SourceSolidity.Ty.bytesN 32)
        s.expectAssignableTo (L00_SourceSolidity.Ty.bytesN 32)
        Except.ok (some (L00_SourceSolidity.Ty.address false))
    | _ => Except.error (TypeError.arityMismatch name 4 checkedArgs.length)
  else if name == "assert" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [cond] => do
        cond.expectBool
        Except.ok (some (L00_SourceSolidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "require" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [cond] => do
        cond.expectBool
        Except.ok (some (L00_SourceSolidity.Ty.tuple []))
    | [cond, reason] => do
        cond.expectBool
        reason.expectAbiEncodable env.types
        Except.ok (some (L00_SourceSolidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 2 checkedArgs.length)
  else if name == "revert" then do
    requireNoNamedArgs name argInfos
    match checkedArgs with
    | [] => Except.ok (some (L00_SourceSolidity.Ty.tuple []))
    | [reason] => do
        reason.expectAbiEncodable env.types
        Except.ok (some (L00_SourceSolidity.Ty.tuple []))
    | _ => Except.error (TypeError.arityMismatch name 1 checkedArgs.length)
  else if name == "selfdestruct" then do
    requireNoNamedArgs name argInfos
    requireLogOrCreateAllowed env "selfdestruct in view or pure function"
    match checkedArgs with
    | [recipient] => do
        recipient.expectAssignableToIn env.types
          (L00_SourceSolidity.Ty.address true)
        Except.ok (some (L00_SourceSolidity.Ty.tuple []))
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

def checkCheckedArgsAssignableToSignature
    (types : TypeContext) (what : String)
    (paramNames : List (Option Name)) (params : List Ty)
    (args : List L00_SourceSolidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  match CheckedArgInfos.ordered? paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered =>
      checkCheckedExprsAssignableToFor types what ordered params
  | none =>
      Except.error
        (TypeError.arityMismatch what params.length checkedArgs.length)

def checkCheckedArgsAssignableToFunctionSig
    (types : TypeContext) (what : String) (sig : FunctionSig)
    (args : List L00_SourceSolidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  match CheckedArgInfos.ordered? sig.paramNames
      (checkedArgInfosFull args checkedArgs) with
  | some ordered => do
      checkCheckedExprsAssignableToFor types what ordered sig.params
      checkCheckedExprsStorageRefsFor what ordered sig.paramStorageRefs
  | none =>
      Except.error
        (TypeError.arityMismatch what sig.params.length checkedArgs.length)

def checkArrayMutationCall? (env : CheckEnv)
    (expr target : L00_SourceSolidity.Expr) (member : Name)
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
                        some L00_SourceSolidity.DataLocation.storage })
            | [value] => do
                value.expectAssignableToIn env.types element
                Except.ok
                  (some
                    { source := expr
                      ty := L00_SourceSolidity.Ty.tuple []
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
                      ty := L00_SourceSolidity.Ty.tuple []
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

def StructDecl.fieldNames (decl : L00_SourceSolidity.StructDecl) :
    List (Option Name) :=
  decl.fields.map (fun field => some field.name)

def StructDecl.fieldTys (decl : L00_SourceSolidity.StructDecl) :
    List Ty :=
  decl.fields.map L00_SourceSolidity.StructField.ty

def checkStructConstructorArgs
    (types : TypeContext) (decl : L00_SourceSolidity.StructDecl)
    (args : List L00_SourceSolidity.Arg)
    (checkedArgs : List CheckedExpr) : Except TypeError Unit := do
  let ordered? :=
    CheckedArgInfos.ordered? (StructDecl.fieldNames decl)
      (checkedArgInfosFull args checkedArgs)
  match ordered? with
  | some ordered =>
      checkCheckedExprsAssignableToFor
        types ("struct constructor " ++ decl.name) ordered
        (StructDecl.fieldTys decl)
  | none => Except.error (TypeError.invalidStructConstructor decl.name)

def functionPointerSig? (name : Name) : Ty -> Option FunctionSig
  | L00_SourceSolidity.Ty.function params returns mutability visibility =>
      some
        { name := name
          params := params
          paramNames := List.replicate params.length none
          paramStorageRefs := List.replicate params.length false
          returns := returns
          visibility := some visibility
          mutability := mutability }
  | _ => none

def requireExternalEncodeCallPointer
    (sig : FunctionSig) : Except TypeError FunctionSig := do
  require (sig.visibility == some L00_SourceSolidity.Visibility.external_)
    (TypeError.invalidAbiCall
      "abi.encodeCall expects an external function pointer")
  Except.ok sig

def resolveEncodeCallFunction (env : CheckEnv)
    (pointer : L00_SourceSolidity.Expr)
    (argInfos : List CheckedArgInfo) :
    Except TypeError FunctionSig :=
  match pointer with
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName (L00_SourceSolidity.Ty.user path))
      member => do
      let sig ←
        env.types.resolveContractMemberFunctionChecked path member argInfos
      require sig.externallyCallable
        (TypeError.invalidAbiCall
          "abi.encodeCall expects an external function")
      Except.ok sig
  | L00_SourceSolidity.Expr.member target member => do
      let targetChecked ← checkCallTargetExpr env target
      match targetChecked.ty with
      | L00_SourceSolidity.Ty.user path => do
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
              (L00_SourceSolidity.Ty.address false) other)
  | L00_SourceSolidity.Expr.ident name => do
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          let isStorageRef := env.isLocalStorageRef name
          if isState || isStorageRef then
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

def FunctionDecl.canReceiveEther
    (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  (fn.kind == L00_SourceSolidity.FunctionKind.receive &&
      fn.mutability == L00_SourceSolidity.StateMutability.payable) ||
    (fn.kind == L00_SourceSolidity.FunctionKind.fallback &&
      fn.mutability == L00_SourceSolidity.StateMutability.payable)

def ContractItems.canReceiveEther :
    List L00_SourceSolidity.ContractItem -> Bool
  | [] => false
  | L00_SourceSolidity.ContractItem.function fn :: rest =>
      FunctionDecl.canReceiveEther fn || ContractItems.canReceiveEther rest
  | _ :: rest => ContractItems.canReceiveEther rest

def TypeContext.contractCanReceiveEther (types : TypeContext)
    (path : Path) : Bool :=
  match types.lookupContractDecl? path with
  | some decl => ContractItems.canReceiveEther decl.items
  | none => false

def requireCreatableContractDecl
    (decl : L00_SourceSolidity.ContractDecl) : Except TypeError Unit := do
  require (decl.kind == L00_SourceSolidity.ContractKind.contract)
    (TypeError.invalidContractHeader
      "contract creation target is not a contract")
  require (!decl.abstract)
    (TypeError.invalidContractHeader
      "contract creation target is abstract")

def checkInternalFunctionValueAssignable?
    (env : CheckEnv) (expr : L00_SourceSolidity.Expr) (expected : Ty) :
    Option (Except TypeError Unit) :=
  match expr, expected with
  | L00_SourceSolidity.Expr.ident name,
    L00_SourceSolidity.Ty.function _ _ _ L00_SourceSolidity.Visibility.internal_ =>
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

def exprContextuallyAssignableTo
    (env : CheckEnv) (expr : L00_SourceSolidity.Expr) (expected : Ty) :
    Bool :=
  match checkInternalFunctionValueAssignable? env expr expected with
  | some (Except.ok _) => true
  | _ =>
      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some actual =>
          TypeContext.canImplicitlyConvert env.types actual expected ||
            implicitLiteralFits expected expr
      | none => false

def exprContextuallyStorageOk
    (env : CheckEnv) (expr : L00_SourceSolidity.Expr)
    (needsStorage : Bool) : Bool :=
  if needsStorage then
    match expr with
    | L00_SourceSolidity.Expr.ident name =>
        (env.isStateName name && !env.isLocalName name) ||
          env.isLocalStorageRef name
    | _ => false
  else
    true

def exprsContextuallyMatchParamTys (env : CheckEnv) :
    List L00_SourceSolidity.Expr -> List Ty -> Bool
  | [], [] => true
  | expr :: exprRest, ty :: tyRest =>
      exprContextuallyAssignableTo env expr ty &&
        exprsContextuallyMatchParamTys env exprRest tyRest
  | _, _ => false

def exprsContextuallyMatchParams (env : CheckEnv) :
    List L00_SourceSolidity.Expr -> List Ty -> List Bool -> Bool
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
    (args : List L00_SourceSolidity.Arg) : Bool :=
  match Args.positionalExprs? args with
  | some exprs =>
      exprsContextuallyMatchParams env exprs sig.params
        sig.paramStorageRefs
  | none => false

namespace FunctionSigs

def resolveContextualLoop (env : CheckEnv)
    (target : Name) (args : List L00_SourceSolidity.Arg) :
    Option FunctionSig -> List FunctionSig -> Except TypeError FunctionSig
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
    (functions : List FunctionSig) (target : Name)
    (args : List L00_SourceSolidity.Arg) : Except TypeError FunctionSig :=
  resolveContextualLoop env target args none functions

end FunctionSigs

mutual

def checkExpr (env : CheckEnv) :
    L00_SourceSolidity.Expr -> Except TypeError CheckedExpr
  | expr@(L00_SourceSolidity.Expr.literal literal) =>
      match literalTy? literal with
      | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
      | none => Except.error (TypeError.unsupported "literal")
  | expr@(L00_SourceSolidity.Expr.ident "this") => do
      requireStateReadAllowed env
      match env.currentContract with
      | some path =>
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.user path
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unknownIdentifier "this")
  | expr@(L00_SourceSolidity.Expr.ident name) =>
      match env.lookupVar? name with
      | some ty => do
          let isState := env.isStateName name && !env.isLocalName name
          let isStorageRef := env.isLocalStorageRef name
          let isConstant := env.isConstantName name
          let isImmutable := env.isImmutableName name
          let dataLocation? :=
            if Ty.needsDataLocation env.types ty then
              if isState || isStorageRef then
                some L00_SourceSolidity.DataLocation.storage
              else
                env.lookupLocalDataLocation? name
            else
              none
          if isState || isStorageRef then
            requireStateReadAllowed env
          else
            Except.ok ()
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
  | expr@(L00_SourceSolidity.Expr.typeName ty) => do
      checkTy env.types ty
      Except.ok { source := expr, ty := ty, lvalue := false }
  | expr@(L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "msg") member) => do
      if member == "data" || member == "sig" then
        Except.ok ()
      else
        requireStateReadAllowed env
      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "block") member) => do
      requireStateReadAllowed env
      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "tx") member) => do
      requireStateReadAllowed env
      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
      | some ty =>
          Except.ok
            { source := expr
              ty := ty
              lvalue := false
              stateLValue := false }
      | none => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName ty) member) => do
      checkTy env.types ty
      match ty with
      | L00_SourceSolidity.Ty.uint _
      | L00_SourceSolidity.Ty.int _ =>
          if member == "min" || member == "max" then
            Except.ok
              { source := expr
                ty := ty
                lvalue := false
                stateLValue := false }
          else
            Except.error (TypeError.unsupported ("member " ++ member))
      | L00_SourceSolidity.Ty.user path =>
          match env.types.lookupEnum? path with
          | some enumDecl =>
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
                        ty := L00_SourceSolidity.Ty.string
                        lvalue := false
                        stateLValue := false }
                  else if member == "creationCode" ||
                      member == "runtimeCode" then
                    require (!env.isCurrentOrAncestorContract path)
                      (TypeError.unsupported ("member " ++ member))
                    Except.ok
                      { source := expr
                        ty := L00_SourceSolidity.Ty.bytes
                        lvalue := false
                        stateLValue := false }
                  else if member == "interfaceId" then
                    require
                      (contractDecl.kind ==
                        L00_SourceSolidity.ContractKind.interface)
                      (TypeError.unsupported ("member " ++ member))
                    Except.ok
                      { source := expr
                        ty := L00_SourceSolidity.Ty.bytesN 4
                        lvalue := false
                        stateLValue := false }
                  else
                    Except.error
                      (TypeError.unsupported ("member " ++ member))
              | none =>
                  Except.error (TypeError.unsupported ("member " ++ member))
      | _ => Except.error (TypeError.unsupported ("member " ++ member))
  | expr@(L00_SourceSolidity.Expr.member base member) => do
      let baseChecked ← checkExpr env base
      require (!baseChecked.arraySlice)
        (TypeError.unsupported "member on array slice")
      let checkNonStructMember : Except TypeError CheckedExpr := do
        if member == "balance" then
          requireStateReadAllowed env
          require (baseChecked.ty.isAddressLike env.types)
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.uint 256
              lvalue := false
              stateLValue := false }
        else if member == "code" then
          requireStateReadAllowed env
          require (baseChecked.ty.isAddressLike env.types)
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.bytes
              lvalue := false
              stateLValue := false }
        else if member == "codehash" then
          requireStateReadAllowed env
          require (baseChecked.ty.isAddressLike env.types)
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address false) baseChecked.ty)
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.bytesN 32
              lvalue := false
              stateLValue := false }
        else if member == "length" then
          require baseChecked.ty.hasLengthMember
            (TypeError.unsupported "length member for non-array value")
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.uint 256
              lvalue := false
              stateLValue := false }
        else
          match L00_SourceSolidity.Executable.Expr.abiTyWithEnv?
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
      | L00_SourceSolidity.Ty.user path =>
          match env.types.lookupStruct? path with
          | some structDecl =>
              match structDecl.fields.find?
                  (fun field => field.name == member) with
              | some field =>
                  Except.ok
                    { source := expr
                      ty := field.ty
                      lvalue := baseChecked.lvalue
                      stateLValue := baseChecked.stateLValue
                      dataLocation? := baseChecked.dataLocation? }
              | none =>
                  Except.error (TypeError.unsupported ("member " ++ member))
          | none => checkNonStructMember
      | _ => checkNonStructMember
  | expr@(L00_SourceSolidity.Expr.index base index) => do
      let baseChecked ← checkExpr env base
      let indexChecked ← checkExpr env index
      match baseChecked.ty with
      | L00_SourceSolidity.Ty.bytes =>
          indexChecked.expectInteger
          Except.ok
            { source := expr, ty := L00_SourceSolidity.Ty.bytesN 1,
              lvalue := baseChecked.lvalue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | L00_SourceSolidity.Ty.bytesN _ =>
          indexChecked.expectInteger
          Except.ok
            { source := expr, ty := L00_SourceSolidity.Ty.bytesN 1,
              lvalue := false }
      | L00_SourceSolidity.Ty.array element _ =>
          indexChecked.expectInteger
          Except.ok
            { source := expr
              ty := element
              lvalue := baseChecked.lvalue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | L00_SourceSolidity.Ty.mapping key value => do
          indexChecked.expectAssignableToIn env.types key
          Except.ok
            { source := expr
              ty := value
              lvalue := baseChecked.lvalue
              stateLValue := baseChecked.stateLValue
              dataLocation? := baseChecked.dataLocation? }
      | other => Except.error (TypeError.expectedType
          (L00_SourceSolidity.Ty.array other none) other)
  | expr@(L00_SourceSolidity.Expr.slice base start? stop?) => do
      let baseChecked ← checkExpr env base
      let sliceTy ←
        match baseChecked.ty with
        | L00_SourceSolidity.Ty.bytes => Except.ok baseChecked.ty
        | L00_SourceSolidity.Ty.array element _ =>
            Except.ok (L00_SourceSolidity.Ty.array element none)
        | other =>
            Except.error
              (TypeError.expectedType
                (L00_SourceSolidity.Ty.array other none) other)
      require
        (baseChecked.dataLocation? ==
          some L00_SourceSolidity.DataLocation.calldata)
        (TypeError.invalidDataLocation baseChecked.ty
          baseChecked.dataLocation?)
      match start? with
      | some start =>
          let startChecked ← checkExpr env start
          startChecked.expectAssignableToIn env.types
            (L00_SourceSolidity.Ty.uint 256)
      | none => Except.ok ()
      match stop? with
      | some stop =>
          let stopChecked ← checkExpr env stop
          stopChecked.expectAssignableToIn env.types
            (L00_SourceSolidity.Ty.uint 256)
      | none => Except.ok ()
      Except.ok
        { source := expr
          ty := sliceTy
          lvalue := false
          dataLocation? := some L00_SourceSolidity.DataLocation.calldata
          arraySlice := true }
  | expr@(L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.typeName targetTy) args) => do
      checkTy env.types targetTy
      let checkTypeConversion : Except TypeError CheckedExpr := do
        let checkedArgs ← checkArgs env args
        let argInfos := checkedArgInfos args checkedArgs
        requireNoNamedArgs "type conversion" argInfos
        require (checkedArgs.length == 1)
          (TypeError.arityMismatch "type conversion" 1 checkedArgs.length)
        match checkedArgs with
        | [arg] =>
            require
              (Ty.canExplicitlyConvert env.types arg.source arg.ty targetTy)
              (TypeError.invalidConversion arg.ty targetTy)
        | _ => Except.ok ()
        Except.ok { source := expr, ty := targetTy, lvalue := false }
      match targetTy with
      | L00_SourceSolidity.Ty.user path =>
          match env.types.lookupStruct? path with
          | some structDecl => do
              let checkedArgs ← checkArgs env args
              checkStructConstructorArgs env.types structDecl args checkedArgs
              Except.ok { source := expr, ty := targetTy, lvalue := false }
          | none => checkTypeConversion
      | _ => checkTypeConversion
  | expr@(L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.ident name) args) => do
      match checkArgs env args with
      | Except.ok checkedArgs =>
          let argInfos := checkedArgInfos args checkedArgs
          let checkedInfos := checkedArgInfosFull args checkedArgs
          match env.lookupVar? name with
          | some (L00_SourceSolidity.Ty.function params returns mutability _) => do
              require (!ArgInfos.anyNamed argInfos)
                (TypeError.unsupported
                  "named arguments for function-typed expression")
              checkCheckedExprsAssignableToFor env.types "function call"
                checkedArgs params
              requireCallMutabilityAllowed env mutability
              Except.ok
                { source := expr, ty := resultTyFromReturns returns,
                  lvalue := false }
          | _ =>
              match FunctionSigs.resolveChecked env.types env.functions name
                  checkedInfos with
              | Except.ok sig => do
                  require sig.internallyCallable
                    (TypeError.invalidFunctionHeader
                      "external function requires external call syntax")
                  requireCallMutabilityAllowed env sig.mutability
                  Except.ok
                    { source := expr, ty := resultTyFromReturns sig.returns,
                      lvalue := false }
              | Except.error _ =>
                  match checkBuiltinIdentCall env name argInfos checkedArgs with
                  | Except.ok (some ty) =>
                      Except.ok { source := expr, ty := ty, lvalue := false }
                  | Except.ok none =>
                      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv?
                          env.vars expr with
                      | some ty => do
                          requireBuiltinIdentCallAllowed env name
                          Except.ok { source := expr, ty := ty, lvalue := false }
                      | none => Except.error (TypeError.unknownFunction name)
                  | Except.error err => Except.error err
      | Except.error argErr =>
          if Args.anyNamed args then
            Except.error argErr
          else
            match env.lookupVar? name with
            | some (L00_SourceSolidity.Ty.function params returns mutability _) =>
                match
                    checkPositionalArgsAssignableToParamsFor
                      env "function call" args params with
                | Except.ok _ => do
                    requireCallMutabilityAllowed env mutability
                    Except.ok
                      { source := expr
                        ty := resultTyFromReturns returns
                        lvalue := false }
                | Except.error _ => Except.error argErr
            | _ =>
                match
                    FunctionSigs.resolveContextual
                      env env.functions name args with
                | Except.ok sig => do
                    let checkedArgs ←
                      checkPositionalArgsAssignableToParamsFor
                        env "function call" args sig.params
                    checkCheckedExprsStorageRefsFor "function call"
                      checkedArgs sig.paramStorageRefs
                    require sig.internallyCallable
                      (TypeError.invalidFunctionHeader
                        "external function requires external call syntax")
                    requireCallMutabilityAllowed env sig.mutability
                    Except.ok
                      { source := expr
                        ty := resultTyFromReturns sig.returns
                        lvalue := false }
                | Except.error _ => Except.error argErr
  | expr@(L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.member
        (L00_SourceSolidity.Expr.ident "abi") "encodeCall") args) => do
      match args with
      | [ L00_SourceSolidity.Arg.positional functionPointer
        , L00_SourceSolidity.Arg.positional
            (L00_SourceSolidity.Expr.tuple items) ] => do
          let checkedItems ← checkEncodeCallTupleItems env items
          let argInfos := checkedExprsAsPositionalCheckedArgInfos checkedItems
          let sig ← resolveEncodeCallFunction env functionPointer argInfos
          checkCheckedExprsAssignableTo env.types checkedItems sig.params
          Except.ok
            { source := expr
              ty := L00_SourceSolidity.Ty.bytes
              lvalue := false }
      | _ =>
          Except.error
            (TypeError.invalidAbiCall
              "abi.encodeCall expects function pointer and tuple arguments")
  | expr@(L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.member
        (L00_SourceSolidity.Expr.typeName targetTy) member) args) => do
      checkTy env.types targetTy
      match targetTy with
      | L00_SourceSolidity.Ty.user path =>
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
              Except.error (TypeError.unsupported ("member call " ++ member))
      | _ =>
          Except.error (TypeError.unsupported ("member call " ++ member))
  | L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.member target member) args => do
      let expr :=
        L00_SourceSolidity.Expr.call
          (L00_SourceSolidity.Expr.member target member) args
      let checkedArgs ←
        match checkArgs env args with
        | Except.ok checkedArgs => Except.ok checkedArgs
        | Except.error argErr =>
            match checkMemberCallArgsContextual env target member args with
            | Except.ok checkedArgs => Except.ok checkedArgs
            | Except.error _ => Except.error argErr
      let argInfos := checkedArgInfos args checkedArgs
      let checkedInfos := checkedArgInfosFull args checkedArgs
      if lowLevelCallMember member then
        let targetChecked ← checkExpr env target
        require (!ArgInfos.anyNamed argInfos)
          (TypeError.unsupported "named arguments for low-level call")
        require (targetChecked.ty.isAddressLike env.types)
          (TypeError.expectedType
            (L00_SourceSolidity.Ty.address false) targetChecked.ty)
        if member == "staticcall" then
          requireCallMutabilityAllowed env
            L00_SourceSolidity.StateMutability.view
        else
          requireCallMutabilityAllowed env
            L00_SourceSolidity.StateMutability.nonpayable
        if member == "call" || member == "staticcall" ||
            member == "delegatecall" then
          match checkedArgs with
          | [data] => do
              data.expectAssignableTo L00_SourceSolidity.Ty.bytes
              Except.ok { source := expr, ty := lowLevelCallReturnTy }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  ("low-level " ++ member) 1 checkedArgs.length)
        else if member == "send" then
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectInteger
              Except.ok
                { source := expr, ty := L00_SourceSolidity.Ty.bool }
          | _ =>
              Except.error
                (TypeError.arityMismatch "send" 1 checkedArgs.length)
        else
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectInteger
              Except.ok
                { source := expr
                  ty := L00_SourceSolidity.Ty.tuple [] }
          | _ =>
              Except.error
                (TypeError.arityMismatch "transfer" 1 checkedArgs.length)
      else
        match target with
        | L00_SourceSolidity.Expr.ident "abi" =>
            requireNoNamedArgs ("abi." ++ member) argInfos
            if member == "encode" || member == "encodePacked" then
              checkAbiEncodableArgs env.types checkedArgs
              Except.ok
                { source := expr
                  ty := L00_SourceSolidity.Ty.bytes
                  lvalue := false }
            else if member == "decode" then
              match args, checkedArgs with
              | [ L00_SourceSolidity.Arg.positional _,
                  L00_SourceSolidity.Arg.positional typesExpr ],
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
                  selector.expectAssignableTo (L00_SourceSolidity.Ty.bytesN 4)
                  checkAbiEncodableArgs env.types rest
                  Except.ok
                    { source := expr
                      ty := L00_SourceSolidity.Ty.bytes
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
                      ty := L00_SourceSolidity.Ty.bytes
                      lvalue := false }
              | [] =>
                  Except.error
                    (TypeError.arityMismatch
                      "abi.encodeWithSignature" 1 0)
            else
              Except.error (TypeError.unsupported ("member " ++ member))
        | L00_SourceSolidity.Expr.ident "bytes" =>
            require (member == "concat")
              (TypeError.unsupported ("member " ++ member))
            requireNoNamedArgs "bytes.concat" argInfos
            checkBytesConcatArgs checkedArgs
            Except.ok
              { source := expr
                ty := L00_SourceSolidity.Ty.bytes
                lvalue := false }
        | L00_SourceSolidity.Expr.ident "string" =>
            require (member == "concat")
              (TypeError.unsupported ("member " ++ member))
            requireNoNamedArgs "string.concat" argInfos
            checkStringConcatArgs checkedArgs
            Except.ok
              { source := expr
                ty := L00_SourceSolidity.Ty.string
                lvalue := false }
        | L00_SourceSolidity.Expr.ident "super" => do
            let sig ←
              FunctionSigs.resolveChecked env.types env.superFunctions
                member checkedInfos
            requireCallMutabilityAllowed env sig.mutability
            Except.ok
              { source := expr
                ty := resultTyFromReturns sig.returns
                lvalue := false }
        | targetExpr => do
            let checkUsingOrFallback : Except TypeError CheckedExpr := do
              let targetChecked ← checkExpr env targetExpr
              require (!targetChecked.arraySlice)
                (TypeError.unsupported "member call on array slice")
              let mutation? ←
                checkArrayMutationCall? env expr targetExpr member
                  argInfos checkedArgs targetChecked
              match mutation? with
              | some checked => Except.ok checked
              | none =>
                  let checkUsingCall : Except TypeError CheckedExpr := do
                    let sig ←
                      env.resolveUsingMemberFunctionChecked targetChecked member
                        checkedInfos
                    requireCallMutabilityAllowed env sig.mutability
                    Except.ok
                      { source := expr
                        ty := resultTyFromReturns sig.returns
                        lvalue := false }
                  match targetChecked.ty with
                  | L00_SourceSolidity.Ty.user path =>
                      if env.types.isContractPath path then
                        match env.types.resolveContractMemberFunctionChecked path
                            member checkedInfos with
                        | Except.ok sig => do
                            requireCallMutabilityAllowed env sig.mutability
                            Except.ok
                              { source := expr
                                ty := resultTyFromReturns sig.returns
                                lvalue := false }
                        | Except.error _ => checkUsingCall
                      else
                        checkUsingCall
                  | _ =>
                      match L00_SourceSolidity.Executable.Expr.abiTyWithEnv?
                          env.vars expr with
                      | some ty =>
                          Except.ok
                            { source := expr, ty := ty, lvalue := false }
                      | none => checkUsingCall
            match targetExpr with
            | L00_SourceSolidity.Expr.ident libraryName =>
                if (env.lookupVar? libraryName).isNone &&
                    TypeContext.pathIn
                      (TypeContext.pathOfName libraryName)
                      env.ancestorPaths then
                  let sig ←
                    env.resolveExplicitBaseMemberFunctionChecked libraryName
                      member checkedInfos
                  requireCallMutabilityAllowed env sig.mutability
                  Except.ok
                    { source := expr
                      ty := resultTyFromReturns sig.returns
                      lvalue := false }
                else
                  match env.lookupVar? libraryName,
                      env.types.lookupContractDecl?
                        (TypeContext.pathOfName libraryName) with
                  | none, some libraryDecl =>
                      if libraryDecl.kind ==
                          L00_SourceSolidity.ContractKind.library then
                        let sig ←
                          env.types.resolveLibraryFunctionChecked libraryName
                            member checkedInfos
                        requireCallMutabilityAllowed env sig.mutability
                        Except.ok
                          { source := expr
                            ty := resultTyFromReturns sig.returns
                            lvalue := false }
                      else
                        checkUsingOrFallback
                  | _, _ => checkUsingOrFallback
            | _ => checkUsingOrFallback
  | expr@(L00_SourceSolidity.Expr.call fn args) => do
      let fnChecked ← checkExpr env fn
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      match fnChecked.ty with
      | L00_SourceSolidity.Ty.function params returns mutability _ => do
          require (!ArgInfos.anyNamed argInfos)
            (TypeError.unsupported
              "named arguments for function-typed expression")
          checkCheckedExprsAssignableToFor env.types "function call"
            checkedArgs params
          requireCallMutabilityAllowed env mutability
          Except.ok
            { source := expr, ty := resultTyFromReturns returns,
              lvalue := false }
      | _ =>
          requireCallExprMutabilityAllowed env fn
          match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
          | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
          | none =>
              Except.error
                (TypeError.unsupported
                  ("call with " ++ toString checkedArgs.length ++ " arguments"))
  | expr@(L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.newExpr ty []) options args) => do
      checkTy env.types ty
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      requireCallOptionsAllowedNames ["value", "salt"] options
      match ty with
      | L00_SourceSolidity.Ty.user path =>
          let contractDecl ←
            match env.types.lookupContractDecl? path with
            | some decl => Except.ok decl
            | none => Except.error (TypeError.invalidType ty)
          requireCreatableContractDecl contractDecl
          requireLogOrCreateAllowed env
            "contract creation in view or pure function"
          let checkedArgs ← checkArgs env args
          let constructorSig := ContractDecl.constructorSignature contractDecl
          checkCheckedArgsAssignableToFunctionSig env.types
            ("constructor " ++ contractDecl.name) constructorSig args
            checkedArgs
          requireValueOptionAllowed constructorSig.mutability options
          Except.ok { source := expr, ty := ty, lvalue := false }
      | _ => Except.error (TypeError.invalidType ty)
  | expr@(L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.ident name) options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      let checkedInfos := checkedArgInfosFull args checkedArgs
      match env.lookupVar? name with
      | some (L00_SourceSolidity.Ty.function params returns mutability
          visibility) => do
          require (!ArgInfos.anyNamed argInfos)
            (TypeError.unsupported
              "named arguments for function-typed expression")
          checkCheckedExprsAssignableToFor env.types "function call"
            checkedArgs params
          if options.isEmpty then
            Except.ok ()
          else
            require (visibility == L00_SourceSolidity.Visibility.external_)
              (TypeError.unsupported
                "call options on internal function value")
          requireCallOptionsAllowedNames ["gas", "value"] options
          requireCallMutabilityAllowed env mutability
          requireValueOptionAllowed mutability options
          Except.ok
            { source := expr, ty := resultTyFromReturns returns,
              lvalue := false }
      | _ => do
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
            { source := expr, ty := resultTyFromReturns sig.returns,
              lvalue := false }
  | expr@(L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.member
        (L00_SourceSolidity.Expr.ident "super") member) options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      require options.isEmpty
        (TypeError.unsupported "call options on super call")
      let checkedArgs ← checkArgs env args
      let checkedInfos := checkedArgInfosFull args checkedArgs
      let sig ←
        FunctionSigs.resolveChecked env.types env.superFunctions member
          checkedInfos
      requireCallMutabilityAllowed env sig.mutability
      Except.ok
        { source := expr
          ty := resultTyFromReturns sig.returns
          lvalue := false }
  | L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.member target member) options args => do
      let expr :=
        L00_SourceSolidity.Expr.callWithOptions
          (L00_SourceSolidity.Expr.member target member) options args
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      let checkedInfos := checkedArgInfosFull args checkedArgs
      if lowLevelCallMember member then
        let targetChecked ← checkExpr env target
        require (!ArgInfos.anyNamed argInfos)
          (TypeError.unsupported "named arguments for low-level call")
        require (targetChecked.ty.isAddressLike env.types)
          (TypeError.expectedType
            (L00_SourceSolidity.Ty.address false) targetChecked.ty)
        if member == "call" then
          requireCallOptionsAllowedNames ["gas", "value"] options
        else if member == "staticcall" || member == "delegatecall" then
          requireCallOptionsAllowedNames ["gas"] options
        else
          requireCallOptionsAllowedNames [] options
        if member == "staticcall" then
          requireCallMutabilityAllowed env
            L00_SourceSolidity.StateMutability.view
        else
          requireCallMutabilityAllowed env
            L00_SourceSolidity.StateMutability.nonpayable
        if member == "call" || member == "staticcall" ||
            member == "delegatecall" then
          match checkedArgs with
          | [data] => do
              data.expectAssignableTo L00_SourceSolidity.Ty.bytes
              Except.ok { source := expr, ty := lowLevelCallReturnTy }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  ("low-level " ++ member) 1 checkedArgs.length)
        else if member == "send" then
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectInteger
              Except.ok
                { source := expr, ty := L00_SourceSolidity.Ty.bool }
          | _ =>
              Except.error
                (TypeError.arityMismatch "send" 1 checkedArgs.length)
        else
          require targetChecked.ty.isPayableAddress
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address true) targetChecked.ty)
          match checkedArgs with
          | [amount] => do
              amount.expectInteger
              Except.ok
                { source := expr
                  ty := L00_SourceSolidity.Ty.tuple [] }
          | _ =>
              Except.error
                (TypeError.arityMismatch "transfer" 1 checkedArgs.length)
      else
        let targetChecked ← checkExpr env target
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
            | L00_SourceSolidity.Ty.user path => do
                let sig ←
                  env.types.resolveContractMemberFunctionChecked path member
                    checkedInfos
                requireCallMutabilityAllowed env sig.mutability
                requireValueOptionAllowed sig.mutability options
                Except.ok
                  { source := expr
                    ty := resultTyFromReturns sig.returns
                    lvalue := false }
            | _ =>
                match L00_SourceSolidity.Executable.Expr.abiTyWithEnv?
                    env.vars expr with
                | some ty =>
                    Except.ok { source := expr, ty := ty, lvalue := false }
                | none =>
                    Except.error
                      (TypeError.unsupported ("member call " ++ member))
  | expr@(L00_SourceSolidity.Expr.callWithOptions fn options args) => do
      ensureUniqueNames "call option" (CallOptions.names options)
      checkCallOptionsLoop env options
      let fnChecked ← checkExpr env fn
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      match fnChecked.ty with
      | L00_SourceSolidity.Ty.function params returns mutability
          visibility => do
          require (!ArgInfos.anyNamed argInfos)
            (TypeError.unsupported
              "named arguments for function-typed expression")
          checkCheckedExprsAssignableToFor env.types "function call"
            checkedArgs params
          if options.isEmpty then
            Except.ok ()
          else
            require (visibility == L00_SourceSolidity.Visibility.external_)
              (TypeError.unsupported
                "call options on internal function value")
          requireCallOptionsAllowedNames ["gas", "value"] options
          requireCallMutabilityAllowed env mutability
          requireValueOptionAllowed mutability options
          Except.ok
            { source := expr, ty := resultTyFromReturns returns,
              lvalue := false }
      | _ =>
          requireCallExprMutabilityAllowed env fn
          match L00_SourceSolidity.Executable.Expr.abiTyWithEnv? env.vars expr with
          | some ty => Except.ok { source := expr, ty := ty, lvalue := false }
          | none =>
              Except.error
                (TypeError.unsupported
                  ("call with " ++ toString checkedArgs.length ++ " arguments"))
  | expr@(L00_SourceSolidity.Expr.newExpr ty args) => do
      checkTy env.types ty
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfos args checkedArgs
      match ty with
      | L00_SourceSolidity.Ty.bytes =>
          requireNoNamedArgs "new bytes" argInfos
          match checkedArgs with
          | [length] => do
              length.expectInteger
              Except.ok { source := expr, ty := ty, lvalue := false }
          | _ =>
              Except.error
                (TypeError.arityMismatch "new bytes" 1 checkedArgs.length)
      | L00_SourceSolidity.Ty.array _ none =>
          requireNoNamedArgs "new dynamic array" argInfos
          match checkedArgs with
          | [length] => do
              length.expectInteger
              Except.ok { source := expr, ty := ty, lvalue := false }
          | _ =>
              Except.error
                (TypeError.arityMismatch
                  "new dynamic array" 1 checkedArgs.length)
      | L00_SourceSolidity.Ty.user path =>
          let contractDecl ←
            match env.types.lookupContractDecl? path with
            | some decl => Except.ok decl
            | none => Except.error (TypeError.invalidType ty)
          requireCreatableContractDecl contractDecl
          requireLogOrCreateAllowed env
            "contract creation in view or pure function"
          let constructorSig := ContractDecl.constructorSignature contractDecl
          checkCheckedArgsAssignableToFunctionSig env.types
            ("constructor " ++ contractDecl.name) constructorSig args
            checkedArgs
          Except.ok { source := expr, ty := ty, lvalue := false }
      | _ => Except.error (TypeError.invalidType ty)
  | expr@(L00_SourceSolidity.Expr.tuple items) => do
      let tys ← checkTupleItems env items
      Except.ok
        { source := expr, ty := L00_SourceSolidity.Ty.tuple tys,
          lvalue := false }
  | L00_SourceSolidity.Expr.array [] =>
      Except.error (TypeError.unsupported "empty array literal")
  | expr@(L00_SourceSolidity.Expr.array (head :: rest)) => do
      let checkedElements ← checkExprList env (head :: rest)
      let elementTy ←
        match CheckedExprs.commonArrayElementTy? checkedElements with
        | some ty => Except.ok ty
        | none =>
            Except.error
              (TypeError.unsupported "array literal common type")
      checkCheckedExprsAssignableToFor env.types "array literal" checkedElements
        (List.replicate checkedElements.length elementTy)
      Except.ok
        { source := expr
          ty := L00_SourceSolidity.Ty.array elementTy
            (some (head :: rest).length)
          lvalue := false }
  | expr@(L00_SourceSolidity.Expr.enumFromUInt _ inner) => do
      let checkedInner ← checkExpr env inner
      checkedInner.expectInteger
      Except.ok
        { source := expr
          ty := L00_SourceSolidity.Ty.uint 8
          lvalue := false }
  | expr@(L00_SourceSolidity.Expr.unary op inner) => do
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
      | L00_SourceSolidity.UnaryOp.logicalNot =>
          checked.expectBool
          Except.ok { source := expr, ty := L00_SourceSolidity.Ty.bool }
      | L00_SourceSolidity.UnaryOp.bitNot =>
          checked.expectShiftLeftOperand
          Except.ok { source := expr, ty := checked.ty }
      | L00_SourceSolidity.UnaryOp.neg =>
          match L00_SourceSolidity.Executable.Expr.toCoreNumericLiteralAs?
              (L00_SourceSolidity.Ty.int 256) expr with
          | some _ =>
              Except.ok
                { source := expr
                  ty := L00_SourceSolidity.Ty.int 256 }
          | none => do
              checked.expectSignedInteger
              Except.ok { source := expr, ty := checked.ty }
      | L00_SourceSolidity.UnaryOp.delete =>
          require checked.lvalue (TypeError.expectedLValue inner)
          checked.expectWritableLocation inner
          match Expr.directIdentName? inner with
          | some name =>
              require (!env.isLocalStorageRef name)
                (TypeError.invalidDataLocation checked.ty
                  (some L00_SourceSolidity.DataLocation.storage))
          | none => Except.ok ()
          if checked.stateLValue then
            requireStateWriteAllowed env
          else
            Except.ok ()
          Except.ok { source := expr, ty := checked.ty, lvalue := false }
      | L00_SourceSolidity.UnaryOp.preIncrement
      | L00_SourceSolidity.UnaryOp.preDecrement
      | L00_SourceSolidity.UnaryOp.postIncrement
      | L00_SourceSolidity.UnaryOp.postDecrement =>
          require checked.lvalue (TypeError.expectedLValue inner)
          checked.expectWritableLocation inner
          if checked.stateLValue then
            requireStateWriteAllowed env
          else
            Except.ok ()
          checked.expectInteger
          Except.ok { source := expr, ty := checked.ty, lvalue := false }
  | expr@(L00_SourceSolidity.Expr.binary op lhs rhs) => do
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
      | L00_SourceSolidity.BinaryOp.boolAnd
      | L00_SourceSolidity.BinaryOp.boolOr =>
          lhsChecked.expectBool
          rhsChecked.expectBool
          Except.ok { source := expr, ty := L00_SourceSolidity.Ty.bool }
      | L00_SourceSolidity.BinaryOp.lt
      | L00_SourceSolidity.BinaryOp.gt
      | L00_SourceSolidity.BinaryOp.le
      | L00_SourceSolidity.BinaryOp.ge =>
          let _ ← CheckedExprs.relationalTy lhsChecked rhsChecked
          Except.ok { source := expr, ty := L00_SourceSolidity.Ty.bool }
      | L00_SourceSolidity.BinaryOp.eq
      | L00_SourceSolidity.BinaryOp.ne =>
          require
            ((TypeContext.canImplicitlyConvert env.types
                rhsChecked.ty lhsChecked.ty ||
              implicitLiteralFits lhsChecked.ty rhsChecked.source) ||
            (TypeContext.canImplicitlyConvert env.types
                lhsChecked.ty rhsChecked.ty ||
              implicitLiteralFits rhsChecked.ty lhsChecked.source))
            (TypeError.expectedType lhsChecked.ty rhsChecked.ty)
          Except.ok { source := expr, ty := L00_SourceSolidity.Ty.bool }
      | L00_SourceSolidity.BinaryOp.add
      | L00_SourceSolidity.BinaryOp.sub
      | L00_SourceSolidity.BinaryOp.mul
      | L00_SourceSolidity.BinaryOp.div
      | L00_SourceSolidity.BinaryOp.mod =>
          let ty ← CheckedExprs.arithmeticTy lhsChecked rhsChecked
          Except.ok { source := expr, ty := ty }
      | L00_SourceSolidity.BinaryOp.exp =>
          lhsChecked.expectInteger
          rhsChecked.expectInteger
          Except.ok { source := expr, ty := lhsChecked.ty }
      | L00_SourceSolidity.BinaryOp.bitAnd
      | L00_SourceSolidity.BinaryOp.bitOr
      | L00_SourceSolidity.BinaryOp.bitXor =>
          let ty ← CheckedExprs.bitwiseTy lhsChecked rhsChecked
          Except.ok { source := expr, ty := ty }
      | L00_SourceSolidity.BinaryOp.shl
      | L00_SourceSolidity.BinaryOp.shr =>
          lhsChecked.expectShiftLeftOperand
          rhsChecked.expectUnsignedInteger
          Except.ok { source := expr, ty := lhsChecked.ty }
      | L00_SourceSolidity.BinaryOp.sar =>
          lhsChecked.expectSignedInteger
          rhsChecked.expectUnsignedInteger
          Except.ok { source := expr, ty := lhsChecked.ty }
  | expr@(L00_SourceSolidity.Expr.ternary cond thenExpr elseExpr) => do
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
        if TypeContext.canImplicitlyConvert env.types
            elseChecked.ty thenChecked.ty then
          thenChecked.ty
        else
          elseChecked.ty
      Except.ok { source := expr, ty := resultTy }
  | expr@(L00_SourceSolidity.Expr.assign lhs _ rhs) => do
      match lhs with
      | L00_SourceSolidity.Expr.tuple lhsItems =>
          match expr with
          | L00_SourceSolidity.Expr.assign _
              L00_SourceSolidity.AssignOp.assign _ => do
              let targets ← checkTupleAssignmentTargets env lhsItems
              let literalValues? ←
                checkTupleAssignmentLiteralValues? env rhs
              let resultTys ←
                match literalValues? with
                | some values =>
                    checkTupleAssignmentTargetsWithValues env targets values
                | none => do
                    let rhsChecked ← checkExpr env rhs
                    match rhsChecked.ty with
                    | L00_SourceSolidity.Ty.tuple tys =>
                        checkTupleAssignmentTargetsWithTys env rhsChecked
                          targets tys
                    | _ =>
                        Except.error
                          (TypeError.arityMismatch
                            "tuple assignment" lhsItems.length 1)
              Except.ok
                { source := expr
                  ty := L00_SourceSolidity.Ty.tuple resultTys
                  lvalue := false }
          | _ => Except.error (TypeError.expectedLValue lhs)
      | _ => do
          let lhsChecked ← checkExpr env lhs
          require lhsChecked.lvalue (TypeError.expectedLValue lhs)
          lhsChecked.expectWritableLocation lhs
          if lhsChecked.stateLValue then
            requireStateWriteAllowed env
          else
            Except.ok ()
          let checkOrdinaryRhs : Except TypeError CheckedExpr := do
            let rhsChecked ← checkExpr env rhs
            match Expr.directIdentName? lhs with
            | some name =>
                require (!env.isLocalStorageRef name || rhsChecked.stateLValue)
                  (TypeError.invalidDataLocation lhsChecked.ty
                    (some L00_SourceSolidity.DataLocation.storage))
            | none => Except.ok ()
            let opResultTy ←
              match expr with
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.assign _ => do
                  rhsChecked.expectAssignableToIn env.types lhsChecked.ty
                  Except.ok lhsChecked.ty
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.addAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.subAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.mulAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.divAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.modAssign _ =>
                  CheckedExprs.arithmeticTy lhsChecked rhsChecked
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.bitAndAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.bitOrAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.bitXorAssign _ =>
                  CheckedExprs.bitwiseTy lhsChecked rhsChecked
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.shlAssign _
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.shrAssign _ => do
                  lhsChecked.expectShiftLeftOperand
                  rhsChecked.expectUnsignedInteger
                  Except.ok lhsChecked.ty
              | L00_SourceSolidity.Expr.assign _
                  L00_SourceSolidity.AssignOp.sarAssign _ => do
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
          | L00_SourceSolidity.Expr.assign _
              L00_SourceSolidity.AssignOp.assign _ =>
              match
                  checkInternalFunctionValueAssignable?
                    env rhs lhsChecked.ty with
              | some result => do
                  result
                  Except.ok
                    { source := expr
                      ty := lhsChecked.ty
                      lvalue := false }
              | none => checkOrdinaryRhs
          | _ => checkOrdinaryRhs
  | expr@(L00_SourceSolidity.Expr.payableConversion inner) => do
      let checked ← checkExpr env inner
      match checked.ty with
      | L00_SourceSolidity.Ty.address _ =>
          Except.ok
            { source := expr, ty := L00_SourceSolidity.Ty.address true,
              lvalue := false }
      | L00_SourceSolidity.Ty.user path =>
          require (env.types.contractCanReceiveEther path)
            (TypeError.expectedType
              (L00_SourceSolidity.Ty.address false) checked.ty)
          Except.ok
            { source := expr, ty := L00_SourceSolidity.Ty.address true,
              lvalue := false }
      | other =>
          match L00_SourceSolidity.Executable.Expr.toCorePayableLiteral?
              inner with
          | some _ =>
              Except.ok
                { source := expr, ty := L00_SourceSolidity.Ty.address true,
                  lvalue := false }
          | none =>
              Except.error
                (TypeError.expectedType
                  (L00_SourceSolidity.Ty.address false) other)
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

def checkArg (env : CheckEnv) : L00_SourceSolidity.Arg ->
    Except TypeError CheckedExpr
  | L00_SourceSolidity.Arg.positional expr => checkExpr env expr
  | L00_SourceSolidity.Arg.named _ expr => checkExpr env expr
termination_by arg => sizeOf arg
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkArgs (env : CheckEnv) : List L00_SourceSolidity.Arg ->
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
    L00_SourceSolidity.Arg -> Except TypeError CheckedExpr
  | L00_SourceSolidity.Arg.positional expr
  | L00_SourceSolidity.Arg.named _ expr =>
      match checkInternalFunctionValueAssignable? env expr expected with
      | some (Except.ok _) =>
          Except.ok
            { source := expr
              ty := expected
              lvalue := false
              stateLValue := false }
      | some (Except.error err) => Except.error err
      | none => do
          let checked ← checkExpr env expr
          checked.expectAssignableToIn env.types expected
          Except.ok checked
termination_by arg => sizeOf arg
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkPositionalArgsAssignableToParamsFor
    (env : CheckEnv) (what : String) :
    List L00_SourceSolidity.Arg -> List Ty ->
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

def checkMemberCallArgsContextual
    (env : CheckEnv) (target : L00_SourceSolidity.Expr)
    (member : Name) (args : List L00_SourceSolidity.Arg) :
    Except TypeError (List CheckedExpr) := do
  require (!Args.anyNamed args)
    (TypeError.unsupported "contextual named member-call arguments")
  require (!lowLevelCallMember member)
    (TypeError.unsupported "contextual low-level member call")
  let targetChecked ← checkExpr env target
  require (!targetChecked.arraySlice)
    (TypeError.unsupported "member call on array slice")
  let candidates ←
    match target with
    | L00_SourceSolidity.Expr.ident libraryName =>
        match env.lookupVar? libraryName,
            env.types.lookupContractDecl?
              (TypeContext.pathOfName libraryName) with
        | none, some libraryDecl =>
            if libraryDecl.kind == L00_SourceSolidity.ContractKind.library then
              Except.ok
                (FunctionSigs.nonPrivate
                  (ContractDecl.directFunctionSigs libraryDecl))
            else
              UsingDecls.memberCandidates env targetChecked member
                env.usingDecls
        | _, _ =>
            UsingDecls.memberCandidates env targetChecked member
              env.usingDecls
    | _ =>
        UsingDecls.memberCandidates env targetChecked member env.usingDecls
  let sig ← FunctionSigs.resolveContextual env candidates member args
  let checkedArgs ←
    checkPositionalArgsAssignableToParamsFor
      env "member call" args sig.params
  checkCheckedExprsStorageRefsFor "member call" checkedArgs
    sig.paramStorageRefs
  Except.ok checkedArgs
termination_by 1 + sizeOf target + sizeOf args
decreasing_by
  all_goals
    simp_wf
    omega

def checkCallOption (env : CheckEnv) :
    L00_SourceSolidity.CallOption -> Except TypeError Unit
  | L00_SourceSolidity.CallOption.named name expr => do
      let checked ← checkExpr env expr
      if name == "gas" || name == "value" then
        checked.expectInteger
      else if name == "salt" then
        requireEqTy (L00_SourceSolidity.Ty.bytesN 32) checked.ty
      else
        Except.error (TypeError.unsupported ("call option " ++ name))
termination_by option => sizeOf option
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkCallOptionsLoop (env : CheckEnv) :
    List L00_SourceSolidity.CallOption -> Except TypeError Unit
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
    List L00_SourceSolidity.TupleItem -> Except TypeError (List Ty)
  | [] => Except.ok []
  | L00_SourceSolidity.TupleItem.hole :: rest => do
      let tail ← checkTupleItems env rest
      Except.ok tail
  | L00_SourceSolidity.TupleItem.value expr :: rest => do
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
    List L00_SourceSolidity.TupleItem ->
    Except TypeError (List TupleAssignmentTarget)
  | [] => Except.ok []
  | L00_SourceSolidity.TupleItem.hole :: rest => do
      let tail ← checkTupleAssignmentTargets env rest
      Except.ok (none :: tail)
  | L00_SourceSolidity.TupleItem.value target :: rest => do
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

def checkTupleAssignmentValues (env : CheckEnv) :
    List L00_SourceSolidity.TupleItem -> Except TypeError (List CheckedExpr)
  | [] => Except.ok []
  | L00_SourceSolidity.TupleItem.hole :: _ =>
      Except.error (TypeError.unsupported "tuple hole in value position")
  | L00_SourceSolidity.TupleItem.value expr :: rest => do
      let checked ← checkExpr env expr
      let tail ← checkTupleAssignmentValues env rest
      Except.ok (checked :: tail)
termination_by items => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkTupleAssignmentLiteralValues? (env : CheckEnv) :
    L00_SourceSolidity.Expr -> Except TypeError (Option (List CheckedExpr))
  | L00_SourceSolidity.Expr.tuple items => do
      let values ← checkTupleAssignmentValues env items
      Except.ok (some values)
  | _ => Except.ok none
termination_by expr => sizeOf expr
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkTupleItemValuesAssignableTo (env : CheckEnv) :
    List L00_SourceSolidity.TupleItem -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | L00_SourceSolidity.TupleItem.value expr :: rest, ty :: tyRest => do
      let checked ← checkExpr env expr
      checked.expectAssignableToIn env.types ty
      checkTupleItemValuesAssignableTo env rest tyRest
  | L00_SourceSolidity.TupleItem.hole :: _, _ =>
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

def checkEncodeCallTupleItems (env : CheckEnv) :
    List L00_SourceSolidity.TupleItem -> Except TypeError (List CheckedExpr)
  | [] => Except.ok []
  | L00_SourceSolidity.TupleItem.hole :: _ =>
      Except.error
        (TypeError.invalidAbiCall
          "abi.encodeCall argument tuple cannot contain holes")
  | L00_SourceSolidity.TupleItem.value expr :: rest => do
      let checked ← checkExpr env expr
      let tail ← checkEncodeCallTupleItems env rest
      Except.ok (checked :: tail)
termination_by items => sizeOf items
decreasing_by
  all_goals
    try subst expr
    simp_wf
    try omega

def checkArrayElements (env : CheckEnv) (expected : Ty) :
    List L00_SourceSolidity.Expr -> Except TypeError Unit
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
    List L00_SourceSolidity.Expr -> Except TypeError (List CheckedExpr)
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

def constantBuiltinIdentCallAllowed (name : Name) : Bool :=
  name == "keccak256" || name == "sha256" || name == "ripemd160" ||
    name == "ecrecover" || name == "addmod" || name == "mulmod" ||
    name == "erc7201"

def constantAbiMemberCallAllowed (member : Name) : Bool :=
  member == "encode" || member == "encodePacked" ||
    member == "encodeWithSelector" || member == "encodeWithSignature" ||
    member == "decode"

def exprIsCompileTimeConstantCallTarget
    (fn : L00_SourceSolidity.Expr) : Bool :=
  match fn with
  | L00_SourceSolidity.Expr.typeName _ => true
  | L00_SourceSolidity.Expr.ident name =>
      constantBuiltinIdentCallAllowed name
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "abi") member =>
      constantAbiMemberCallAllowed member
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "bytes") "concat" => true
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.ident "string") "concat" => true
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName _) member =>
      member == "wrap" || member == "unwrap"
  | _ => false

mutual

def exprIsCompileTimeConstant (env : CheckEnv) :
    L00_SourceSolidity.Expr -> Bool
  | L00_SourceSolidity.Expr.literal _ => true
  | L00_SourceSolidity.Expr.ident name => env.isConstantName name
  | L00_SourceSolidity.Expr.typeName _ => true
  | L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName _) _ => true
  | L00_SourceSolidity.Expr.member _ _ => false
  | L00_SourceSolidity.Expr.index base index =>
      exprIsCompileTimeConstant env base &&
        exprIsCompileTimeConstant env index
  | L00_SourceSolidity.Expr.slice base start? stop? =>
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
  | L00_SourceSolidity.Expr.call fn args =>
      exprIsCompileTimeConstantCallTarget fn &&
        argsAllCompileTimeConstant env args
  | L00_SourceSolidity.Expr.callWithOptions _ _ _ => false
  | L00_SourceSolidity.Expr.newExpr _ args =>
      argsAllCompileTimeConstant env args
  | L00_SourceSolidity.Expr.tuple items =>
      tupleItemsAllCompileTimeConstant env items
  | L00_SourceSolidity.Expr.array exprs =>
      exprsAllCompileTimeConstant env exprs
  | L00_SourceSolidity.Expr.enumFromUInt _ inner =>
      exprIsCompileTimeConstant env inner
  | L00_SourceSolidity.Expr.unary op inner =>
      match op with
      | L00_SourceSolidity.UnaryOp.logicalNot
      | L00_SourceSolidity.UnaryOp.bitNot
      | L00_SourceSolidity.UnaryOp.neg =>
          exprIsCompileTimeConstant env inner
      | L00_SourceSolidity.UnaryOp.delete
      | L00_SourceSolidity.UnaryOp.preIncrement
      | L00_SourceSolidity.UnaryOp.preDecrement
      | L00_SourceSolidity.UnaryOp.postIncrement
      | L00_SourceSolidity.UnaryOp.postDecrement => false
  | L00_SourceSolidity.Expr.binary _ lhs rhs =>
      exprIsCompileTimeConstant env lhs &&
        exprIsCompileTimeConstant env rhs
  | L00_SourceSolidity.Expr.ternary cond thenExpr elseExpr =>
      exprIsCompileTimeConstant env cond &&
        exprIsCompileTimeConstant env thenExpr &&
          exprIsCompileTimeConstant env elseExpr
  | L00_SourceSolidity.Expr.assign _ _ _ => false
  | L00_SourceSolidity.Expr.payableConversion inner =>
      exprIsCompileTimeConstant env inner

def exprsAllCompileTimeConstant (env : CheckEnv) :
    List L00_SourceSolidity.Expr -> Bool
  | [] => true
  | expr :: rest =>
      exprIsCompileTimeConstant env expr &&
        exprsAllCompileTimeConstant env rest

def argIsCompileTimeConstant (env : CheckEnv) :
    L00_SourceSolidity.Arg -> Bool
  | L00_SourceSolidity.Arg.positional expr =>
      exprIsCompileTimeConstant env expr
  | L00_SourceSolidity.Arg.named _ expr =>
      exprIsCompileTimeConstant env expr

def argsAllCompileTimeConstant (env : CheckEnv) :
    List L00_SourceSolidity.Arg -> Bool
  | [] => true
  | arg :: rest =>
      argIsCompileTimeConstant env arg &&
        argsAllCompileTimeConstant env rest

def tupleItemIsCompileTimeConstant (env : CheckEnv) :
    L00_SourceSolidity.TupleItem -> Bool
  | L00_SourceSolidity.TupleItem.hole => true
  | L00_SourceSolidity.TupleItem.value expr =>
      exprIsCompileTimeConstant env expr

def tupleItemsAllCompileTimeConstant (env : CheckEnv) :
    List L00_SourceSolidity.TupleItem -> Bool
  | [] => true
  | item :: rest =>
      tupleItemIsCompileTimeConstant env item &&
        tupleItemsAllCompileTimeConstant env rest

end

def Expr.isCompileTimeConstant (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Bool :=
  exprIsCompileTimeConstant env expr

def exprIsStorageLayoutBaseComptime (env : CheckEnv) :
    L00_SourceSolidity.Expr -> Bool
  | L00_SourceSolidity.Expr.literal (L00_SourceSolidity.Literal.number _) =>
      true
  | L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.unitNumber _ _) => true
  | L00_SourceSolidity.Expr.ident name => env.isConstantName name
  | L00_SourceSolidity.Expr.call (L00_SourceSolidity.Expr.ident "erc7201")
      [L00_SourceSolidity.Arg.positional id] =>
      exprIsCompileTimeConstant env id
  | L00_SourceSolidity.Expr.unary L00_SourceSolidity.UnaryOp.neg inner =>
      exprIsStorageLayoutBaseComptime env inner
  | L00_SourceSolidity.Expr.binary _ lhs rhs =>
      exprIsStorageLayoutBaseComptime env lhs &&
        exprIsStorageLayoutBaseComptime env rhs
  | _ => false

def Expr.isStorageLayoutBaseComptime (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Bool :=
  exprIsStorageLayoutBaseComptime env expr

def Exprs.allCompileTimeConstant (env : CheckEnv)
    (exprs : List L00_SourceSolidity.Expr) : Bool :=
  exprsAllCompileTimeConstant env exprs

def StateVarDecl.hasCompileTimeImmutableInit
    (constantBindings : List (Name × Bool))
    (decl : L00_SourceSolidity.StateVarDecl) : Bool :=
  decl.mutability == L00_SourceSolidity.VarMutability.immutable &&
    match decl.init with
    | some init =>
        Expr.isCompileTimeConstant
          ({ constantBindings := constantBindings } : CheckEnv) init
    | none => false

def StateVarDecl.runtimeStateNameWith?
    (constantBindings : List (Name × Bool))
    (decl : L00_SourceSolidity.StateVarDecl) : Option Name :=
  if decl.mutability == L00_SourceSolidity.VarMutability.mutable ||
      decl.mutability == L00_SourceSolidity.VarMutability.transient ||
      (decl.mutability == L00_SourceSolidity.VarMutability.immutable &&
        !StateVarDecl.hasCompileTimeImmutableInit constantBindings decl) then
    some decl.name
  else
    none

def StateVarDecls.runtimeStateNamesWith
    (constantBindings : List (Name × Bool)) :
    List L00_SourceSolidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.runtimeStateNameWith? constantBindings decl with
      | some name =>
          name :: StateVarDecls.runtimeStateNamesWith constantBindings rest
      | none => StateVarDecls.runtimeStateNamesWith constantBindings rest

def checkExprAssignableTo (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) (expected : Ty) :
    Except TypeError Unit := do
  match checkInternalFunctionValueAssignable? env expr expected with
  | some result => result
  | none => do
      let checked ← checkExpr env expr
      checked.expectAssignableToIn env.types expected

def checkReturnExprs (env : CheckEnv)
    (expr? : Option L00_SourceSolidity.Expr) : Except TypeError Unit :=
  match expr?, env.returnTys with
  | none, [] => Except.ok ()
  | none, expected =>
      Except.error (TypeError.returnArityMismatch expected.length 0)
  | some expr, [expected] => checkExprAssignableTo env expr expected
  | some (L00_SourceSolidity.Expr.tuple items), expected =>
      checkTupleItemValuesAssignableTo env items expected
  | some expr, expected => do
      let checked ← checkExpr env expr
      match checked.ty with
      | L00_SourceSolidity.Ty.tuple actual =>
          require (sameLength actual expected)
            (TypeError.returnArityMismatch expected.length actual.length)
          let rec checkTuple : List Ty -> List Ty -> Except TypeError Unit
            | [], [] => Except.ok ()
            | actualTy :: actualRest, expectedTy :: expectedRest => do
                require
                  (TypeContext.canImplicitlyConvert env.types actualTy
                    expectedTy)
                  (TypeError.expectedType expectedTy actualTy)
                checkTuple actualRest expectedRest
            | actualRest, expectedRest =>
                Except.error
                  (TypeError.returnArityMismatch
                    expectedRest.length actualRest.length)
          checkTuple actual expected
      | _ =>
          Except.error (TypeError.returnArityMismatch expected.length 1)

def checkTysAssignableTo (types : TypeContext) :
    List Ty -> List Ty -> Except TypeError Unit
  | [], [] => Except.ok ()
  | actualTy :: actualRest, expectedTy :: expectedRest => do
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
  | [] => requireEqTy (L00_SourceSolidity.Ty.tuple []) checked.ty
  | [ty] => checked.expectAssignableToIn types ty
  | tys =>
      match checked.ty with
      | L00_SourceSolidity.Ty.tuple actual =>
          checkTysAssignableTo types actual tys
      | _ => Except.error (TypeError.returnArityMismatch tys.length 1)

def Ty.isExternalFunction : Ty -> Bool
  | L00_SourceSolidity.Ty.function _ _ _
      L00_SourceSolidity.Visibility.external_ => true
  | _ => false

def isKnownContractCreationTryTarget (env : CheckEnv) :
    L00_SourceSolidity.Expr -> Bool
  | L00_SourceSolidity.Expr.newExpr
      (L00_SourceSolidity.Ty.user path) _ =>
      env.types.isContractPath path
  | L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.newExpr
        (L00_SourceSolidity.Ty.user path) _) _ _ =>
      env.types.isContractPath path
  | _ => false

def checkTryExternalMemberCallTarget (env : CheckEnv)
    (target : L00_SourceSolidity.Expr) (member : Name)
    (args : List L00_SourceSolidity.Arg) : Except TypeError Unit := do
  let checkedArgs ← checkArgs env args
  let checkedInfos := checkedArgInfosFull args checkedArgs
  let targetChecked ← checkExpr env target
  match targetChecked.ty with
  | L00_SourceSolidity.Ty.user path =>
      let sig ←
        env.types.resolveContractMemberFunctionChecked path member
          checkedInfos
      require sig.externallyCallable
        (TypeError.invalidTryCatch
          "try target is not an external function call")
  | _ =>
      Except.error
        (TypeError.invalidTryCatch
          "try target is not an external function call")

def checkTryTargetKind (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Except TypeError Unit :=
  match expr with
  | L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.member target member) args =>
      checkTryExternalMemberCallTarget env target member args
  | L00_SourceSolidity.Expr.callWithOptions
      (L00_SourceSolidity.Expr.member target member) _ args =>
      checkTryExternalMemberCallTarget env target member args
  | L00_SourceSolidity.Expr.call
      (L00_SourceSolidity.Expr.ident name) _ =>
      match env.lookupVar? name with
      | some ty =>
          require ty.isExternalFunction
            (TypeError.invalidTryCatch
              "try target is not an external function call")
      | none =>
          Except.error
            (TypeError.invalidTryCatch
              "try target is not an external function call")
  | L00_SourceSolidity.Expr.call fn _ => do
      let fnChecked ← checkExpr env fn
      require fnChecked.ty.isExternalFunction
        (TypeError.invalidTryCatch
          "try target is not an external function call")
  | L00_SourceSolidity.Expr.callWithOptions fn _ _ => do
      let fnChecked ← checkExpr env fn
      require fnChecked.ty.isExternalFunction
        (TypeError.invalidTryCatch
          "try target is not an external function call")
  | _ =>
      require (isKnownContractCreationTryTarget env expr)
        (TypeError.invalidTryCatch
          "try target is not an external call or contract creation")

def checkTryTarget (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Except TypeError CheckedExpr := do
  checkTryTargetKind env expr
  checkExpr env expr

def checkEventEmission (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Except TypeError Unit :=
  match expr with
  | L00_SourceSolidity.Expr.call (L00_SourceSolidity.Expr.ident name) args => do
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfosFull args checkedArgs
      let _ ← EventSigs.resolveChecked env.types env.events name argInfos
      Except.ok ()
  | other => do
      let _ ← checkExpr env other
      Except.ok ()

def checkRevertCall (env : CheckEnv)
    (expr : L00_SourceSolidity.Expr) : Except TypeError Unit :=
  match expr with
  | L00_SourceSolidity.Expr.call (L00_SourceSolidity.Expr.ident name) args => do
      let checkedArgs ← checkArgs env args
      let argInfos := checkedArgInfosFull args checkedArgs
      let _ ← ErrorSigs.resolveChecked env.types env.errors name argInfos
      Except.ok ()
  | other => do
      let _ ← checkExpr env other
      Except.ok ()

def VarBinding.checkType (env : CheckEnv)
    (binding : L00_SourceSolidity.VarBinding) :
    Except TypeError Ty :=
  match binding.ty, binding.name with
  | some ty, _ => do
      checkLocationForTy env.types ty binding.location
      Except.ok ty
  | none, some name => Except.error (TypeError.missingTypeAnnotation name)
  | none, none => Except.error (TypeError.unsupported "anonymous untyped binding")

def VarBinding.namedType? (env : CheckEnv)
    (binding : L00_SourceSolidity.VarBinding) :
    Except TypeError (Option (Name × Ty)) := do
  let ty ← VarBinding.checkType env binding
  match binding.name with
  | some name => Except.ok (some (name, ty))
  | none => Except.ok none

def VarBinding.isStorageRef (types : TypeContext)
    (binding : L00_SourceSolidity.VarBinding) : Bool :=
  match binding.ty with
  | some ty =>
      Ty.needsDataLocation types ty &&
        binding.location == some L00_SourceSolidity.DataLocation.storage
  | none => false

def VarBinding.namedTypeStorageRef? (env : CheckEnv)
    (binding : L00_SourceSolidity.VarBinding) :
    Except TypeError (Option (Name × Ty × Bool)) := do
  let ty ← VarBinding.checkType env binding
  match binding.name with
  | some name =>
      Except.ok
        (some (name, ty, VarBinding.isStorageRef env.types binding))
  | none => Except.ok none

def VarBinding.namedDataLocation? (env : CheckEnv)
    (binding : L00_SourceSolidity.VarBinding) :
    Except TypeError (Option (Name × L00_SourceSolidity.DataLocation)) := do
  let ty ← VarBinding.checkType env binding
  match binding.name, binding.location with
  | some name, some location =>
      if Ty.needsDataLocation env.types ty then
        Except.ok (some (name, location))
      else
        Except.ok none
  | _, _ => Except.ok none

def VarBinding.checkStorageRefInitializer (env : CheckEnv)
    (binding : L00_SourceSolidity.VarBinding) (checked : CheckedExpr) :
    Except TypeError Unit := do
  let ty ← VarBinding.checkType env binding
  if VarBinding.isStorageRef env.types binding then
    checked.expectAssignableToIn env.types ty
    require checked.stateLValue
      (TypeError.invalidDataLocation ty binding.location)
  else
    Except.ok ()

def VarBindings.namedTypes (env : CheckEnv) :
    List L00_SourceSolidity.VarBinding ->
    Except TypeError (List (Name × Ty))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedType? env binding
      let tail ← VarBindings.namedTypes env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.namedTypeStorageRefs (env : CheckEnv) :
    List L00_SourceSolidity.VarBinding ->
    Except TypeError (List (Name × Ty × Bool))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedTypeStorageRef? env binding
      let tail ← VarBindings.namedTypeStorageRefs env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.namedDataLocations (env : CheckEnv) :
    List L00_SourceSolidity.VarBinding ->
    Except TypeError (List (Name × L00_SourceSolidity.DataLocation))
  | [] => Except.ok []
  | binding :: rest => do
      let head? ← VarBinding.namedDataLocation? env binding
      let tail ← VarBindings.namedDataLocations env rest
      match head? with
      | some head => Except.ok (head :: tail)
      | none => Except.ok tail

def VarBindings.anyStorageRef (types : TypeContext) :
    List L00_SourceSolidity.VarBinding -> Bool
  | [] => false
  | binding :: rest =>
      VarBinding.isStorageRef types binding ||
        VarBindings.anyStorageRef types rest

def VarBindings.checkStorageRefTupleInitializers (env : CheckEnv) :
    List L00_SourceSolidity.VarBinding ->
    List L00_SourceSolidity.TupleItem -> Except TypeError Unit
  | [], [] => Except.ok ()
  | binding :: bindingRest,
      L00_SourceSolidity.TupleItem.value expr :: itemRest => do
      let checked ← checkExpr env expr
      VarBinding.checkStorageRefInitializer env binding checked
      VarBindings.checkStorageRefTupleInitializers env bindingRest itemRest
  | binding :: _, L00_SourceSolidity.TupleItem.hole :: _ => do
      if VarBinding.isStorageRef env.types binding then
        Except.error (TypeError.invalidDataLocation
          (binding.ty.getD (L00_SourceSolidity.Ty.tuple []))
          binding.location)
      else
        Except.error (TypeError.unsupported "tuple hole in value position")
  | actual, expected =>
      Except.error
        (TypeError.arityMismatch
          "tuple expression" expected.length actual.length)

def VarBindings.tys (env : CheckEnv) :
    List L00_SourceSolidity.VarBinding -> Except TypeError (List Ty)
  | [] => Except.ok []
  | binding :: rest => do
      let ty ← VarBinding.checkType env binding
      let tail ← VarBindings.tys env rest
      Except.ok (ty :: tail)

def Parameter.isStringMemory (param : L00_SourceSolidity.Parameter) : Bool :=
  param.ty == L00_SourceSolidity.Ty.string &&
    param.location == some L00_SourceSolidity.DataLocation.memory

def Parameter.isBytesMemory (param : L00_SourceSolidity.Parameter) : Bool :=
  param.ty == L00_SourceSolidity.Ty.bytes &&
    param.location == some L00_SourceSolidity.DataLocation.memory

def Parameter.isBytesCalldata (param : L00_SourceSolidity.Parameter) : Bool :=
  param.ty == L00_SourceSolidity.Ty.bytes &&
    param.location == some L00_SourceSolidity.DataLocation.calldata

def Parameter.isPanicCode (param : L00_SourceSolidity.Parameter) : Bool :=
  param.ty == L00_SourceSolidity.Ty.uint 256 && param.location.isNone

def checkCatchClauseHeader (env : CheckEnv)
    (name? : Option Name) (params : List L00_SourceSolidity.Parameter) :
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
    L00_SourceSolidity.CatchClause -> Option CatchKind
  | L00_SourceSolidity.CatchClause.clause (some "Error") _ _ =>
      some CatchKind.error
  | L00_SourceSolidity.CatchClause.clause (some "Panic") _ _ =>
      some CatchKind.panic
  | L00_SourceSolidity.CatchClause.clause none _ _ =>
      some CatchKind.lowLevel
  | _ => none

def checkCatchClauseKindsUniqueFrom (seen : List CatchKind) :
    List L00_SourceSolidity.CatchClause -> Except TypeError Unit
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
    List L00_SourceSolidity.CatchClause -> Except TypeError Unit :=
  checkCatchClauseKindsUniqueFrom []

structure CheckedStmt where
  source : L00_SourceSolidity.Stmt
  deriving Repr

mutual

def checkStmt (env : CheckEnv) :
    L00_SourceSolidity.Stmt -> Except TypeError CheckedStmt
  | stmt@L00_SourceSolidity.Stmt.empty => Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.block body) => do
      let _ ← checkStmtSeq env body
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.varDecl bindings init?) => do
      let named ← VarBindings.namedTypes env bindings
      ensureUniqueNames "local" (named.map Prod.fst)
      match init? with
      | none =>
          require (!VarBindings.anyStorageRef env.types bindings)
            (TypeError.unsupported
              "storage reference local requires an initializer")
      | some init =>
          match bindings with
          | [binding] =>
              let ty ← VarBinding.checkType env binding
              match checkInternalFunctionValueAssignable? env init ty with
              | some result => result
              | none => do
                  let checked ← checkExpr env init
                  checked.expectAssignableToIn env.types ty
                  VarBinding.checkStorageRefInitializer env binding checked
          | _ =>
              match init with
              | L00_SourceSolidity.Expr.tuple items => do
                  let expected ← VarBindings.tys env bindings
                  checkTupleItemValuesAssignableTo env items expected
                  VarBindings.checkStorageRefTupleInitializers env bindings
                    items
              | _ =>
                  require (!VarBindings.anyStorageRef env.types bindings)
                    (TypeError.unsupported
                      "storage reference tuple return binding")
                  let expected ← VarBindings.tys env bindings
                  let checked ← checkExpr env init
                  checked.expectAssignableToTys env.types expected
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.expr
      (L00_SourceSolidity.Expr.call
        (L00_SourceSolidity.Expr.ident "require")
        [ L00_SourceSolidity.Arg.positional cond
        , L00_SourceSolidity.Arg.positional
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident errorName) errorArgs) ])) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let checkedArgs ← checkArgs env errorArgs
      let argInfos := checkedArgInfosFull errorArgs checkedArgs
      match ErrorSigs.resolveChecked env.types env.errors errorName argInfos with
      | Except.ok _ => Except.ok { source := stmt }
      | Except.error err =>
          if env.errors.any (fun sig => sig.name == errorName) then
            Except.error err
          else
            let _ ← checkExpr env
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "require")
                [ L00_SourceSolidity.Arg.positional cond
                , L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.ident errorName)
                      errorArgs) ])
            Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.expr expr) => do
      let _ ← checkExpr env expr
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.ifElse cond thenBranch elseBranch?) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let _ ← checkStmt env thenBranch
      match elseBranch? with
      | some elseBranch => let _ ← checkStmt env elseBranch; Except.ok ()
      | none => Except.ok ()
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.whileLoop cond body) => do
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      let _ ← checkStmt env.enterLoop body
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.doWhile body cond) => do
      let _ ← checkStmt env.enterLoop body
      let condChecked ← checkExpr env cond
      condChecked.expectBool
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.forLoop init? cond? post? body) => do
      let loopEnv ←
        match init? with
        | none => Except.ok env
        | some initStmt =>
            match initStmt with
            | L00_SourceSolidity.Stmt.varDecl bindings _ => do
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
  | stmt@(L00_SourceSolidity.Stmt.tryCatch expr clauses) => do
      let _ ← checkTryTarget env expr
      checkCatchClauseKindsUnique clauses
      let _ ← checkCatchClauses env clauses
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.tryCatchReturns expr returns success clauses) => do
      Parameters.check env.types returns
      let checked ← checkTryTarget env expr
      checked.expectAssignableToTys env.types (Parameters.tys returns)
      let successEnv :=
        (env.extendVarsWithStorageRefs
        (Parameters.namedTypeStorageRefs env.types returns)).extendDataLocations
          (Parameters.namedDataLocations env.types returns)
      let _ ← checkStmt successEnv success
      checkCatchClauseKindsUnique clauses
      let _ ← checkCatchClauses env clauses
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.emitEvent expr) => do
      requireLogOrCreateAllowed env
        "event emission in view or pure function"
      checkEventEmission env expr
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.revertCall expr) => do
      checkRevertCall env expr
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.returnValues expr?) => do
      checkReturnExprs env expr?
      Except.ok { source := stmt }
  | stmt@L00_SourceSolidity.Stmt.break => do
      require (env.loopDepth > 0) TypeError.breakOutsideLoop
      Except.ok { source := stmt }
  | stmt@L00_SourceSolidity.Stmt.continue => do
      require (env.loopDepth > 0) TypeError.continueOutsideLoop
      Except.ok { source := stmt }
  | stmt@(L00_SourceSolidity.Stmt.unchecked body) => do
      require (!env.inUnchecked) (TypeError.unsupported
        "nested unchecked block")
      let _ ← checkStmt env.enterUnchecked body
      Except.ok { source := stmt }
  | L00_SourceSolidity.Stmt.inlineAssembly _ =>
      Except.error (TypeError.unsupported "inline assembly")
  | stmt@L00_SourceSolidity.Stmt.modifierPlaceholder => do
      require env.inModifier TypeError.modifierPlaceholderOutsideModifier
      require (!env.inUnchecked) (TypeError.unsupported
        "modifier placeholder in unchecked block")
      Except.ok { source := stmt }

def checkStmtSeq (env : CheckEnv) :
    List L00_SourceSolidity.Stmt -> Except TypeError CheckEnv
  | [] => Except.ok env
  | stmt :: rest => do
      let _ ← checkStmt env stmt
      let nextEnv ←
        match stmt with
        | L00_SourceSolidity.Stmt.varDecl bindings _ => do
            let named ← VarBindings.namedTypeStorageRefs env bindings
            let dataLocations ← VarBindings.namedDataLocations env bindings
            Except.ok
              ((env.extendVarsWithStorageRefs named).extendDataLocations
                dataLocations)
        | _ => Except.ok env
      checkStmtSeq nextEnv rest

def checkCatchClause (env : CheckEnv) :
    L00_SourceSolidity.CatchClause -> Except TypeError Unit
  | L00_SourceSolidity.CatchClause.clause name? params body => do
      checkCatchClauseHeader env name? params
      let clauseEnv :=
        (env.extendVarsWithStorageRefs
          (Parameters.namedTypeStorageRefs env.types params)).extendDataLocations
          (Parameters.namedDataLocations env.types params)
      let _ ← checkStmt clauseEnv body
      Except.ok ()

def checkCatchClauses (env : CheckEnv) :
    List L00_SourceSolidity.CatchClause -> Except TypeError Unit
  | [] => Except.ok ()
  | clause :: rest => do
      checkCatchClause env clause
      checkCatchClauses env rest

end

def StateVarDecl.check (env : CheckEnv)
    (decl : L00_SourceSolidity.StateVarDecl) : Except TypeError Unit := do
  checkTy env.types decl.ty
  require (!(decl.visibility == some L00_SourceSolidity.Visibility.external_))
    (TypeError.invalidVariableDecl "state variable is external")
  if decl.visibility == some L00_SourceSolidity.Visibility.public_ then
    let getterShape ←
      match Ty.publicGetterShape? env.types 64 decl.ty with
      | some shape => Except.ok shape
      | none => Except.error (TypeError.invalidType decl.ty)
    match Tys.firstNonAbiEncodable? env.types getterShape.fst with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Tys.firstNonAbiEncodable? env.types getterShape.snd with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
  else
    Except.ok ()
  if decl.mutability == L00_SourceSolidity.VarMutability.constant then
    require (env.types.isConstantStateVarTypeShape decl.ty)
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
  else if decl.mutability == L00_SourceSolidity.VarMutability.immutable then
    require (env.types.isImmutableStateVarTypeShape decl.ty)
      (TypeError.invalidVariableDecl
        "immutable variable has unsupported type")
  else if decl.mutability == L00_SourceSolidity.VarMutability.transient then
    require (env.types.isValueTypeShape decl.ty)
      (TypeError.invalidVariableDecl
        "transient variable has unsupported type")
    require decl.init.isNone
      (TypeError.invalidVariableDecl
        "transient variable has an initializer")
  else
    Except.ok ()
  match decl.init with
  | none => Except.ok ()
  | some init => checkExprAssignableTo env init decl.ty

def StateVarDecl.checkFileLevelConstant (env : CheckEnv)
    (decl : L00_SourceSolidity.StateVarDecl) : Except TypeError Unit := do
  require (decl.mutability == L00_SourceSolidity.VarMutability.constant)
    (TypeError.invalidVariableDecl
      "only constant variables are allowed at file level")
  require decl.visibility.isNone
    (TypeError.invalidVariableDecl
      "file-level constant has visibility")
  require decl.override?.isNone
    (TypeError.invalidVariableDecl
      "file-level constant has override")
  StateVarDecl.check env decl

def StateVarDecl.namedType (decl : L00_SourceSolidity.StateVarDecl) :
    Name × Ty :=
  (decl.name, decl.ty)

def StateVarDecl.namedConstness (decl : L00_SourceSolidity.StateVarDecl) :
    Name × Bool :=
  (decl.name, decl.mutability == L00_SourceSolidity.VarMutability.constant)

def StateVarDecl.isRuntimeStateRead
    (decl : L00_SourceSolidity.StateVarDecl) : Bool :=
  decl.mutability == L00_SourceSolidity.VarMutability.mutable ||
    decl.mutability == L00_SourceSolidity.VarMutability.transient

def StateVarDecl.immutableName? (decl : L00_SourceSolidity.StateVarDecl) :
    Option Name :=
  if decl.mutability == L00_SourceSolidity.VarMutability.immutable then
    some decl.name
  else
    none

def StateVarDecl.runtimeStateName? (decl : L00_SourceSolidity.StateVarDecl) :
    Option Name :=
  if StateVarDecl.isRuntimeStateRead decl then some decl.name else none

def StateVarDecls.namedTypes :
    List L00_SourceSolidity.StateVarDecl -> List (Name × Ty)
  | [] => []
  | decl :: rest => StateVarDecl.namedType decl :: StateVarDecls.namedTypes rest

def StateVarDecls.namedConstness :
    List L00_SourceSolidity.StateVarDecl -> List (Name × Bool)
  | [] => []
  | decl :: rest =>
      StateVarDecl.namedConstness decl :: StateVarDecls.namedConstness rest

def StateVarDecls.runtimeStateNames :
    List L00_SourceSolidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.runtimeStateName? decl with
      | some name => name :: StateVarDecls.runtimeStateNames rest
      | none => StateVarDecls.runtimeStateNames rest

def StateVarDecls.immutableNames :
    List L00_SourceSolidity.StateVarDecl -> List Name
  | [] => []
  | decl :: rest =>
      match StateVarDecl.immutableName? decl with
      | some name => name :: StateVarDecls.immutableNames rest
      | none => StateVarDecls.immutableNames rest

def StateVarDecl.visibleToDerived
    (decl : L00_SourceSolidity.StateVarDecl) : Bool :=
  !(decl.visibility == some L00_SourceSolidity.Visibility.private_)

def ContractItem.visibleStateVarName? :
    L00_SourceSolidity.ContractItem -> Option Name
  | L00_SourceSolidity.ContractItem.stateVar decl =>
      if StateVarDecl.visibleToDerived decl then some decl.name else none
  | _ => none

def ContractItem.visibleStateVar? :
    L00_SourceSolidity.ContractItem ->
    Option L00_SourceSolidity.StateVarDecl
  | L00_SourceSolidity.ContractItem.stateVar decl =>
      if StateVarDecl.visibleToDerived decl then some decl else none
  | _ => none

def ContractDecl.visibleStateVarNames
    (decl : L00_SourceSolidity.ContractDecl) : List Name :=
  decl.items.filterMap ContractItem.visibleStateVarName?

def ContractDecl.visibleStateVars
    (decl : L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.StateVarDecl :=
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
    List Path -> List L00_SourceSolidity.StateVarDecl
  | [] => []
  | path :: rest =>
      match types.lookupContractDecl? path with
      | some decl =>
          ContractDecl.visibleStateVars decl ++
            ContractDecls.visibleStateVars types rest
      | none => ContractDecls.visibleStateVars types rest

def StateVarDecls.checkNoInheritedShadowing
    (inheritedNames : List Name) :
    List L00_SourceSolidity.StateVarDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | decl :: rest => do
      require
        (!L00_SourceSolidity.Executable.nameIn decl.name inheritedNames)
        (TypeError.invalidContractHeader
          "state variable shadows inherited state variable")
      StateVarDecls.checkNoInheritedShadowing inheritedNames rest

structure OverrideMember where
  origin : Path
  originKind : L00_SourceSolidity.ContractKind
  fromStateVar : Bool := false
  name : Name
  params : List Ty := []
  returns : List Ty := []
  visibility : Option L00_SourceSolidity.Visibility := none
  mutability : L00_SourceSolidity.StateMutability :=
    L00_SourceSolidity.StateMutability.nonpayable
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
    (base actual : Option L00_SourceSolidity.Visibility) : Bool :=
  if base == actual then
    true
  else
    base == some L00_SourceSolidity.Visibility.external_ &&
      actual == some L00_SourceSolidity.Visibility.public_

def overrideMutabilityAllowed
    (base actual : L00_SourceSolidity.StateMutability) : Bool :=
  match base with
  | L00_SourceSolidity.StateMutability.pure =>
      actual == L00_SourceSolidity.StateMutability.pure
  | L00_SourceSolidity.StateMutability.view =>
      actual == L00_SourceSolidity.StateMutability.view ||
        actual == L00_SourceSolidity.StateMutability.pure
  | L00_SourceSolidity.StateMutability.nonpayable =>
      actual == L00_SourceSolidity.StateMutability.nonpayable ||
        actual == L00_SourceSolidity.StateMutability.view ||
        actual == L00_SourceSolidity.StateMutability.pure
  | L00_SourceSolidity.StateMutability.payable =>
      actual == L00_SourceSolidity.StateMutability.payable

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

def StateVarDecl.publicGetterOverrideMember? (types : TypeContext)
    (origin : Path) (originKind : L00_SourceSolidity.ContractKind)
    (decl : L00_SourceSolidity.StateVarDecl) : Option OverrideMember :=
  match decl.visibility with
  | some L00_SourceSolidity.Visibility.public_ => do
      let shape ← Ty.publicGetterShape? types 64 decl.ty
      some
        { origin := origin
          originKind := originKind
          fromStateVar := true
          name := decl.name
          params := shape.fst
          returns := shape.snd
          visibility := some L00_SourceSolidity.Visibility.external_
          mutability := L00_SourceSolidity.StateMutability.view
          virtual := false
          implemented := true }
  | _ => none

def receiveOverrideName : Name := "#receive"

def fallbackOverrideName : Name := "#fallback"

def FunctionDecl.overrideMember? (origin : Path)
    (originKind : L00_SourceSolidity.ContractKind)
    (fn : L00_SourceSolidity.FunctionDecl) : Option OverrideMember :=
  match fn.kind, fn.name, fn.visibility with
  | L00_SourceSolidity.FunctionKind.function, some _,
      some L00_SourceSolidity.Visibility.private_ => none
  | L00_SourceSolidity.FunctionKind.function, some name, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := name
          params := Parameters.tys fn.params
          returns := Parameters.tys fn.returns
          visibility := visibility
          mutability := fn.mutability
          virtual :=
            fn.virtual ||
              originKind == L00_SourceSolidity.ContractKind.interface
          implemented := fn.body.isSome }
  | L00_SourceSolidity.FunctionKind.receive, _, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := receiveOverrideName
          params := []
          returns := []
          visibility := visibility
          mutability := fn.mutability
          virtual := fn.virtual
          implemented := fn.body.isSome }
  | L00_SourceSolidity.FunctionKind.fallback, _, visibility =>
      some
        { origin := origin
          originKind := originKind
          fromStateVar := false
          name := fallbackOverrideName
          params := []
          returns := []
          visibility := visibility
          mutability := fn.mutability
          virtual := fn.virtual
          implemented := fn.body.isSome }
  | _, _, _ => none

def ContractItem.overrideMember? (types : TypeContext)
    (origin : Path) (originKind : L00_SourceSolidity.ContractKind) :
    L00_SourceSolidity.ContractItem -> Option OverrideMember
  | L00_SourceSolidity.ContractItem.function fn =>
      FunctionDecl.overrideMember? origin originKind fn
  | L00_SourceSolidity.ContractItem.stateVar decl =>
      StateVarDecl.publicGetterOverrideMember? types origin originKind decl
  | _ => none

def ContractDecl.overrideMembers (types : TypeContext)
    (decl : L00_SourceSolidity.ContractDecl) : List OverrideMember :=
  let origin := TypeContext.pathOfName decl.name
  decl.items.filterMap (ContractItem.overrideMember? types origin decl.kind)

def ContractDecls.lookupPath? (target : Path) :
    List L00_SourceSolidity.ContractDecl ->
    Option L00_SourceSolidity.ContractDecl
  | [] => none
  | decl :: rest =>
      if TypeContext.pathMatches target (TypeContext.pathOfName decl.name) then
        some decl
      else
        ContractDecls.lookupPath? target rest

def OverrideMembers.collectMostDerivedFrom (types : TypeContext)
    (members : List OverrideMember) :
    List L00_SourceSolidity.ContractDecl -> List OverrideMember
  | [] => members
  | decl :: rest =>
      OverrideMembers.collectMostDerivedFrom types
        (OverrideMembers.addAllIfNewKey members
          (ContractDecl.overrideMembers types decl))
        rest

def OverrideMembers.collectMostDerived (types : TypeContext)
    (order : List L00_SourceSolidity.ContractDecl) :
    List OverrideMember :=
  OverrideMembers.collectMostDerivedFrom types [] order

def BaseSpecifier.frontierOverrideMembers? (types : TypeContext)
    (contracts : List L00_SourceSolidity.ContractDecl)
    (specifier : L00_SourceSolidity.BaseSpecifier) :
    Option (List OverrideMember) := do
  let base ← ContractDecls.lookupPath? specifier.base contracts
  let order ←
    L00_SourceSolidity.Executable.ContractDecl.dispatchOrder? contracts base
  some (OverrideMembers.collectMostDerived types order)

def BaseSpecifiers.frontierOverrideMembers? (types : TypeContext)
    (contracts : List L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.BaseSpecifier -> Option (List OverrideMember)
  | [] => some []
  | specifier :: rest => do
      let head ← BaseSpecifier.frontierOverrideMembers? types contracts specifier
      let tail ← BaseSpecifiers.frontierOverrideMembers? types contracts rest
      some (head ++ tail)

def ContractDecl.inheritedOverrideMembers? (types : TypeContext)
    (contracts : List L00_SourceSolidity.ContractDecl)
    (decl : L00_SourceSolidity.ContractDecl) :
    Option (List OverrideMember) := do
  let members ← BaseSpecifiers.frontierOverrideMembers? types contracts decl.bases
  some (OverrideMembers.dedupOriginKeys members)

def ContractDecl.ancestorPaths? (contracts : List L00_SourceSolidity.ContractDecl)
    (decl : L00_SourceSolidity.ContractDecl) : Option (List Path) := do
  let order ←
    L00_SourceSolidity.Executable.ContractDecl.dispatchOrder? contracts decl
  some ((List.drop 1 order).map (fun base => TypeContext.pathOfName base.name))

def singleImplicitInterfaceOverride : List OverrideMember -> Bool
  | [member] => member.originKind == L00_SourceSolidity.ContractKind.interface
  | _ => false

def checkOverrideSpecifier (ancestorPaths : List Path)
    (baseMatches : List OverrideMember)
    (specifier : L00_SourceSolidity.OverrideSpecifier) :
    Except TypeError Unit := do
  require (pathAllIn specifier.bases ancestorPaths)
    (TypeError.invalidOverride "override specifier names a non-base contract")
  if specifier.bases.isEmpty then
    require (baseMatches.length <= 1)
      (TypeError.invalidOverride "multiple base overrides require base list")
  else
    require
      (pathSetsEqual specifier.bases
        (OverrideMembers.originPaths baseMatches))
      (TypeError.invalidOverride "override base list does not match bases")

def checkOverrideUse (ancestorPaths : List Path)
    (override? : Option L00_SourceSolidity.OverrideSpecifier)
    (baseMatches : List OverrideMember) : Except TypeError Unit :=
  match override? with
  | none =>
      require (singleImplicitInterfaceOverride baseMatches)
        (TypeError.invalidOverride "missing override specifier")
  | some specifier =>
      checkOverrideSpecifier ancestorPaths baseMatches specifier

def FunctionDecl.checkOverrideRules (currentPath : Path)
    (currentKind : L00_SourceSolidity.ContractKind)
    (ancestorPaths : List Path) (inherited : List OverrideMember)
    (fn : L00_SourceSolidity.FunctionDecl) :
    Except TypeError Unit :=
  match FunctionDecl.overrideMember? currentPath currentKind fn with
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
          checkOverrideUse ancestorPaths fn.override? baseMatches

def StateVarDecl.checkOverrideRules (types : TypeContext)
    (currentPath : Path) (currentKind : L00_SourceSolidity.ContractKind)
    (ancestorPaths : List Path) (inherited : List OverrideMember)
    (decl : L00_SourceSolidity.StateVarDecl) :
    Except TypeError Unit :=
  match StateVarDecl.publicGetterOverrideMember? types currentPath
      currentKind decl with
  | none =>
      require decl.override?.isNone
        (TypeError.invalidOverride "override on non-public state variable")
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
    (members : List OverrideMember) : Bool :=
  (matchingKey target members).length > 1

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
    (current : List OverrideMember)
    (members : List OverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if hasConflictFor member members &&
          !hasCurrentOverrideFor member current then
        Except.error
          (TypeError.invalidOverride
            "multiple inherited base members require an override")
      else
        checkInheritedConflicts current rest

def OverrideMembers.checkInheritedAbstractImplemented
    (contractIsAbstract : Bool) (current : List OverrideMember)
    (members : List OverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if !contractIsAbstract && !member.implemented &&
          !hasImplementedCurrentFor member current then
        Except.error
          (TypeError.invalidContractHeader
            "non-abstract contract inherits unimplemented function")
      else
        checkInheritedAbstractImplemented contractIsAbstract current rest

structure ModifierOverrideMember where
  origin : Path
  originKind : L00_SourceSolidity.ContractKind
  name : Name
  params : List Ty := []
  virtual : Bool := false
  implemented : Bool := true
  deriving Repr

def ModifierDecl.overrideMember (origin : Path)
    (originKind : L00_SourceSolidity.ContractKind)
    (modifier : L00_SourceSolidity.ModifierDecl) : ModifierOverrideMember :=
  { origin := origin
    originKind := originKind
    name := modifier.name
    params := Parameters.tys modifier.params
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
      checkCompatible current rest

def itemMember? (origin : Path)
    (originKind : L00_SourceSolidity.ContractKind) :
    L00_SourceSolidity.ContractItem -> Option ModifierOverrideMember
  | L00_SourceSolidity.ContractItem.modifierDecl modifier =>
      some (ModifierDecl.overrideMember origin originKind modifier)
  | _ => none

def forContract (decl : L00_SourceSolidity.ContractDecl) :
    List ModifierOverrideMember :=
  let origin := TypeContext.pathOfName decl.name
  decl.items.filterMap (itemMember? origin decl.kind)

def collectMostDerivedFrom (members : List ModifierOverrideMember) :
    List L00_SourceSolidity.ContractDecl -> List ModifierOverrideMember
  | [] => members
  | decl :: rest =>
      collectMostDerivedFrom
        (addAllIfNewName members (forContract decl)) rest

def collectMostDerived (order : List L00_SourceSolidity.ContractDecl) :
    List ModifierOverrideMember :=
  collectMostDerivedFrom [] order

def hasConflictFor (target : ModifierOverrideMember)
    (members : List ModifierOverrideMember) : Bool :=
  (matchingName target members).length > 1

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

def checkInheritedConflicts (current : List ModifierOverrideMember)
    (members : List ModifierOverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if hasConflictFor member members &&
          !hasCurrentOverrideFor member current then
        Except.error
          (TypeError.invalidOverride
            "multiple inherited modifiers require an override")
      else
        checkInheritedConflicts current rest

def checkInheritedAbstractImplemented
    (contractIsAbstract : Bool) (current : List ModifierOverrideMember)
    (members : List ModifierOverrideMember) : Except TypeError Unit :=
  match members with
  | [] => Except.ok ()
  | member :: rest => do
      if !contractIsAbstract && !member.implemented &&
          !hasImplementedCurrentFor member current then
        Except.error
          (TypeError.invalidContractHeader
            "non-abstract contract inherits unimplemented modifier")
      else
        checkInheritedAbstractImplemented contractIsAbstract current rest

end ModifierOverrideMembers

def BaseSpecifier.frontierModifierMembers?
    (contracts : List L00_SourceSolidity.ContractDecl)
    (specifier : L00_SourceSolidity.BaseSpecifier) :
    Option (List ModifierOverrideMember) := do
  let base ← ContractDecls.lookupPath? specifier.base contracts
  let order ←
    L00_SourceSolidity.Executable.ContractDecl.dispatchOrder? contracts base
  some (ModifierOverrideMembers.collectMostDerived order)

def BaseSpecifiers.frontierModifierMembers?
    (contracts : List L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.BaseSpecifier ->
    Option (List ModifierOverrideMember)
  | [] => some []
  | specifier :: rest => do
      let head ← BaseSpecifier.frontierModifierMembers? contracts specifier
      let tail ← BaseSpecifiers.frontierModifierMembers? contracts rest
      some (head ++ tail)

def ContractDecl.inheritedModifierMembers?
    (contracts : List L00_SourceSolidity.ContractDecl)
    (decl : L00_SourceSolidity.ContractDecl) :
    Option (List ModifierOverrideMember) := do
  let members ← BaseSpecifiers.frontierModifierMembers? contracts decl.bases
  some (ModifierOverrideMembers.dedupOriginNames members)

def checkModifierOverrideUse (ancestorPaths : List Path)
    (override? : Option L00_SourceSolidity.OverrideSpecifier)
    (baseMatches : List ModifierOverrideMember) : Except TypeError Unit :=
  match override? with
  | none =>
      require false
        (TypeError.invalidOverride "missing modifier override specifier")
  | some specifier => do
      require (pathAllIn specifier.bases ancestorPaths)
        (TypeError.invalidOverride
          "modifier override specifier names a non-base contract")
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
    (currentKind : L00_SourceSolidity.ContractKind)
    (ancestorPaths : List Path)
    (inherited : List ModifierOverrideMember)
    (modifier : L00_SourceSolidity.ModifierDecl) :
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
      checkModifierOverrideUse ancestorPaths modifier.override? baseMatches

def FunctionDecl.externallyVisible
    (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  match fn.visibility with
  | some L00_SourceSolidity.Visibility.public_ => true
  | some L00_SourceSolidity.Visibility.external_ => true
  | _ => false

def FunctionDecl.checkHeader (env : CheckEnv)
    (fn : L00_SourceSolidity.FunctionDecl) : Except TypeError Unit := do
  match env.contractKind, fn.kind with
  | none, L00_SourceSolidity.FunctionKind.function =>
      require fn.name.isSome
        (TypeError.invalidFunctionHeader "free function missing name")
      require fn.visibility.isNone
        (TypeError.invalidFunctionHeader "free function has visibility")
      require (!(fn.mutability == L00_SourceSolidity.StateMutability.payable))
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
  | some _, L00_SourceSolidity.FunctionKind.function =>
      require fn.name.isSome
        (TypeError.invalidFunctionHeader "function missing name")
      require fn.visibility.isSome
        (TypeError.invalidFunctionHeader "contract function missing visibility")
  | some _, L00_SourceSolidity.FunctionKind.constructor =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "constructor has a name")
      require fn.visibility.isNone
        (TypeError.invalidFunctionHeader "constructor has visibility")
      require (!fn.virtual)
        (TypeError.invalidFunctionHeader "constructor is virtual")
      require fn.override?.isNone
        (TypeError.invalidFunctionHeader "constructor has override")
      require fn.returns.isEmpty
        (TypeError.invalidFunctionHeader "constructor has returns")
      require fn.body.isSome
        (TypeError.invalidFunctionHeader "constructor has no implementation")
      require (!Parameters.anyCalldata fn.params)
        (TypeError.invalidFunctionHeader
          "constructor parameter uses calldata")
      require (!Parameters.anyStorageRef env.types fn.params)
        (TypeError.invalidFunctionHeader
          "constructor parameter uses storage")
  | some _, L00_SourceSolidity.FunctionKind.receive =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "receive function has a name")
      require fn.params.isEmpty
        (TypeError.invalidFunctionHeader "receive function has parameters")
      require fn.returns.isEmpty
        (TypeError.invalidFunctionHeader "receive function has returns")
      require
        (fn.visibility == some L00_SourceSolidity.Visibility.external_)
        (TypeError.invalidFunctionHeader
          "receive function is not external")
      require
        (fn.mutability == L00_SourceSolidity.StateMutability.payable)
        (TypeError.invalidFunctionHeader
          "receive function is not payable")
  | some _, L00_SourceSolidity.FunctionKind.fallback =>
      require fn.name.isNone
        (TypeError.invalidFunctionHeader "fallback function has a name")
      require
        (fn.visibility == some L00_SourceSolidity.Visibility.external_)
        (TypeError.invalidFunctionHeader
          "fallback function is not external")
      require
        (fn.mutability == L00_SourceSolidity.StateMutability.nonpayable ||
          fn.mutability == L00_SourceSolidity.StateMutability.payable)
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
    (!(fn.visibility == some L00_SourceSolidity.Visibility.private_) ||
      !fn.virtual)
    (TypeError.invalidFunctionHeader "private function is virtual")
  if env.inLibrary && fn.kind == L00_SourceSolidity.FunctionKind.function then
    require (!(fn.mutability == L00_SourceSolidity.StateMutability.payable))
      (TypeError.invalidFunctionHeader "library function is payable")
  else
    Except.ok ()
  if env.contractKind == some L00_SourceSolidity.ContractKind.interface then
    Except.ok ()
  else if !(fn.kind == L00_SourceSolidity.FunctionKind.constructor) &&
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
    match Parameters.firstMappingContainingTy? env.types fn.returns with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
    match Parameters.firstNonAbiEncodableTy? env.types fn.returns with
    | some ty => Except.error (TypeError.invalidAbiType ty)
    | none => Except.ok ()
  else
    Except.ok ()

def ModifierInvocation.targetName
    (invocation : L00_SourceSolidity.ModifierInvocation) :
    Except TypeError Name := do
  let name ←
    match L00_SourceSolidity.Executable.pathLast? invocation.target with
    | some name => Except.ok name
    | none =>
        Except.error
          (TypeError.invalidFunctionHeader "empty modifier invocation")
  Except.ok name

def ModifierInvocation.baseConstructorPath?
    (env : CheckEnv)
    (invocation : L00_SourceSolidity.ModifierInvocation) :
    Option Path := do
  let name ← L00_SourceSolidity.Executable.pathLast? invocation.target
  let path := TypeContext.pathOfName name
  if TypeContext.pathIn path env.ancestorPaths then
    some path
  else
    none

def ModifierInvocation.baseConstructorDecl?
    (env : CheckEnv)
    (invocation : L00_SourceSolidity.ModifierInvocation) :
    Option L00_SourceSolidity.ContractDecl := do
  let path ← ModifierInvocation.baseConstructorPath? env invocation
  env.types.lookupContractDecl? path

def ModifierInvocation.checkBaseConstructor (env : CheckEnv)
    (invocation : L00_SourceSolidity.ModifierInvocation)
    (baseDecl : L00_SourceSolidity.ContractDecl) :
    Except TypeError Unit := do
  let checkedArgs ← checkArgs env invocation.args
  checkCheckedArgsAssignableToFunctionSig env.types
    ("base constructor " ++ baseDecl.name)
    (ContractDecl.constructorSignature baseDecl) invocation.args checkedArgs

def ModifierInvocation.check (env : CheckEnv) (allowBaseConstructors : Bool)
    (invocation : L00_SourceSolidity.ModifierInvocation) :
    Except TypeError Unit := do
  match ModifierInvocation.baseConstructorDecl? env invocation with
  | some baseDecl =>
      require allowBaseConstructors
        (TypeError.invalidFunctionHeader
          "base constructor invocation outside constructor")
      ModifierInvocation.checkBaseConstructor env invocation baseDecl
  | none =>
      let name ← ModifierInvocation.targetName invocation
      let checkedArgs ← checkArgs env invocation.args
      let argInfos := checkedArgInfosFull invocation.args checkedArgs
      let _ ← ModifierSigs.resolveChecked env.types env.modifiers name argInfos
      Except.ok ()

def ModifierInvocation.checkBodyForCaller (env : CheckEnv)
    (invocation : L00_SourceSolidity.ModifierInvocation) :
    Except TypeError Unit := do
  match ModifierInvocation.baseConstructorDecl? env invocation with
  | some _ => Except.ok ()
  | none => do
      let name ← ModifierInvocation.targetName invocation
      let modifier ←
        match env.lookupModifierDecl? name with
        | some modifier => Except.ok modifier
        | none => Except.error (TypeError.unknownFunction name)
      match modifier.body with
      | none => Except.ok ()
      | some body =>
          let locals := Parameters.namedTypeStorageRefs env.types modifier.params
          let dataLocations :=
            Parameters.namedDataLocations env.types modifier.params
          let modifierEnv :=
            { env.enterModifier with
              vars := locals.map (fun entry => (entry.1, entry.2.1)) ++ env.vars
              localNames := locals.map Prod.fst ++ env.localNames
              localStorageRefs :=
                (locals.filterMap
                  (fun entry =>
                    if entry.2.2 then some entry.1 else none)) ++
                  env.localStorageRefs
              localDataLocations := dataLocations ++ env.localDataLocations
              returnTys := [] }
          let _ ← checkStmt modifierEnv body
          Except.ok ()

def ModifierInvocations.checkWithSeen (env : CheckEnv)
    (allowBaseConstructors : Bool) (seenBaseConstructors : List Path) :
    List L00_SourceSolidity.ModifierInvocation -> Except TypeError Unit
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
    List L00_SourceSolidity.ModifierInvocation -> Except TypeError Unit :=
  ModifierInvocations.checkWithSeen env allowBaseConstructors []

def ModifierInvocations.checkBodiesForCaller (env : CheckEnv) :
    List L00_SourceSolidity.ModifierInvocation -> Except TypeError Unit
  | [] => Except.ok ()
  | invocation :: rest => do
      ModifierInvocation.checkBodyForCaller env invocation
      ModifierInvocations.checkBodiesForCaller env rest

def FunctionDecl.check (baseEnv : CheckEnv)
    (fn : L00_SourceSolidity.FunctionDecl) : Except TypeError Unit := do
  FunctionDecl.checkHeader baseEnv fn
  Parameters.check baseEnv.types fn.params
  Parameters.check baseEnv.types fn.returns
  let localNames := (Parameters.namedTypes fn.params).map Prod.fst ++
    (Parameters.namedTypes fn.returns).map Prod.fst
  ensureUniqueNames "function local" localNames
  let locals := Parameters.namedTypeStorageRefs baseEnv.types fn.returns ++
    Parameters.namedTypeStorageRefs baseEnv.types fn.params
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
      returnTys := Parameters.tys fn.returns
      inConstructor := fn.kind == L00_SourceSolidity.FunctionKind.constructor }
  ModifierInvocations.check env
    (fn.kind == L00_SourceSolidity.FunctionKind.constructor)
    fn.modifiers
  match fn.body with
  | none => Except.ok ()
  | some body =>
      ModifierInvocations.checkBodiesForCaller env fn.modifiers
      let _ ← checkStmt env body
      Except.ok ()

def ModifierDecl.check (baseEnv : CheckEnv)
    (modifier : L00_SourceSolidity.ModifierDecl) : Except TypeError Unit := do
  Parameters.check baseEnv.types modifier.params
  match modifier.body with
  | none =>
      require modifier.virtual
        (TypeError.invalidFunctionHeader
          "modifier without implementation is not virtual")
  | some body =>
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
          returnTys := [] }
      let _ ← checkStmt env body
      Except.ok ()

def EventParam.indexedWeight
    (param : L00_SourceSolidity.EventParam) : Nat :=
  if param.indexed then 1 else 0

def EventParams.indexedCount :
    List L00_SourceSolidity.EventParam -> Nat
  | [] => 0
  | param :: rest =>
      EventParam.indexedWeight param + EventParams.indexedCount rest

def EventDecl.indexedLimit
    (event : L00_SourceSolidity.EventDecl) : Nat :=
  if event.anonymous then 4 else 3

def EventParam.check (env : CheckEnv)
    (param : L00_SourceSolidity.EventParam) :
    Except TypeError Unit := do
  checkTy env.types param.ty
  require (TypeContext.isAbiEncodable env.types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (!Ty.containsMapping env.types 64 param.ty)
    (TypeError.invalidAbiType param.ty)

def EventDecl.check (env : CheckEnv)
    (event : L00_SourceSolidity.EventDecl) :
    Except TypeError Unit := do
  require (EventParams.indexedCount event.params <=
      EventDecl.indexedLimit event)
    (TypeError.invalidEventHeader event.name
      "too many indexed event parameters")
  event.params.foldl
    (fun acc param => do
      acc
      EventParam.check env param)
    (Except.ok ())

def Parameter.checkErrorParam (types : TypeContext)
    (param : L00_SourceSolidity.Parameter) : Except TypeError Unit := do
  checkTy types param.ty
  require param.location.isNone
    (TypeError.invalidDataLocation param.ty param.location)
  require (TypeContext.isAbiEncodable types param.ty)
    (TypeError.invalidAbiType param.ty)
  require (!Ty.containsMapping types 64 param.ty)
    (TypeError.invalidAbiType param.ty)

def Parameters.checkErrorParams (types : TypeContext) :
    List L00_SourceSolidity.Parameter -> Except TypeError Unit
  | [] => Except.ok ()
  | param :: rest => do
      Parameter.checkErrorParam types param
      Parameters.checkErrorParams types rest

def ErrorDecl.check (env : CheckEnv)
    (err : L00_SourceSolidity.ErrorDecl) :
    Except TypeError Unit := do
  require (!(err.name == "Error" || err.name == "Panic"))
    (TypeError.invalidErrorHeader err.name
      "built-in error cannot be redefined")
  Parameters.checkErrorParams env.types err.params

def pathInList (target : Path) : List Path -> Bool :=
  TypeContext.pathIn target

mutual

def Ty.hasForbiddenStructSelfReference (targets : List Path) : Ty -> Bool
  | L00_SourceSolidity.Ty.user path => pathInList path targets
  | L00_SourceSolidity.Ty.array element (some _) =>
      Ty.hasForbiddenStructSelfReference targets element
  | L00_SourceSolidity.Ty.tuple tys =>
      Tys.hasForbiddenStructSelfReference targets tys
  | L00_SourceSolidity.Ty.function params returns _ _ =>
      Tys.hasForbiddenStructSelfReference targets params ||
        Tys.hasForbiddenStructSelfReference targets returns
  | _ => false

def Tys.hasForbiddenStructSelfReference (targets : List Path) :
    List Ty -> Bool
  | [] => false
  | ty :: rest =>
      Ty.hasForbiddenStructSelfReference targets ty ||
        Tys.hasForbiddenStructSelfReference targets rest

end

def StructField.check (env : CheckEnv) (selfPaths : List Path)
    (field : L00_SourceSolidity.StructField) : Except TypeError Unit := do
  checkTy env.types field.ty
  require (!Ty.hasForbiddenStructSelfReference selfPaths field.ty)
    (TypeError.invalidType field.ty)

def StructDecl.check (env : CheckEnv) (selfPaths : List Path)
    (decl : L00_SourceSolidity.StructDecl) : Except TypeError Unit := do
  ensureUniqueNames "struct field" (decl.fields.map L00_SourceSolidity.StructField.name)
  let rec checkFields :
      List L00_SourceSolidity.StructField -> Except TypeError Unit
    | [] => Except.ok ()
    | field :: rest => do
        StructField.check env selfPaths field
        checkFields rest
  checkFields decl.fields

def EnumDecl.check (decl : L00_SourceSolidity.EnumDecl) :
    Except TypeError Unit := do
  require (decl.cases.length > 0 && decl.cases.length <= 256)
    (TypeError.invalidEnum decl.name)
  ensureUniqueNames "enum case" decl.cases

def UserValueTypeDecl.check (env : CheckEnv)
    (decl : L00_SourceSolidity.UserValueTypeDecl) :
    Except TypeError Unit := do
  checkTy env.types decl.underlying
  require (Ty.isBuiltInValueTypeShape decl.underlying)
    (TypeError.invalidUserValueType decl.name decl.underlying)

def UsingFunction.check (env : CheckEnv)
    (target? : Option Ty) (global : Bool)
    (binding : L00_SourceSolidity.UsingFunction) : Except TypeError Unit := do
  let (libraryPath, functionName) ←
    match L00_SourceSolidity.Executable.pathInitLast? binding.function with
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
      | L00_SourceSolidity.Ty.user path =>
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
          require (libraryDecl.kind == L00_SourceSolidity.ContractKind.library)
            (TypeError.invalidContractHeader "using target is not a library")
          Except.ok
            ((FunctionSigs.nonPrivate
              (ContractDecl.directFunctionSigs libraryDecl)).filter
                (fun sig => sig.name == functionName))
      require (!candidates.isEmpty) (TypeError.unknownFunction functionName)

def UsingFunctions.check (env : CheckEnv)
    (target? : Option Ty) (global : Bool) :
    List L00_SourceSolidity.UsingFunction -> Except TypeError Unit
  | [] => Except.ok ()
  | binding :: rest => do
      UsingFunction.check env target? global binding
      UsingFunctions.check env target? global rest

def UsingDecl.checkCore (env : CheckEnv)
    (decl : L00_SourceSolidity.UsingDecl) : Except TypeError Unit := do
  if decl.functions.isEmpty then
    let libraryDecl ←
      match env.types.lookupContractDecl? decl.library with
      | some libraryDecl => Except.ok libraryDecl
      | none => Except.error (TypeError.unknownType decl.library)
    require (libraryDecl.kind == L00_SourceSolidity.ContractKind.library)
      (TypeError.invalidContractHeader "using target is not a library")
  else
    UsingFunctions.check env decl.target decl.global decl.functions
  match decl.target with
  | some ty => checkTy env.types ty
  | none => Except.ok ()

def UsingDecl.checkContractLevel (env : CheckEnv)
    (decl : L00_SourceSolidity.UsingDecl) : Except TypeError Unit := do
  UsingDecl.checkCore env decl
  require (!decl.global)
    (TypeError.invalidContractHeader
      "global using directive is only allowed at file scope")

def UsingDecl.checkFileLevel (env : CheckEnv)
    (decl : L00_SourceSolidity.UsingDecl) : Except TypeError Unit := do
  UsingDecl.checkCore env decl
  require decl.target.isSome
    (TypeError.invalidContractHeader
      "file-level using directive requires an explicit type")
  if decl.global then
    match decl.target with
    | some (L00_SourceSolidity.Ty.user path) =>
        require (env.types.isUserValueTypePath path)
          (TypeError.invalidContractHeader
            "global using directive target is not a user value type")
    | _ =>
        Except.error
          (TypeError.invalidContractHeader
            "global using directive target is not a user value type")
  else
    Except.ok ()

def ContractItem.stateVar? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.StateVarDecl
  | L00_SourceSolidity.ContractItem.stateVar decl => some decl
  | _ => none

def ContractItem.function? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.FunctionDecl
  | L00_SourceSolidity.ContractItem.function decl => some decl
  | _ => none

def ContractItem.modifier? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.ModifierDecl
  | L00_SourceSolidity.ContractItem.modifierDecl decl => some decl
  | _ => none

def ContractItem.event? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.EventDecl
  | L00_SourceSolidity.ContractItem.eventDecl decl => some decl
  | _ => none

def ContractItem.error? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.ErrorDecl
  | L00_SourceSolidity.ContractItem.errorDecl decl => some decl
  | _ => none

def ContractItem.struct? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.StructDecl
  | L00_SourceSolidity.ContractItem.structDecl decl => some decl
  | _ => none

def ContractItem.enum? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.EnumDecl
  | L00_SourceSolidity.ContractItem.enumDecl decl => some decl
  | _ => none

def ContractItem.userValueType? :
    L00_SourceSolidity.ContractItem ->
    Option L00_SourceSolidity.UserValueTypeDecl
  | L00_SourceSolidity.ContractItem.userValueTypeDecl decl => some decl
  | _ => none

def ContractItem.using? :
    L00_SourceSolidity.ContractItem -> Option L00_SourceSolidity.UsingDecl
  | L00_SourceSolidity.ContractItem.usingDecl decl => some decl
  | _ => none

def StateVarDecl.isConstant (decl : L00_SourceSolidity.StateVarDecl) : Bool :=
  decl.mutability == L00_SourceSolidity.VarMutability.constant

def FunctionDecl.hasBody (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  match fn.body with
  | some _ => true
  | none => false

def FunctionDecl.isOrdinary (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  fn.kind == L00_SourceSolidity.FunctionKind.function

def FunctionDecl.declaredName? (fn : L00_SourceSolidity.FunctionDecl) :
    Option Name :=
  match fn.kind, fn.name with
  | L00_SourceSolidity.FunctionKind.function, some name => some name
  | _, _ => none

def FunctionDecl.isInterfaceDeclaration
    (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  FunctionDecl.isOrdinary fn && !FunctionDecl.hasBody fn &&
    fn.visibility == some L00_SourceSolidity.Visibility.external_

def FunctionDecl.isConstructorLike
    (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  fn.kind == L00_SourceSolidity.FunctionKind.constructor ||
    fn.kind == L00_SourceSolidity.FunctionKind.receive ||
    fn.kind == L00_SourceSolidity.FunctionKind.fallback

def FunctionDecl.requiresImplementation
    (fn : L00_SourceSolidity.FunctionDecl) : Bool :=
  !FunctionDecl.hasBody fn

def ModifierDecl.hasBody (modifier : L00_SourceSolidity.ModifierDecl) : Bool :=
  match modifier.body with
  | some _ => true
  | none => false

def ModifierDecl.requiresImplementation
    (modifier : L00_SourceSolidity.ModifierDecl) : Bool :=
  !ModifierDecl.hasBody modifier

def Functions.anyMissingBody :
    List L00_SourceSolidity.FunctionDecl -> Bool
  | [] => false
  | fn :: rest =>
      FunctionDecl.requiresImplementation fn || Functions.anyMissingBody rest

def Modifiers.anyMissingBody :
    List L00_SourceSolidity.ModifierDecl -> Bool
  | [] => false
  | modifier :: rest =>
      ModifierDecl.requiresImplementation modifier ||
        Modifiers.anyMissingBody rest

def Functions.anyConstructorLike :
    List L00_SourceSolidity.FunctionDecl -> Bool
  | [] => false
  | fn :: rest =>
      FunctionDecl.isConstructorLike fn || Functions.anyConstructorLike rest

def StateVars.allConstant :
    List L00_SourceSolidity.StateVarDecl -> Bool
  | [] => true
  | decl :: rest =>
      StateVarDecl.isConstant decl && StateVars.allConstant rest

def ContractDecl.hasStorageLayoutBase
    (decl : L00_SourceSolidity.ContractDecl) : Bool :=
  decl.layoutBase.isSome

def ContractDecls.anyStorageLayoutBase :
    List L00_SourceSolidity.ContractDecl -> Bool
  | [] => false
  | decl :: rest =>
      ContractDecl.hasStorageLayoutBase decl ||
        ContractDecls.anyStorageLayoutBase rest

def ContractDecl.checkStorageLayoutBase (env : CheckEnv)
    (contract : L00_SourceSolidity.ContractDecl) :
    Except TypeError Unit := do
  match contract.layoutBase with
  | none => Except.ok ()
  | some expr => do
      require (contract.kind == L00_SourceSolidity.ContractKind.contract)
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
        (L00_SourceSolidity.Ty.uint 256)

def BaseSpecifier.check (env : CheckEnv) (sourceTypes : TypeContext)
    (contractKind : L00_SourceSolidity.ContractKind) (contractName : Name)
    (specifier : L00_SourceSolidity.BaseSpecifier) :
    Except TypeError Unit := do
  let baseDecl ←
    match sourceTypes.lookupContractDecl? specifier.base with
    | some decl => Except.ok decl
    | none => Except.error (TypeError.unknownType specifier.base)
  require (!(baseDecl.name == contractName))
    (TypeError.invalidContractHeader "contract inherits itself")
  if contractKind == L00_SourceSolidity.ContractKind.interface then
    require (baseDecl.kind == L00_SourceSolidity.ContractKind.interface)
      (TypeError.invalidContractHeader
        "interface inherits non-interface")
  else
    Except.ok ()
  if baseDecl.kind == L00_SourceSolidity.ContractKind.library then
    Except.error
      (TypeError.invalidContractHeader "contract inherits library")
  else
    Except.ok ()
  if specifier.args.isEmpty then
    Except.ok ()
  else
    require (argsAllCompileTimeConstant env specifier.args)
      (TypeError.invalidContractHeader
        "base constructor argument is not compile-time constant")
    let checkedArgs ← checkArgs env specifier.args
    checkCheckedArgsAssignableToFunctionSig env.types
      ("base constructor " ++ baseDecl.name)
      (ContractDecl.constructorSignature baseDecl) specifier.args checkedArgs

def BaseSpecifiers.check (env : CheckEnv) (sourceTypes : TypeContext)
    (contractKind : L00_SourceSolidity.ContractKind) (contractName : Name) :
    List L00_SourceSolidity.BaseSpecifier -> Except TypeError Unit
  | [] => Except.ok ()
  | specifier :: rest => do
      BaseSpecifier.check env sourceTypes contractKind contractName specifier
      BaseSpecifiers.check env sourceTypes contractKind contractName rest

def ContractDecl.checkBaseConstructorArgsForDeployment
    (storageOrder : List L00_SourceSolidity.ContractDecl)
    (target : L00_SourceSolidity.ContractDecl) :
    List L00_SourceSolidity.ContractDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | baseDecl :: rest => do
      if baseDecl.name == target.name then
        ContractDecl.checkBaseConstructorArgsForDeployment storageOrder target
          rest
      else
        let immediateDerived ←
          match L00_SourceSolidity.Executable.ContractDecl.findImmediateDerivedInOrder?
              storageOrder baseDecl with
          | some decl => Except.ok decl
          | none =>
              Except.error
                (TypeError.invalidContractHeader
                  "base constructor has no immediate derived contract")
        let args ←
          match L00_SourceSolidity.Executable.ContractDecl.baseConstructorArgsForDeployment?
              target immediateDerived baseDecl with
          | some args => Except.ok args
          | none =>
              Except.error
                (TypeError.invalidContractHeader
                  "base constructor arguments specified twice")
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
    List L00_SourceSolidity.FunctionDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | fn :: rest => do
      require (FunctionDecl.isInterfaceDeclaration fn)
        (TypeError.invalidContractHeader
          "interface function is not an external declaration")
      Functions.checkInterfaceDeclarations rest

def ContractDecl.checkKindShape (env : CheckEnv) (sourceTypes : TypeContext)
    (contract : L00_SourceSolidity.ContractDecl)
    (stateVars : List L00_SourceSolidity.StateVarDecl)
    (functions : List L00_SourceSolidity.FunctionDecl)
    (modifiers : List L00_SourceSolidity.ModifierDecl) :
    Except TypeError Unit := do
  BaseSpecifiers.check env sourceTypes contract.kind contract.name contract.bases
  match contract.kind with
  | L00_SourceSolidity.ContractKind.interface =>
      require (!contract.abstract)
        (TypeError.invalidContractHeader "interface is explicitly abstract")
      require stateVars.isEmpty
        (TypeError.invalidContractHeader
          "interface declares state variables")
      require modifiers.isEmpty
        (TypeError.invalidContractHeader "interface declares modifiers")
      require (!Functions.anyConstructorLike functions)
        (TypeError.invalidContractHeader
          "interface declares constructor, receive, or fallback")
      Functions.checkInterfaceDeclarations functions
  | L00_SourceSolidity.ContractKind.library =>
      require contract.bases.isEmpty
        (TypeError.invalidContractHeader "library has bases")
      require (!contract.abstract)
        (TypeError.invalidContractHeader "library is abstract")
      require stateVars.isEmpty
        (TypeError.invalidContractHeader "library declares state variables")
      require (!Functions.anyConstructorLike functions)
        (TypeError.invalidContractHeader
          "library declares constructor, receive, or fallback")
      require (!Functions.anyMissingBody functions)
        (TypeError.invalidContractHeader
          "library function has no implementation")
      require (!Modifiers.anyMissingBody modifiers)
        (TypeError.invalidContractHeader
          "library modifier has no implementation")
  | L00_SourceSolidity.ContractKind.contract =>
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
    (sourceConstants : List L00_SourceSolidity.StateVarDecl)
    (sourceUsingDecls : List L00_SourceSolidity.UsingDecl)
    (sourceTypes : TypeContext)
    (contract : L00_SourceSolidity.ContractDecl) : Except TypeError Unit := do
  let stateVars := contract.items.filterMap ContractItem.stateVar?
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
    stateVars.map L00_SourceSolidity.StateVarDecl.name ++
      modifiers.map L00_SourceSolidity.ModifierDecl.name ++
      errors.map L00_SourceSolidity.ErrorDecl.name ++
      structs.map L00_SourceSolidity.StructDecl.name ++
      enums.map L00_SourceSolidity.EnumDecl.name ++
      userValueTypes.map L00_SourceSolidity.UserValueTypeDecl.name
  ensureUniqueNames "contract declaration" nonFunctionNames
  ensureNamesDisjointFrom "contract declaration" nonFunctionNames
    functionNames
  ensureNamesDisjointFrom "contract declaration"
    (nonFunctionNames ++ functionNames)
    (events.map L00_SourceSolidity.EventDecl.name)
  let contractTypes :=
    sourceTypes.withContractTypes contract.name structs enums userValueTypes
  let functionSigs := FunctionDecls.signatures functions
  FunctionSigs.ensureNoDuplicateSignatures functionSigs
  FunctionSigs.ensureNoDuplicateExternalAbiSignatures contractTypes
    functionSigs
  require ((functions.filter
      (fun fn => fn.kind == L00_SourceSolidity.FunctionKind.constructor)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple constructors")
  require ((functions.filter
      (fun fn => fn.kind == L00_SourceSolidity.FunctionKind.receive)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple receive functions")
  require ((functions.filter
      (fun fn => fn.kind == L00_SourceSolidity.FunctionKind.fallback)).length <= 1)
    (TypeError.invalidFunctionHeader "multiple fallback functions")
  let modifierSigs := modifiers.map ModifierDecl.signature
  let eventSigs := events.map EventDecl.signature
  EventSigs.ensureNoDuplicateAbiSignatures contractTypes eventSigs
  let errorSigs := errors.map ErrorDecl.signature
  let currentPath := TypeContext.pathOfName contract.name
  let sourceConstantVars := StateVarDecls.namedTypes sourceConstants
  let sourceConstantBindings := StateVarDecls.namedConstness sourceConstants
  let currentConstantBindings :=
    StateVarDecls.namedConstness stateVars ++ sourceConstantBindings
  let baseEnv : CheckEnv :=
    { types := contractTypes
      vars := StateVarDecls.namedTypes stateVars ++ sourceConstantVars
      stateNames :=
        StateVarDecls.runtimeStateNamesWith currentConstantBindings stateVars
      constantBindings := currentConstantBindings
      immutableNames := StateVarDecls.immutableNames stateVars
      functions := functionSigs ++ sourceFunctions
      modifiers := modifierSigs
      modifierDecls := modifiers
      usingDecls := usingDecls ++ sourceUsingDecls
      errors := errorSigs ++ sourceErrors
      events := eventSigs ++ sourceEvents
      contractKind := some contract.kind
      currentContract := some currentPath
      returnTys := [] }
  let baseSpecifierEnv :=
    { baseEnv with
      vars := sourceConstantVars
      stateNames := []
      constantBindings := sourceConstantBindings
      immutableNames := []
      functions := [] }
  ContractDecl.checkKindShape baseSpecifierEnv sourceTypes contract stateVars
    functions modifiers
  ContractDecl.checkStorageLayoutBase baseEnv contract
  let allContracts := sourceTypes.contractDecls.map Prod.snd
  let dispatchOrder ←
    match L00_SourceSolidity.Executable.ContractDecl.dispatchOrder?
        allContracts contract with
    | some order => Except.ok order
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  let ancestorPaths :=
    (List.drop 1 dispatchOrder).map
      (fun base => TypeContext.pathOfName base.name)
  require
    (!ContractDecls.anyStorageLayoutBase (List.drop 1 dispatchOrder))
    (TypeError.invalidContractHeader
      "storage layout specified by inherited contract")
  let storageOrder ←
    match L00_SourceSolidity.Executable.ContractDecl.storageOrder?
        allContracts contract with
    | some order => Except.ok order
    | none =>
        Except.error
          (TypeError.invalidContractHeader
            "inconsistent inheritance linearization")
  let allModifierDecls := ContractDecl.modifierDeclsFromOrder dispatchOrder
  let inheritedStateVars :=
    ContractDecls.visibleStateVars contractTypes ancestorPaths
  let visibleStateVars := stateVars ++ inheritedStateVars
  let visibleConstantBindings :=
    StateVarDecls.namedConstness visibleStateVars ++ sourceConstantBindings
  let baseEnv :=
    { baseEnv with
      ancestorPaths := ancestorPaths
      vars := StateVarDecls.namedTypes visibleStateVars ++
        sourceConstantVars
      stateNames :=
        StateVarDecls.runtimeStateNamesWith visibleConstantBindings
          visibleStateVars
      constantBindings := visibleConstantBindings
      immutableNames := StateVarDecls.immutableNames visibleStateVars
      superFunctions :=
        ContractDecl.nonPrivateFunctionSigsFromOrder
          (List.drop 1 dispatchOrder)
      modifiers := ModifierDecls.signatures allModifierDecls
      modifierDecls := allModifierDecls }
  ContractDecl.checkBaseConstructorArgsForDeployment storageOrder contract
    storageOrder
  StateVarDecls.checkNoInheritedShadowing
    (ContractDecls.visibleStateVarNames contractTypes ancestorPaths)
    stateVars
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
  let currentMembers := ContractDecl.overrideMembers contractTypes contract
  let currentModifierMembers := ModifierOverrideMembers.forContract contract
  OverrideMembers.checkInheritedConflicts currentMembers inheritedMembers
  ModifierOverrideMembers.checkInheritedConflicts currentModifierMembers
    inheritedModifierMembers
  OverrideMembers.checkInheritedAbstractImplemented contract.abstract
    currentMembers inheritedMembers
  ModifierOverrideMembers.checkInheritedAbstractImplemented contract.abstract
    currentModifierMembers inheritedModifierMembers
  let rec checkStructs :
      List L00_SourceSolidity.StructDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StructDecl.check baseEnv
          [ TypeContext.pathOfName decl.name,
            TypeContext.qualifiedPath contract.name decl.name ] decl
        checkStructs rest
  let rec checkEnums :
      List L00_SourceSolidity.EnumDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        EnumDecl.check decl
        checkEnums rest
  let rec checkUserValueTypes :
      List L00_SourceSolidity.UserValueTypeDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UserValueTypeDecl.check baseEnv decl
        checkUserValueTypes rest
  let rec checkUsingDecls :
      List L00_SourceSolidity.UsingDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UsingDecl.checkContractLevel baseEnv decl
        checkUsingDecls rest
  let rec checkStateVars :
      List L00_SourceSolidity.StateVarDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StateVarDecl.checkOverrideRules contractTypes currentPath
          contract.kind ancestorPaths inheritedMembers decl
        StateVarDecl.check baseEnv decl
        checkStateVars rest
  let rec checkFunctions :
      List L00_SourceSolidity.FunctionDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | fn :: rest => do
        FunctionDecl.checkOverrideRules currentPath contract.kind ancestorPaths
          inheritedMembers fn
        FunctionDecl.check baseEnv fn
        checkFunctions rest
  let rec checkModifiers :
      List L00_SourceSolidity.ModifierDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | modifier :: rest => do
        ModifierDecl.checkOverrideRules currentPath contract.kind
          ancestorPaths inheritedModifierMembers modifier
        ModifierDecl.check baseEnv modifier
        checkModifiers rest
  let rec checkEvents :
      List L00_SourceSolidity.EventDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | event :: rest => do
        EventDecl.check baseEnv event
        checkEvents rest
  let rec checkErrors :
      List L00_SourceSolidity.ErrorDecl -> Except TypeError Unit
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
  source : L00_SourceSolidity.SourceUnit
  deriving Repr

def SourceItem.contract? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.ContractDecl
  | L00_SourceSolidity.SourceItem.contract decl => some decl
  | _ => none

def SourceItem.freeFunction? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.FunctionDecl
  | L00_SourceSolidity.SourceItem.freeFunction decl => some decl
  | _ => none

def SourceItem.freeConstant? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.StateVarDecl
  | L00_SourceSolidity.SourceItem.freeConstant decl => some decl
  | _ => none

def SourceItem.freeError? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.ErrorDecl
  | L00_SourceSolidity.SourceItem.freeError decl => some decl
  | _ => none

def SourceItem.freeStruct? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.StructDecl
  | L00_SourceSolidity.SourceItem.freeStruct decl => some decl
  | _ => none

def SourceItem.freeEnum? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.EnumDecl
  | L00_SourceSolidity.SourceItem.freeEnum decl => some decl
  | _ => none

def SourceItem.freeUserValueType? :
    L00_SourceSolidity.SourceItem ->
    Option L00_SourceSolidity.UserValueTypeDecl
  | L00_SourceSolidity.SourceItem.freeUserValueType decl => some decl
  | _ => none

def SourceItem.using? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.UsingDecl
  | L00_SourceSolidity.SourceItem.usingDecl decl => some decl
  | _ => none

def SourceItem.freeEvent? :
    L00_SourceSolidity.SourceItem -> Option L00_SourceSolidity.EventDecl
  | _ => none

def SourceUnit.check (source : L00_SourceSolidity.SourceUnit) :
    Except TypeError CheckedSourceUnit := do
  let contracts := source.items.filterMap SourceItem.contract?
  let freeFunctions := source.items.filterMap SourceItem.freeFunction?
  let freeConstants := source.items.filterMap SourceItem.freeConstant?
  let freeErrors := source.items.filterMap SourceItem.freeError?
  let freeStructs := source.items.filterMap SourceItem.freeStruct?
  let freeEnums := source.items.filterMap SourceItem.freeEnum?
  let freeUserValueTypes :=
    source.items.filterMap SourceItem.freeUserValueType?
  let sourceUsingDecls := source.items.filterMap SourceItem.using?
  let freeFunctionSigs := FunctionDecls.signatures freeFunctions
  let freeFunctionNames := freeFunctions.filterMap FunctionDecl.declaredName?
  let freeErrorSigs := freeErrors.map ErrorDecl.signature
  let freeEventSigs : List EventSig := []
  FunctionSigs.ensureNoDuplicateSignatures freeFunctionSigs
  let topLevelNonFunctionNames :=
    contracts.map L00_SourceSolidity.ContractDecl.name ++
      freeConstants.map L00_SourceSolidity.StateVarDecl.name ++
      freeErrors.map L00_SourceSolidity.ErrorDecl.name ++
      freeStructs.map L00_SourceSolidity.StructDecl.name ++
      freeEnums.map L00_SourceSolidity.EnumDecl.name ++
      freeUserValueTypes.map L00_SourceSolidity.UserValueTypeDecl.name
  ensureUniqueNames "top-level declaration" topLevelNonFunctionNames
  ensureNamesDisjointFrom "top-level declaration" topLevelNonFunctionNames
    freeFunctionNames
  let sourceTypes :=
    TypeContext.empty.withSourceTypes contracts freeStructs freeEnums
      freeUserValueTypes
  let sourceEnv : CheckEnv :=
    { types := sourceTypes
      vars := StateVarDecls.namedTypes freeConstants
      constantBindings := StateVarDecls.namedConstness freeConstants
      functions := freeFunctionSigs
      usingDecls := sourceUsingDecls
      errors := freeErrorSigs
      events := freeEventSigs
      returnTys := [] }
  let rec checkFreeStructs :
      List L00_SourceSolidity.StructDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StructDecl.check sourceEnv [TypeContext.pathOfName decl.name] decl
        checkFreeStructs rest
  let rec checkFreeEnums :
      List L00_SourceSolidity.EnumDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        EnumDecl.check decl
        checkFreeEnums rest
  let rec checkFreeUserValueTypes :
      List L00_SourceSolidity.UserValueTypeDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UserValueTypeDecl.check sourceEnv decl
        checkFreeUserValueTypes rest
  let rec checkFreeConstants :
      List L00_SourceSolidity.StateVarDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        StateVarDecl.checkFileLevelConstant sourceEnv decl
        checkFreeConstants rest
  let rec checkSourceUsingDecls :
      List L00_SourceSolidity.UsingDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | decl :: rest => do
        UsingDecl.checkFileLevel sourceEnv decl
        checkSourceUsingDecls rest
  let rec checkFreeFunctions :
      List L00_SourceSolidity.FunctionDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | fn :: rest => do
        FunctionDecl.check sourceEnv fn
        checkFreeFunctions rest
  let rec checkFreeErrors :
      List L00_SourceSolidity.ErrorDecl -> Except TypeError Unit
    | [] => Except.ok ()
    | err :: rest => do
        ErrorDecl.check sourceEnv err
        checkFreeErrors rest
  let rec checkContracts :
      List L00_SourceSolidity.ContractDecl -> Except TypeError Unit
  | [] => Except.ok ()
  | contract :: rest => do
      ContractDecl.check freeFunctionSigs freeErrorSigs freeEventSigs
          freeConstants sourceUsingDecls sourceTypes contract
      checkContracts rest
  checkFreeStructs freeStructs
  checkFreeEnums freeEnums
  checkFreeUserValueTypes freeUserValueTypes
  checkFreeConstants freeConstants
  checkSourceUsingDecls sourceUsingDecls
  checkFreeFunctions freeFunctions
  checkFreeErrors freeErrors
  checkContracts contracts
  Except.ok { source := source }

def sourceUnitAccepted? (source : L00_SourceSolidity.SourceUnit) : Bool :=
  Result.isOk (SourceUnit.check source)

namespace Examples

def uint256 : Ty := L00_SourceSolidity.Ty.uint 256

def int256 : Ty := L00_SourceSolidity.Ty.int 256

def numberExpr (value : String) : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.literal
    (L00_SourceSolidity.Literal.number value)

def boolExpr (value : Bool) : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.literal
    (L00_SourceSolidity.Literal.bool value)

def userPath (name : Name) : Path :=
  { segments := [name] }

def simpleReturnFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "f"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.number "7")))) }

def simpleSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "C"
          items := [L00_SourceSolidity.ContractItem.function
            simpleReturnFunction] }] }

def simpleSourceAccepted : Bool :=
  sourceUnitAccepted? simpleSource

def badIfFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    body :=
      some
        (L00_SourceSolidity.Stmt.ifElse
          (L00_SourceSolidity.Expr.literal
            (L00_SourceSolidity.Literal.number "1"))
          (L00_SourceSolidity.Stmt.returnValues
            (some
              (L00_SourceSolidity.Expr.literal
                (L00_SourceSolidity.Literal.number "1"))))
          (some
            (L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "0")))))) }

def badIfSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "C"
          items := [L00_SourceSolidity.ContractItem.function badIfFunction] }] }

def badIfRejected : Bool :=
  Result.isError (SourceUnit.check badIfSource)

def pointStruct : L00_SourceSolidity.StructDecl :=
  { name := "Point"
    fields := [{ name := "x", ty := uint256 }] }

def pointTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Point")

def pairStruct : L00_SourceSolidity.StructDecl :=
  { name := "Pair"
    fields :=
      [ { name := "x", ty := uint256 }
      , { name := "y", ty := uint256 } ] }

def pairTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Pair")

def pairConstructorNamedReverseExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName pairTy)
    [ L00_SourceSolidity.Arg.named "y" (numberExpr "2")
    , L00_SourceSolidity.Arg.named "x" (numberExpr "1") ]

def pairConstructorFieldFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pairX"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              pairConstructorNamedReverseExpr "x"))) }

def pairConstructorFieldSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "StructCtor"
            items :=
              [L00_SourceSolidity.ContractItem.function
                pairConstructorFieldFunction] } ] }

def pairConstructorFieldAccepted : Bool :=
  sourceUnitAccepted? pairConstructorFieldSource

def badPairConstructorMissingFieldFunction :
    L00_SourceSolidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.typeName pairTy)
              [L00_SourceSolidity.Arg.named "x" (numberExpr "1")]))) }

def badPairConstructorMissingFieldSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStructCtor"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badPairConstructorMissingFieldFunction] } ] }

def badPairConstructorMissingFieldRejected : Bool :=
  Result.isError (SourceUnit.check badPairConstructorMissingFieldSource)

def badPairConstructorMixedArgsFunction :
    L00_SourceSolidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.typeName pairTy)
              [ L00_SourceSolidity.Arg.positional (numberExpr "1")
              , L00_SourceSolidity.Arg.named "y" (numberExpr "2") ]))) }

def badPairConstructorMixedArgsSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadMixedStructCtor"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badPairConstructorMixedArgsFunction] } ] }

def badPairConstructorMixedArgsRejected : Bool :=
  Result.isError (SourceUnit.check badPairConstructorMixedArgsSource)

def badStructFieldFunction : L00_SourceSolidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    name := some "badField"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              pairConstructorNamedReverseExpr "z"))) }

def badStructFieldSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStructField"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badStructFieldFunction] } ] }

def badStructFieldRejected : Bool :=
  Result.isError (SourceUnit.check badStructFieldSource)

def structFieldAssignFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "writeField"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.member
                  (L00_SourceSolidity.Expr.ident "p") "x")
                L00_SourceSolidity.AssignOp.assign
                (numberExpr "3"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def structFieldAssignViewFunction : L00_SourceSolidity.FunctionDecl :=
  { structFieldAssignFunction with
    name := some "writeFieldView"
    mutability := L00_SourceSolidity.StateMutability.view }

def structFieldAssignSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "StructStorage"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "p", ty := pairTy }
              , L00_SourceSolidity.ContractItem.function
                  structFieldAssignFunction ] } ] }

def structFieldAssignAccepted : Bool :=
  sourceUnitAccepted? structFieldAssignSource

def structFieldAssignViewSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStructStorage"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "p", ty := pairTy }
              , L00_SourceSolidity.ContractItem.function
                  structFieldAssignViewFunction ] } ] }

def structFieldAssignViewRejected : Bool :=
  Result.isError (SourceUnit.check structFieldAssignViewSource)

def uintArrayTy : Ty :=
  L00_SourceSolidity.Ty.array uint256 none

def storageAliasFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "storageAlias"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some L00_SourceSolidity.DataLocation.storage } ]
              (some (L00_SourceSolidity.Expr.ident "arr"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.index
                  (L00_SourceSolidity.Expr.ident "local")
                  (numberExpr "0"))
                L00_SourceSolidity.AssignOp.assign
                (numberExpr "1"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageAliasSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StorageAlias"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  storageAliasFunction ] } ] }

def storageAliasAccepted : Bool :=
  sourceUnitAccepted? storageAliasSource

def uninitializedStorageAliasSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadStorageAlias"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badStorageAlias"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              none
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def uninitializedStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check uninitializedStorageAliasSource)

def memoryToStorageAliasSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MemoryToStorageAlias"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMemoryAlias"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.ident "input"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryToStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check memoryToStorageAliasSource)

def viewWritesStorageAliasSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewWritesStorageAlias"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  { storageAliasFunction with
                    name := some "badViewAliasWrite"
                    mutability :=
                      L00_SourceSolidity.StateMutability.view } ] } ] }

def viewWritesStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check viewWritesStorageAliasSource)

def storageParamHelperFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "touch"
    params :=
      [ { name := some "a"
          ty := uintArrayTy
          location := some L00_SourceSolidity.DataLocation.storage } ]
    visibility := some L00_SourceSolidity.Visibility.internal_
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.index
                  (L00_SourceSolidity.Expr.ident "a")
                  (numberExpr "0"))
                L00_SourceSolidity.AssignOp.assign
                (numberExpr "1"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageParamCallerFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callTouch"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "touch")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "arr")]))) }

def storageParamCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StorageParamCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  storageParamHelperFunction
              , L00_SourceSolidity.ContractItem.function
                  storageParamCallerFunction ] } ] }

def storageParamCallAccepted : Bool :=
  sourceUnitAccepted? storageParamCallSource

def memoryToStorageParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadStorageParamCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  storageParamHelperFunction
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCallTouch"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ]
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.ident "touch")
                              [L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "input")])))} ] } ] }

def memoryToStorageParamRejected : Bool :=
  Result.isError (SourceUnit.check memoryToStorageParamSource)

def publicStorageParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PublicStorageParam"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { storageParamHelperFunction with
                    name := some "badPublicStorageParam"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicStorageParamRejected : Bool :=
  Result.isError (SourceUnit.check publicStorageParamSource)

def libraryStorageParamFunction : L00_SourceSolidity.FunctionDecl :=
  { storageParamHelperFunction with
    name := some "touchPublic"
    visibility := some L00_SourceSolidity.Visibility.public_ }

def libraryStorageParamCallFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callLibraryTouch"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "ArrayLib")
                "touchPublic")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "arr")]))) }

def libraryStorageParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.library
            name := "ArrayLib"
            items :=
              [L00_SourceSolidity.ContractItem.function
                libraryStorageParamFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "LibraryStorageParam"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  libraryStorageParamCallFunction ] } ] }

def libraryStorageParamAccepted : Bool :=
  sourceUnitAccepted? libraryStorageParamSource

def payableLibraryFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "payMe"
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.payable }

def payableLibrarySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.library
            name := "PayableLibrary"
            items :=
              [L00_SourceSolidity.ContractItem.function
                payableLibraryFunction] } ] }

def payableLibraryRejected : Bool :=
  Result.isError (SourceUnit.check payableLibrarySource)

def calldataArrayCopyFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "copyFromCalldata"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some L00_SourceSolidity.DataLocation.calldata } ]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some L00_SourceSolidity.DataLocation.memory } ]
              (some (L00_SourceSolidity.Expr.ident "input"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.index
                  (L00_SourceSolidity.Expr.ident "local")
                  (numberExpr "0"))) ]) }

def calldataArrayCopySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CalldataArrayCopy"
            items :=
              [L00_SourceSolidity.ContractItem.function
                calldataArrayCopyFunction] } ] }

def calldataArrayCopyAccepted : Bool :=
  sourceUnitAccepted? calldataArrayCopySource

def calldataToStorageAssignFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "copyCalldataToStorage"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some L00_SourceSolidity.DataLocation.calldata } ]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "arr")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.ident "input"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataToStorageAssignSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CalldataToStorageAssign"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  calldataToStorageAssignFunction ] } ] }

def calldataToStorageAssignAccepted : Bool :=
  sourceUnitAccepted? calldataToStorageAssignSource

def calldataArrayWriteSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCalldataArrayWrite"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { calldataArrayCopyFunction with
                    name := some "writeInput"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident "input")
                                  (numberExpr "0"))
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataArrayWriteRejected : Bool :=
  Result.isError (SourceUnit.check calldataArrayWriteSource)

def calldataStructFieldWriteSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadCalldataStructFieldWrite"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "writePair"
                    params :=
                      [ { name := some "p"
                          ty := pairTy
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.calldata } ]
                    visibility :=
                      some L00_SourceSolidity.Visibility.external_
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident "p")
                                  "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataStructFieldWriteRejected : Bool :=
  Result.isError (SourceUnit.check calldataStructFieldWriteSource)

def memberCallExpr (base : L00_SourceSolidity.Expr) (member : Name)
    (args : List L00_SourceSolidity.Arg) : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.member base member) args

def arrayPushExpr (base : L00_SourceSolidity.Expr)
    (args : List L00_SourceSolidity.Arg) : L00_SourceSolidity.Expr :=
  memberCallExpr base "push" args

def arrayPopExpr (base : L00_SourceSolidity.Expr) :
    L00_SourceSolidity.Expr :=
  memberCallExpr base "pop" []

def storageArrayPushPopFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pushPop"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (arrayPushExpr (L00_SourceSolidity.Expr.ident "arr")
                [L00_SourceSolidity.Arg.positional (numberExpr "1")])
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (arrayPushExpr (L00_SourceSolidity.Expr.ident "arr") [])
                L00_SourceSolidity.AssignOp.assign
                (numberExpr "2"))
          , L00_SourceSolidity.Stmt.expr
              (arrayPopExpr (L00_SourceSolidity.Expr.ident "arr"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageArrayPushPopSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StorageArrayPushPop"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  storageArrayPushPopFunction ] } ] }

def storageArrayPushPopAccepted : Bool :=
  sourceUnitAccepted? storageArrayPushPopSource

def viewArrayPushSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewArrayPush"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badViewPush"
                    mutability :=
                      L00_SourceSolidity.StateMutability.view } ] } ] }

def viewArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check viewArrayPushSource)

def memoryArrayPushSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MemoryArrayPush"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMemoryPush"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (arrayPushExpr
                                (L00_SourceSolidity.Expr.ident "input")
                                [L00_SourceSolidity.Arg.positional
                                  (numberExpr "1")])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check memoryArrayPushSource)

def fixedUintArrayTy : Ty :=
  L00_SourceSolidity.Ty.array uint256 (some 2)

def fixedArrayPushSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FixedArrayPush"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := fixedUintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badFixedPush"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (arrayPushExpr
                                (L00_SourceSolidity.Expr.ident "arr")
                                [L00_SourceSolidity.Arg.positional
                                  (numberExpr "1")])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def fixedArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check fixedArrayPushSource)

def bytes1SevenExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName
      (L00_SourceSolidity.Ty.bytesN 1))
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [7]))]

def storageBytesPushPopFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pushPopBytes"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (arrayPushExpr (L00_SourceSolidity.Expr.ident "data") [])
          , L00_SourceSolidity.Stmt.expr
              (arrayPushExpr (L00_SourceSolidity.Expr.ident "data")
                [L00_SourceSolidity.Arg.positional bytes1SevenExpr])
          , L00_SourceSolidity.Stmt.expr
              (arrayPopExpr (L00_SourceSolidity.Expr.ident "data"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageBytesPushPopSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StorageBytesPushPop"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "data", ty := L00_SourceSolidity.Ty.bytes }
              , L00_SourceSolidity.ContractItem.function
                  storageBytesPushPopFunction ] } ] }

def storageBytesPushPopAccepted : Bool :=
  sourceUnitAccepted? storageBytesPushPopSource

def calldataBytesPopSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CalldataBytesPop"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCalldataBytesPop"
                    params :=
                      [ { name := some "data"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.calldata } ]
                    visibility :=
                      some L00_SourceSolidity.Visibility.external_
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (arrayPopExpr
                                (L00_SourceSolidity.Expr.ident "data"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataBytesPopRejected : Bool :=
  Result.isError (SourceUnit.check calldataBytesPopSource)

def sliceExpr (base : L00_SourceSolidity.Expr)
    (start? stop? : Option L00_SourceSolidity.Expr) :
    L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.slice base start? stop?

def calldataBytesSliceFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sliceBytes"
    params :=
      [ { name := some "payload"
          ty := L00_SourceSolidity.Ty.bytes
          location := some L00_SourceSolidity.DataLocation.calldata } ]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some L00_SourceSolidity.Ty.bytes
                  location :=
                    some L00_SourceSolidity.DataLocation.memory } ]
              (some
                (sliceExpr (L00_SourceSolidity.Expr.ident "payload")
                  (some (numberExpr "0")) (some (numberExpr "4"))))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataBytesSliceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CalldataBytesSlice"
            items :=
              [L00_SourceSolidity.ContractItem.function
                calldataBytesSliceFunction] } ] }

def calldataBytesSliceAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceSource

def memoryBytesSliceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MemoryBytesSlice"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badMemorySlice"
                    params :=
                      [ { name := some "payload"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ] } ] } ] }

def memoryBytesSliceRejected : Bool :=
  Result.isError (SourceUnit.check memoryBytesSliceSource)

def calldataArraySliceFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sliceArray"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some L00_SourceSolidity.DataLocation.calldata } ]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some L00_SourceSolidity.DataLocation.memory } ]
              (some
                (sliceExpr (L00_SourceSolidity.Expr.ident "input")
                  (some (numberExpr "0")) (some (numberExpr "2"))))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.index
                  (L00_SourceSolidity.Expr.ident "local")
                  (numberExpr "0"))) ]) }

def calldataArraySliceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CalldataArraySlice"
            items :=
              [L00_SourceSolidity.ContractItem.function
                calldataArraySliceFunction] } ] }

def calldataArraySliceAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceSource

def calldataSliceSignedIndexSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCalldataSliceSignedIndex"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badSignedIndex"
                    params :=
                      [ { name := some "payload"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.calldata }
                      , { name := some "offset"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some L00_SourceSolidity.Ty.bytes
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.memory } ]
                              (some
                                (sliceExpr
                                  (L00_SourceSolidity.Expr.ident "payload")
                                  (some
                                    (L00_SourceSolidity.Expr.ident "offset"))
                                  (some (numberExpr "4"))))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataSliceSignedIndexRejected : Bool :=
  Result.isError (SourceUnit.check calldataSliceSignedIndexSource)

def calldataSliceMemberSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCalldataSliceMember"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badSliceMember"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.member
                              (sliceExpr
                                (L00_SourceSolidity.Expr.ident "payload")
                                none (some (numberExpr "4")))
                              "length"))) } ] } ] }

def calldataSliceMemberRejected : Bool :=
  Result.isError (SourceUnit.check calldataSliceMemberSource)

def structParamFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usePoint"
    params :=
      [ { name := some "point"
          ty := pointTy
          location := some L00_SourceSolidity.DataLocation.memory } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.number "1")))) }

def structSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pointStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "StructUser"
            items := [L00_SourceSolidity.ContractItem.function
              structParamFunction] } ] }

def structSourceAccepted : Bool :=
  sourceUnitAccepted? structSource

def missingStructLocationFunction : L00_SourceSolidity.FunctionDecl :=
  { structParamFunction with
    params := [{ name := some "point", ty := pointTy, location := none }] }

def missingStructLocationSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pointStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStructLocation"
            items := [L00_SourceSolidity.ContractItem.function
              missingStructLocationFunction] } ] }

def missingStructLocationRejected : Bool :=
  Result.isError (SourceUnit.check missingStructLocationSource)

def tupleReturnFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "tupleReturn"
    params := []
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.uint 8
          location := none }
      , { name := none
          ty := L00_SourceSolidity.Ty.bool
          location := none } ]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.tuple
              [ L00_SourceSolidity.TupleItem.value (numberExpr "1")
              , L00_SourceSolidity.TupleItem.value (boolExpr true) ]))) }

def tupleReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TupleReturn"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tupleReturnFunction] } ] }

def tupleReturnAccepted : Bool :=
  sourceUnitAccepted? tupleReturnSource

def tupleVarDeclFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleDecl"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "a"
                  ty := some uint256
                  location := none }
              , { name := some "b"
                  ty := some L00_SourceSolidity.Ty.bool
                  location := none } ]
              (some
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value (numberExpr "1")
                  , L00_SourceSolidity.TupleItem.value
                      (boolExpr true) ]))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def tupleVarDeclSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TupleDecl"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tupleVarDeclFunction] } ] }

def tupleVarDeclAccepted : Bool :=
  sourceUnitAccepted? tupleVarDeclSource

def badTupleVarDeclFunction : L00_SourceSolidity.FunctionDecl :=
  { tupleVarDeclFunction with
    name := some "badTupleDecl"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "a"
                  ty := some uint256
                  location := none }
              , { name := some "b"
                  ty := some L00_SourceSolidity.Ty.bool
                  location := none } ]
              (some
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value (numberExpr "1")
                  , L00_SourceSolidity.TupleItem.value (numberExpr "2") ]))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def badTupleVarDeclSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTupleDecl"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badTupleVarDeclFunction] } ] }

def badTupleVarDeclRejected : Bool :=
  Result.isError (SourceUnit.check badTupleVarDeclSource)

def tupleAssignmentFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleAssign"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [{ name := some "a", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , L00_SourceSolidity.Stmt.varDecl
              [{ name := some "b", ty := some uint256, location := none }]
              (some (numberExpr "2"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "a")
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "b") ])
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "b")
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "a") ]))
          , L00_SourceSolidity.Stmt.returnValues
              (some (L00_SourceSolidity.Expr.ident "a")) ]) }

def tupleAssignmentSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TupleAssign"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tupleAssignmentFunction] } ] }

def tupleAssignmentAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentSource

def tupleAssignmentHoleFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleAssignHole"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [{ name := some "a", ty := some uint256, location := none }]
              (some (numberExpr "0"))
          , L00_SourceSolidity.Stmt.varDecl
              [{ name := some "b", ty := some uint256, location := none }]
              (some (numberExpr "0"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "a")
                  , L00_SourceSolidity.TupleItem.hole
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.ident "b") ])
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value (numberExpr "4")
                  , L00_SourceSolidity.TupleItem.value (numberExpr "99")
                  , L00_SourceSolidity.TupleItem.value (numberExpr "2") ]))
          , L00_SourceSolidity.Stmt.returnValues
              (some (L00_SourceSolidity.Expr.ident "a")) ]) }

def tupleAssignmentHoleSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TupleAssignHole"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tupleAssignmentHoleFunction] } ] }

def tupleAssignmentHoleAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentHoleSource

def tupleAssignmentFromReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TupleAssignReturn"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "pair"
                    returns :=
                      [ { name := none, ty := uint256, location := none }
                      , { name := none, ty := uint256, location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.tuple
                              [ L00_SourceSolidity.TupleItem.value
                                  (numberExpr "4")
                              , L00_SourceSolidity.TupleItem.value
                                  (numberExpr "2") ]))) }
              , L00_SourceSolidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "run"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "a")
                                  , L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "b") ])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.ident "pair")
                                  []))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "a")) ]) } ] } ] }

def tupleAssignmentFromReturnAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentFromReturnSource

def badTupleAssignmentAritySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTupleAssignArity"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badArity"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "a")
                                  , L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "b") ])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (numberExpr "1") ]))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentArityRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentAritySource)

def badTupleAssignmentTypeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTupleAssignType"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badType"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some L00_SourceSolidity.Ty.bool
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "a")
                                  , L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "b") ])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (numberExpr "1")
                                  , L00_SourceSolidity.TupleItem.value
                                      (numberExpr "2") ]))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentTypeRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentTypeSource)

def badTupleAssignmentTargetSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTupleAssignTarget"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badTarget"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.ident "a")
                                  , L00_SourceSolidity.TupleItem.value
                                      (numberExpr "1") ])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.tuple
                                  [ L00_SourceSolidity.TupleItem.value
                                      (numberExpr "1")
                                  , L00_SourceSolidity.TupleItem.value
                                      (numberExpr "2") ]))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentTargetRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentTargetSource)

def valueTypeMemoryParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadValueLocation"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badValueLocation"
                    params :=
                      [ { name := some "x"
                          ty := uint256
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ] } ] } ] }

def valueTypeMemoryParamRejected : Bool :=
  Result.isError (SourceUnit.check valueTypeMemoryParamSource)

def constantWithInitSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "ANSWER"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant
            init :=
              some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "42")) } ] }

def constantWithInitAccepted : Bool :=
  sourceUnitAccepted? constantWithInitSource

def constantWithoutInitSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "MISSING"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant } ] }

def constantWithoutInitRejected : Bool :=
  Result.isError (SourceUnit.check constantWithoutInitSource)

def bytesConstantSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "BLOB"
            ty := L00_SourceSolidity.Ty.bytes
            mutability := L00_SourceSolidity.VarMutability.constant
            init :=
              some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.bytes [1, 2])) } ] }

def bytesConstantAccepted : Bool :=
  sourceUnitAccepted? bytesConstantSource

def badArrayConstantSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadArrayConstant"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "values"
                    ty := L00_SourceSolidity.Ty.array uint256 (some 1)
                    mutability :=
                      L00_SourceSolidity.VarMutability.constant
                    init :=
                      some
                        (L00_SourceSolidity.Expr.array
                          [numberExpr "1"]) } ] } ] }

def badArrayConstantRejected : Bool :=
  Result.isError (SourceUnit.check badArrayConstantSource)

def badFreeMutableSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "NOT_CONSTANT"
            ty := uint256
            init := some (numberExpr "1") } ] }

def badFreeMutableRejected : Bool :=
  Result.isError (SourceUnit.check badFreeMutableSource)

def addmodConstantSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "MODDED"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant
            init :=
              some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "addmod")
                  [ L00_SourceSolidity.Arg.positional (numberExpr "1")
                  , L00_SourceSolidity.Arg.positional (numberExpr "2")
                  , L00_SourceSolidity.Arg.positional (numberExpr "3") ]) } ] }

def addmodConstantAccepted : Bool :=
  sourceUnitAccepted? addmodConstantSource

def constantFromStateSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadConstantFromState"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "Y"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.constant
                    init :=
                      some (L00_SourceSolidity.Expr.ident "x") } ] } ] }

def constantFromStateRejected : Bool :=
  Result.isError (SourceUnit.check constantFromStateSource)

def fileConstantInContractSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "K"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant
            init := some (numberExpr "1") }
      , L00_SourceSolidity.SourceItem.contract
          { name := "UsesFileConstant"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "K"))) } ] } ] }

def fileConstantInContractAccepted : Bool :=
  sourceUnitAccepted? fileConstantInContractSource

def stateConstantPureReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StateConstantPureRead"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "K"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.constant
                    init := some (numberExpr "1") }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "K"))) } ] } ] }

def stateConstantPureReadAccepted : Bool :=
  sourceUnitAccepted? stateConstantPureReadSource

def assignConstantSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAssignConstant"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "K"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.constant
                    init := some (numberExpr "1") }
              , L00_SourceSolidity.ContractItem.function
                  { kind := L00_SourceSolidity.FunctionKind.function
                    name := some "f"
                    params := []
                    returns := []
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "K")
                            L00_SourceSolidity.AssignOp.assign
                            (numberExpr "2"))) } ] } ] }

def assignConstantRejected : Bool :=
  Result.isError (SourceUnit.check assignConstantSource)

def badFileConstantVisibilitySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "VISIBLE"
            ty := uint256
            visibility := some L00_SourceSolidity.Visibility.public_
            mutability := L00_SourceSolidity.VarMutability.constant
            init := some (numberExpr "1") } ] }

def badFileConstantVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check badFileConstantVisibilitySource)

def badFileConstantOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "OVERRIDES"
            ty := uint256
            override? := some { bases := [] }
            mutability := L00_SourceSolidity.VarMutability.constant
            init := some (numberExpr "1") } ] }

def badFileConstantOverrideRejected : Bool :=
  Result.isError (SourceUnit.check badFileConstantOverrideSource)

def badExternalStateVarSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadExternalStateVar"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    visibility :=
                      some L00_SourceSolidity.Visibility.external_ } ] } ] }

def badExternalStateVarRejected : Bool :=
  Result.isError (SourceUnit.check badExternalStateVarSource)

def immutableInternalFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] []
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.internal_

def immutableExternalFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] []
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.external_

def immutableInternalFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ImmutableInternalFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fp"
                    ty := immutableInternalFunctionTy
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable } ] } ] }

def immutableInternalFunctionAccepted : Bool :=
  sourceUnitAccepted? immutableInternalFunctionSource

def badImmutableExternalFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadImmutableExternalFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fp"
                    ty := immutableExternalFunctionTy
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable } ] } ] }

def badImmutableExternalFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badImmutableExternalFunctionSource)

def badImmutableStringSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadImmutableString"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "text"
                    ty := L00_SourceSolidity.Ty.string
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable } ] } ] }

def badImmutableStringRejected : Bool :=
  Result.isError (SourceUnit.check badImmutableStringSource)

def immutableAssignedInConstructorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ImmutableAssignedInConstructor"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable }
              , L00_SourceSolidity.ContractItem.function
                  { kind := L00_SourceSolidity.FunctionKind.constructor
                    params := []
                    returns := []
                    visibility := none
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "x")
                            L00_SourceSolidity.AssignOp.assign
                            (numberExpr "1"))) } ] } ] }

def immutableAssignedInConstructorAccepted : Bool :=
  sourceUnitAccepted? immutableAssignedInConstructorSource

def immutableAssignedInFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadImmutableAssignedInFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable }
              , L00_SourceSolidity.ContractItem.function
                  { kind := L00_SourceSolidity.FunctionKind.function
                    name := some "f"
                    params := []
                    returns := []
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "x")
                            L00_SourceSolidity.AssignOp.assign
                            (numberExpr "1"))) } ] } ] }

def immutableAssignedInFunctionRejected : Bool :=
  Result.isError (SourceUnit.check immutableAssignedInFunctionSource)

def immutableInlineConstantPureReadSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ImmutableInlineConstantPureRead"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable
                    init := some (numberExpr "1") }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "x"))) } ] } ] }

def immutableInlineConstantPureReadAccepted : Bool :=
  sourceUnitAccepted? immutableInlineConstantPureReadSource

def immutableRuntimePureReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadImmutableRuntimePureRead"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.immutable }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "x"))) } ] } ] }

def immutableRuntimePureReadRejected : Bool :=
  Result.isError (SourceUnit.check immutableRuntimePureReadSource)

def transientUintSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TransientUint"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "flag"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.transient } ] } ] }

def transientUintAccepted : Bool :=
  sourceUnitAccepted? transientUintSource

def badTransientInitSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTransientInit"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "flag"
                    ty := uint256
                    mutability :=
                      L00_SourceSolidity.VarMutability.transient
                    init := some (numberExpr "1") } ] } ] }

def badTransientInitRejected : Bool :=
  Result.isError (SourceUnit.check badTransientInitSource)

def badTransientStringSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadTransientString"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "text"
                    ty := L00_SourceSolidity.Ty.string
                    mutability :=
                      L00_SourceSolidity.VarMutability.transient } ] } ] }

def badTransientStringRejected : Bool :=
  Result.isError (SourceUnit.check badTransientStringSource)

def unknownUserTypeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UnknownType"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "Missing") } ] } ] }

def unknownUserTypeRejected : Bool :=
  Result.isError (SourceUnit.check unknownUserTypeSource)

def zeroFixedArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ZeroFixedArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "xs"
                    ty := L00_SourceSolidity.Ty.array uint256
                      (some 0) } ] } ] }

def zeroFixedArrayRejected : Bool :=
  Result.isError (SourceUnit.check zeroFixedArraySource)

def emptyEnumSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeEnum
          { name := "Empty", cases := [] } ] }

def emptyEnumRejected : Bool :=
  Result.isError (SourceUnit.check emptyEnumSource)

def colorEnum : L00_SourceSolidity.EnumDecl :=
  { name := "Color", cases := ["Red", "Blue"] }

def colorTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Color")

def enumMemberFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "red"
    params := []
    returns := [{ name := none, ty := colorTy, location := none }]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.typeName colorTy) "Red"))) }

def enumMemberSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeEnum colorEnum
      , L00_SourceSolidity.SourceItem.contract
          { name := "EnumUser"
            items :=
              [L00_SourceSolidity.ContractItem.function
                enumMemberFunction] } ] }

def enumMemberAccepted : Bool :=
  sourceUnitAccepted? enumMemberSource

def badEnumMemberFunction : L00_SourceSolidity.FunctionDecl :=
  { enumMemberFunction with
    name := some "green"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.typeName colorTy) "Green"))) }

def badEnumMemberSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeEnum colorEnum
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadEnumUser"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badEnumMemberFunction] } ] }

def badEnumMemberRejected : Bool :=
  Result.isError (SourceUnit.check badEnumMemberSource)

def typeMaxFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "maxValue"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.typeName uint256) "max"))) }

def typeMaxSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "TypeMax"
          items :=
            [L00_SourceSolidity.ContractItem.function
              typeMaxFunction] }] }

def typeMaxAccepted : Bool :=
  sourceUnitAccepted? typeMaxSource

def unitNumberReturnFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "unitNumber"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.unitNumber "2.5"
                L00_SourceSolidity.UnitDenomination.ether)))) }

def unitNumberReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "UnitNumber"
          items :=
            [L00_SourceSolidity.ContractItem.function
              unitNumberReturnFunction] }] }

def unitNumberReturnAccepted : Bool :=
  sourceUnitAccepted? unitNumberReturnSource

def fractionalWeiReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "FractionalWei"
          items :=
            [ L00_SourceSolidity.ContractItem.function
                { unitNumberReturnFunction with
                  body :=
                    some
                      (L00_SourceSolidity.Stmt.returnValues
                        (some
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.unitNumber "0.5"
                              L00_SourceSolidity.UnitDenomination.wei)))) } ] }] }

def fractionalWeiReturnRejected : Bool :=
  Result.isError (SourceUnit.check fractionalWeiReturnSource)

def subWeiEtherReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [L00_SourceSolidity.SourceItem.contract
        { name := "SubWeiEther"
          items :=
            [ L00_SourceSolidity.ContractItem.function
                { unitNumberReturnFunction with
                  body :=
                    some
                      (L00_SourceSolidity.Stmt.returnValues
                        (some
                          (L00_SourceSolidity.Expr.literal
                            (L00_SourceSolidity.Literal.unitNumber "1e-19"
                              L00_SourceSolidity.UnitDenomination.ether)))) } ] }] }

def subWeiEtherReturnRejected : Bool :=
  Result.isError (SourceUnit.check subWeiEtherReturnSource)

def contractCodeReturnFunction (contractName member : Name) :
    L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some member
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.bytes
          location := some L00_SourceSolidity.DataLocation.memory } ]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.typeName
                (L00_SourceSolidity.Ty.user (userPath contractName)))
              member))) }

def typeCreationCodeOtherSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CodeTarget" }
      , L00_SourceSolidity.SourceItem.contract
          { name := "CodeReader"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  (contractCodeReturnFunction "CodeTarget"
                    "creationCode") ] } ] }

def typeCreationCodeOtherAccepted : Bool :=
  sourceUnitAccepted? typeCreationCodeOtherSource

def typeCreationCodeSelfSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "SelfCode"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  (contractCodeReturnFunction "SelfCode"
                    "creationCode") ] } ] }

def typeCreationCodeSelfRejected : Bool :=
  Result.isError (SourceUnit.check typeCreationCodeSelfSource)

def typeRuntimeCodeBaseContract : L00_SourceSolidity.ContractDecl :=
  { name := "RuntimeBase" }

def typeRuntimeCodeDerivedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          typeRuntimeCodeBaseContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "RuntimeDerived"
            bases := [{ base := userPath "RuntimeBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  (contractCodeReturnFunction "RuntimeBase"
                    "runtimeCode") ] } ] }

def typeRuntimeCodeDerivedRejected : Bool :=
  Result.isError (SourceUnit.check typeRuntimeCodeDerivedSource)

def memoryMappingLocalFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "m"
                  ty := some
                    (L00_SourceSolidity.Ty.mapping uint256 uint256)
                  location := some L00_SourceSolidity.DataLocation.memory } ]
              none
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "1"))) ]) }

def memoryMappingLocalSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadMappingLocation"
            items := [L00_SourceSolidity.ContractItem.function
              memoryMappingLocalFunction] } ] }

def memoryMappingLocalRejected : Bool :=
  Result.isError (SourceUnit.check memoryMappingLocalSource)

def publicMappingParamFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesMap"
    params :=
      [ { name := some "m"
          ty := L00_SourceSolidity.Ty.mapping uint256 uint256
          location := some L00_SourceSolidity.DataLocation.storage } ] }

def publicMappingParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiMapping"
            items := [L00_SourceSolidity.ContractItem.function
              publicMappingParamFunction] } ] }

def publicMappingParamRejected : Bool :=
  Result.isError (SourceUnit.check publicMappingParamSource)

def mappingReadFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readMap"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.index
              (L00_SourceSolidity.Expr.ident "m")
              (numberExpr "1")))) }

def mappingReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MappingRead"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "m"
                    ty := L00_SourceSolidity.Ty.mapping
                      uint256 uint256 }
              , L00_SourceSolidity.ContractItem.function
                  mappingReadFunction ] } ] }

def mappingReadAccepted : Bool :=
  sourceUnitAccepted? mappingReadSource

def badMappingIndexFunction : L00_SourceSolidity.FunctionDecl :=
  { mappingReadFunction with
    name := some "badMapIndex"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.index
              (L00_SourceSolidity.Expr.ident "m")
              (boolExpr true)))) }

def badMappingIndexSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadMappingIndex"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "m"
                    ty := L00_SourceSolidity.Ty.mapping
                      uint256 uint256 }
              , L00_SourceSolidity.ContractItem.function
                  badMappingIndexFunction ] } ] }

def badMappingIndexRejected : Bool :=
  Result.isError (SourceUnit.check badMappingIndexSource)

def keyTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Key")

def keyDecl : L00_SourceSolidity.UserValueTypeDecl :=
  { name := "Key", underlying := uint256 }

def userValueMappingKeyFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readByKey"
    params := [{ name := some "k", ty := keyTy, location := none }]
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.index
              (L00_SourceSolidity.Expr.ident "m")
              (L00_SourceSolidity.Expr.ident "k")))) }

def userValueMappingKeySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType keyDecl
      , L00_SourceSolidity.SourceItem.contract
          { name := "UserValueMappingKey"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "m"
                    ty := L00_SourceSolidity.Ty.mapping
                      keyTy uint256 }
              , L00_SourceSolidity.ContractItem.function
                  userValueMappingKeyFunction ] } ] }

def userValueMappingKeyAccepted : Bool :=
  sourceUnitAccepted? userValueMappingKeySource

def signedMappingKeySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "SignedMappingKey"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "values"
                    ty := L00_SourceSolidity.Ty.mapping
                      int256 uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := int256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident
                                "values")
                              (L00_SourceSolidity.Expr.ident
                                "key"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := int256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident
                                "values")
                              (L00_SourceSolidity.Expr.ident
                                "key")))) } ] } ] }

def signedMappingKeyAccepted : Bool :=
  sourceUnitAccepted? signedMappingKeySource

def stringLengthSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadStringLength"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "stringLength"
                    params :=
                      [ { name := some "s"
                          ty := L00_SourceSolidity.Ty.string
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.memory } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "s")
                              "length"))) } ] } ] }

def stringLengthRejected : Bool :=
  Result.isError (SourceUnit.check stringLengthSource)

def duplicateSignatureSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateFns"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  simpleReturnFunction
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.literal
                              (L00_SourceSolidity.Literal.number "9")))) } ] } ] }

def duplicateSignatureRejected : Bool :=
  Result.isError (SourceUnit.check duplicateSignatureSource)

def stateFunctionNameClashSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "StateFunctionNameClash"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "clash", ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with name := some "clash" } ] } ] }

def stateFunctionNameClashRejected : Bool :=
  Result.isError (SourceUnit.check stateFunctionNameClashSource)

def functionEventNameClashSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FunctionEventNameClash"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with name := some "Ping" }
              , L00_SourceSolidity.ContractItem.eventDecl
                  { name := "Ping"
                    params := [{ name := none, ty := uint256 }] } ] } ] }

def functionEventNameClashRejected : Bool :=
  Result.isError (SourceUnit.check functionEventNameClashSource)

def topLevelFunctionContractNameClashSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TopLevelClash" }
      , L00_SourceSolidity.SourceItem.freeFunction
          { simpleReturnFunction with
            name := some "TopLevelClash"
            visibility := none } ] }

def topLevelFunctionContractNameClashRejected : Bool :=
  Result.isError
    (SourceUnit.check topLevelFunctionContractNameClashSource)

def freeErrorOverloadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError
          { name := "FreeErrorClash"
            params := [{ name := none, ty := uint256, location := none }] }
      , L00_SourceSolidity.SourceItem.freeError
          { name := "FreeErrorClash"
            params :=
              [ { name := none
                  ty := L00_SourceSolidity.Ty.address false
                  location := none } ] } ] }

def freeErrorOverloadRejected : Bool :=
  Result.isError (SourceUnit.check freeErrorOverloadSource)

def abiClashContractTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "B")

def abiClashContractParamFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "clash"
    params :=
      [{ name := some "target", ty := abiClashContractTy, location := none }] }

def abiClashAddressParamFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "clash"
    params :=
      [ { name := some "target"
          ty := L00_SourceSolidity.Ty.address false
          location := none } ] }

def abiExternalSignatureClashSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "B" }
      , L00_SourceSolidity.SourceItem.contract
          { name := "AbiClash"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  abiClashContractParamFunction
              , L00_SourceSolidity.ContractItem.function
                  abiClashAddressParamFunction ] } ] }

def abiExternalSignatureClashRejected : Bool :=
  Result.isError (SourceUnit.check abiExternalSignatureClashSource)

def internalAbiTwinSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "B" }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InternalAbiTwin"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { abiClashContractParamFunction with
                    visibility := some L00_SourceSolidity.Visibility.internal_ }
              , L00_SourceSolidity.ContractItem.function
                  { abiClashAddressParamFunction with
                    visibility := some L00_SourceSolidity.Visibility.internal_ } ] } ] }

def internalAbiTwinAccepted : Bool :=
  sourceUnitAccepted? internalAbiTwinSource

def passThroughModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "onlyReady"
    body := some L00_SourceSolidity.Stmt.modifierPlaceholder }

def modifierInvocationFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "withModifier"
    modifiers :=
      [ { target := userPath "onlyReady", args := [] } ] }

def modifierInvocationSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ModifierUser"
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  passThroughModifier
              , L00_SourceSolidity.ContractItem.function
                  modifierInvocationFunction ] } ] }

def modifierInvocationAccepted : Bool :=
  sourceUnitAccepted? modifierInvocationSource

def returnThroughModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ReturnThroughModifier"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.modifierDecl
                  { name := "afterReturn"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.modifierPlaceholder
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "0")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility := some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    modifiers :=
                      [{ target := userPath "afterReturn"
                         args := [] }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "11")) ]) } ] } ] }

def returnThroughModifierAccepted : Bool :=
  sourceUnitAccepted? returnThroughModifierSource

def uncheckedArithmeticFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "uncheckedArithmetic"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [{ name := some "x", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , L00_SourceSolidity.Stmt.unchecked
              (L00_SourceSolidity.Stmt.block
                [L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.assign
                    (L00_SourceSolidity.Expr.ident "x")
                    L00_SourceSolidity.AssignOp.addAssign
                    (numberExpr "1"))])
          , L00_SourceSolidity.Stmt.returnValues
              (some (L00_SourceSolidity.Expr.ident "x")) ]) }

def uncheckedArithmeticSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UncheckedArithmetic"
            items := [L00_SourceSolidity.ContractItem.function
              uncheckedArithmeticFunction] } ] }

def uncheckedArithmeticAccepted : Bool :=
  sourceUnitAccepted? uncheckedArithmeticSource

def uncheckedInternalMaxPlusOneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.binary
    L00_SourceSolidity.BinaryOp.add
    (L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName uint256) "max")
    (numberExpr "1")

def uncheckedInternalCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UncheckedInternalCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { name := some "overflow"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some uncheckedInternalMaxPlusOneExpr)) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "id"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }]
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "callOverflow"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.unchecked
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident
                                  "overflow") [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "callWithWrappedArg"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.unchecked
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "id")
                                [L00_SourceSolidity.Arg.positional
                                  uncheckedInternalMaxPlusOneExpr])))) } ] } ] }

def uncheckedInternalCallAccepted : Bool :=
  sourceUnitAccepted? uncheckedInternalCallSource

def internalReturnSubexpressionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalReturnSubexpression"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { name := some "base"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (numberExpr "41"))) }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "run"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.add
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "base")
                                [])
                              (numberExpr "1")))) } ] } ] }

def internalReturnSubexpressionAccepted : Bool :=
  sourceUnitAccepted? internalReturnSubexpressionSource

def internalReturnRightSubexpressionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalReturnRightSubexpression"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "run"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.add
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "5"))
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "read")
                                [])))) } ] } ] }

def internalReturnRightSubexpressionAccepted : Bool :=
  sourceUnitAccepted? internalReturnRightSubexpressionSource

def internalReturnShortCircuitSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalReturnShortCircuit"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "mark"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "andSkip"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.boolAnd
                              (boolExpr false)
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "mark")
                                [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "orSkip"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.boolOr
                              (boolExpr true)
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "mark")
                                [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "andCall"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.boolAnd
                              (boolExpr true)
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "mark")
                                [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "orCall"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.boolOr
                              (boolExpr false)
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "mark")
                                [])))) } ] } ] }

def internalReturnShortCircuitAccepted : Bool :=
  sourceUnitAccepted? internalReturnShortCircuitSource

def internalBinaryLocalCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalBinaryLocalCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "base"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (numberExpr "41"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setFive"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "5"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "mark"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "2"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "2"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVar"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.add
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "base")
                                    [])
                                  (numberExpr "1")))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.add
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "setFive")
                                    [])
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "read")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssign"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "y")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.add
                                  (L00_SourceSolidity.Expr.assign
                                    (L00_SourceSolidity.Expr.ident "x")
                                    L00_SourceSolidity.AssignOp.assign
                                    (numberExpr "5"))
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "read")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "y")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.add
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "setFive")
                                    [])
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "read")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarShort"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.boolAnd
                                  (boolExpr false)
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "mark")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignShort"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "ok")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.boolOr
                                  (boolExpr true)
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "mark")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarShortBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.boolAnd
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident
                                      "flagFalse")
                                    [])
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "mark")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignShortBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "ok")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.boolOr
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "flagTrue")
                                    [])
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "mark")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignShortBothCall"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "ok")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.boolAnd
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "flagTrue")
                                    [])
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "mark")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalBinaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalBinaryLocalCallSource

def internalUnaryLocalCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalUnaryLocalCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "zero"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "11"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "0")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "minusFive"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    params :=
                      [{ name := some "seed"
                         ty := int256
                         location := none }]
                    returns :=
                      [{ name := some "out"
                         ty := int256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "13"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.unary
                                  L00_SourceSolidity.UnaryOp.neg
                                  (L00_SourceSolidity.Expr.ident
                                    "seed"))) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReturnNot"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.logicalNot
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "flagFalse")
                                [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarNot"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.unary
                                  L00_SourceSolidity.UnaryOp.logicalNot
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident
                                      "flagFalse")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "ok")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignNot"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some L00_SourceSolidity.Ty.bool
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "ok")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.unary
                                  L00_SourceSolidity.UnaryOp.logicalNot
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident
                                      "flagFalse")
                                    [])))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "ok")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBitNot"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.bitNot
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "zero")
                                [])))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runNeg"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := int256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.neg
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "minusFive")
                                [L00_SourceSolidity.Arg.positional
                                  (numberExpr "5")])))) } ] } ] }

def internalUnaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalUnaryLocalCallSource

def internalTernaryCallExpr (name : Name) : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.ident name) []

def internalTernaryAssignXExpr (value : String) :
    L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.assign
    (L00_SourceSolidity.Expr.ident "x")
    L00_SourceSolidity.AssignOp.assign
    (numberExpr value)

def internalTernaryLocalCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalTernaryLocalCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (internalTernaryAssignXExpr "1")
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (internalTernaryAssignXExpr "2")
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReturnTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ternary
                              (internalTernaryCallExpr "flagTrue")
                              (internalTernaryAssignXExpr "21")
                              (internalTernaryAssignXExpr "22")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReturnFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ternary
                              (internalTernaryCallExpr "flagFalse")
                              (internalTernaryAssignXExpr "21")
                              (internalTernaryAssignXExpr "22")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.ternary
                                  (internalTernaryCallExpr "flagTrue")
                                  (internalTernaryAssignXExpr "31")
                                  (internalTernaryAssignXExpr "32")))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "y")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ternary
                                  (internalTernaryCallExpr "flagFalse")
                                  (internalTernaryAssignXExpr "41")
                                  (internalTernaryAssignXExpr "42")))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) } ] } ] }

def internalTernaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalTernaryLocalCallSource

def internalTernaryBranchCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalTernaryBranchCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "markThen"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (internalTernaryAssignXExpr "21")
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "markElse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (internalTernaryAssignXExpr "22")
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReturnThen"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ternary
                              (boolExpr true)
                              (internalTernaryCallExpr "markThen")
                              (internalTernaryAssignXExpr "99")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReturnElse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ternary
                              (boolExpr false)
                              (internalTernaryAssignXExpr "99")
                              (internalTernaryCallExpr "markElse")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runVarBothFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (L00_SourceSolidity.Expr.ternary
                                  (boolExpr false)
                                  (internalTernaryCallExpr "markThen")
                                  (internalTernaryCallExpr "markElse")))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssignBothTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "y")
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ternary
                                  (boolExpr true)
                                  (internalTernaryCallExpr "markThen")
                                  (internalTernaryCallExpr "markElse")))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) } ] } ] }

def internalTernaryBranchCallAccepted : Bool :=
  sourceUnitAccepted? internalTernaryBranchCallSource

def internalIfConditionCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalIfConditionCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.ifElse
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "flagTrue")
                            [])
                          (L00_SourceSolidity.Stmt.returnValues
                            (some
                              (L00_SourceSolidity.Expr.binary
                                L00_SourceSolidity.BinaryOp.add
                                (L00_SourceSolidity.Expr.ident "x")
                                (numberExpr "1"))))
                          (some
                            (L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "9"))))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.ifElse
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "flagFalse")
                            [])
                          (L00_SourceSolidity.Stmt.returnValues
                            (some (numberExpr "9")))
                          (some
                            (L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.add
                                  (L00_SourceSolidity.Expr.ident "x")
                                  (numberExpr "2")))))) } ] } ] }

def internalIfConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalIfConditionCallSource

def internalWhileConditionCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalWhileConditionCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "keepGoing"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.ifElse
                          (L00_SourceSolidity.Expr.binary
                            L00_SourceSolidity.BinaryOp.lt
                            (L00_SourceSolidity.Expr.ident "x")
                            (numberExpr "3"))
                          (L00_SourceSolidity.Stmt.block
                            [ L00_SourceSolidity.Stmt.expr
                                (L00_SourceSolidity.Expr.assign
                                  (L00_SourceSolidity.Expr.ident "x")
                                  L00_SourceSolidity.AssignOp.addAssign
                                  (numberExpr "1"))
                            , L00_SourceSolidity.Stmt.returnValues
                                (some (boolExpr true)) ])
                          (some
                            (L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false))))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.whileLoop
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "keepGoing")
                                [])
                              L00_SourceSolidity.Stmt.empty
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalWhileConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalWhileConditionCallSource

def internalForPostCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalForPostCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "bump"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "x")
                            L00_SourceSolidity.AssignOp.addAssign
                            (numberExpr "1"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "0"))
                          , L00_SourceSolidity.Stmt.forLoop
                              none
                              (some
                                (L00_SourceSolidity.Expr.binary
                                  L00_SourceSolidity.BinaryOp.lt
                                  (L00_SourceSolidity.Expr.ident "x")
                                  (numberExpr "3")))
                              (some
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.ident "bump")
                                  []))
                              L00_SourceSolidity.Stmt.continue
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalForPostCallAccepted : Bool :=
  sourceUnitAccepted? internalForPostCallSource

def loopBreakContinueSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "LoopBreakContinue"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBreak"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "0"))
                          , L00_SourceSolidity.Stmt.whileLoop
                              (boolExpr true)
                              (L00_SourceSolidity.Stmt.block
                                [ L00_SourceSolidity.Stmt.expr
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "x")
                                      L00_SourceSolidity.AssignOp.addAssign
                                      (numberExpr "1"))
                                , L00_SourceSolidity.Stmt.ifElse
                                    (L00_SourceSolidity.Expr.binary
                                      L00_SourceSolidity.BinaryOp.eq
                                      (L00_SourceSolidity.Expr.ident "x")
                                      (numberExpr "3"))
                                    L00_SourceSolidity.Stmt.break
                                    none ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runContinue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "0"))
                          , L00_SourceSolidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some (numberExpr "0"))
                          , L00_SourceSolidity.Stmt.whileLoop
                              (L00_SourceSolidity.Expr.binary
                                L00_SourceSolidity.BinaryOp.lt
                                (L00_SourceSolidity.Expr.ident "x")
                                (numberExpr "5"))
                              (L00_SourceSolidity.Stmt.block
                                [ L00_SourceSolidity.Stmt.expr
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "x")
                                      L00_SourceSolidity.AssignOp.addAssign
                                      (numberExpr "1"))
                                , L00_SourceSolidity.Stmt.ifElse
                                    (L00_SourceSolidity.Expr.binary
                                      L00_SourceSolidity.BinaryOp.eq
                                      (L00_SourceSolidity.Expr.binary
                                        L00_SourceSolidity.BinaryOp.mod
                                        (L00_SourceSolidity.Expr.ident "x")
                                        (numberExpr "2"))
                                      (numberExpr "0"))
                                    L00_SourceSolidity.Stmt.continue
                                    none
                                , L00_SourceSolidity.Stmt.expr
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "y")
                                      L00_SourceSolidity.AssignOp.addAssign
                                      (L00_SourceSolidity.Expr.ident "x")) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "y")) ]) } ] } ] }

def loopBreakContinueAccepted : Bool :=
  sourceUnitAccepted? loopBreakContinueSource

def breakOutsideLoopSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BreakOutsideLoop"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body := some L00_SourceSolidity.Stmt.break } ] } ] }

def breakOutsideLoopRejected : Bool :=
  Result.isError (SourceUnit.check breakOutsideLoopSource)

def continueOutsideLoopSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ContinueOutsideLoop"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body := some L00_SourceSolidity.Stmt.continue } ] } ] }

def continueOutsideLoopRejected : Bool :=
  Result.isError (SourceUnit.check continueOutsideLoopSource)

def namedReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NamedReturn"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "stop"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues none
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "99")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runFallthrough"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "out")
                            L00_SourceSolidity.AssignOp.assign
                            (numberExpr "9"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runDefault"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body := some L00_SourceSolidity.Stmt.empty } ] } ] }

def namedReturnAccepted : Bool :=
  sourceUnitAccepted? namedReturnSource

def namedBareReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NamedBareReturn"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues none) } ] } ] }

def namedBareReturnRejected : Bool :=
  Result.isError (SourceUnit.check namedBareReturnSource)

def internalRequireConditionCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalRequireConditionCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "okTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "okFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runAssert"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "assert")
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "okTrue")
                                    [])])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runRequire"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "okTrue")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.string
                                        "bad")) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runRequireFail"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident
                                        "okFalse")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.string
                                        "bad")) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runRequireCustomFail"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident
                                        "okFalse")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "Bad")
                                      [L00_SourceSolidity.Arg.positional
                                        (numberExpr "7")]) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalRequireConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalRequireConditionCallSource

def internalRequireReasonCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalRequireReasonCall"
            items :=
              [ L00_SourceSolidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "note"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.string
                         location :=
                           some L00_SourceSolidity.DataLocation.memory }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "9"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.literal
                                  (L00_SourceSolidity.Literal.string
                                    "ok"))) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "okTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.literal
                                  (L00_SourceSolidity.Literal.bool
                                    true))) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "okFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := L00_SourceSolidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "1"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.literal
                                  (L00_SourceSolidity.Literal.bool
                                    false))) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runReasonTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.bool true))
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "note")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runCustomFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.literal
                                      (L00_SourceSolidity.Literal.bool false))
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "Bad")
                                      [L00_SourceSolidity.Arg.positional
                                        (L00_SourceSolidity.Expr.call
                                          (L00_SourceSolidity.Expr.ident
                                            "value")
                                          [])]) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBothReasonTrue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident
                                        "okTrue")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "note")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBothCustomFalse"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "require")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident
                                        "okFalse")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "Bad")
                                      [L00_SourceSolidity.Arg.positional
                                        (L00_SourceSolidity.Expr.call
                                          (L00_SourceSolidity.Expr.ident
                                            "value")
                                          [])]) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalRequireReasonCallAccepted : Bool :=
  sourceUnitAccepted? internalRequireReasonCallSource

def internalEmitArgumentCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalEmitArgumentCall"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl
                  { name := "Seen"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         indexed := false }] }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.emitEvent
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Seen")
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "value")
                                    [])])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalEmitArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalEmitArgumentCallSource

def internalEmitTwoArgumentCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalEmitTwoArgumentCall"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl
                  { name := "Seen"
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          indexed := false }
                      , { name := some "right"
                          ty := uint256
                          indexed := false } ] }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runLeft"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.emitEvent
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Seen")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "value")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.binary
                                      L00_SourceSolidity.BinaryOp.add
                                      (L00_SourceSolidity.Expr.ident "x")
                                      (numberExpr "1")) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runRight"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.emitEvent
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Seen")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "x")
                                      L00_SourceSolidity.AssignOp.assign
                                      (numberExpr "5"))
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "read")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.emitEvent
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Seen")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "value")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "read")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              ] } ] }

def internalEmitTwoArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalEmitTwoArgumentCallSource

def internalRevertArgumentCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalRevertArgumentCall"
            items :=
              [ L00_SourceSolidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.revertCall
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Bad")
                                [L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "value")
                                    [])])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalRevertArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalRevertArgumentCallSource

def internalRevertTwoArgumentCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalRevertTwoArgumentCall"
            items :=
              [ L00_SourceSolidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ] }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "7"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runLeft"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.revertCall
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Bad")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "value")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.binary
                                      L00_SourceSolidity.BinaryOp.add
                                      (L00_SourceSolidity.Expr.ident "x")
                                      (numberExpr "1")) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runRight"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.revertCall
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Bad")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.assign
                                      (L00_SourceSolidity.Expr.ident "x")
                                      L00_SourceSolidity.AssignOp.assign
                                      (numberExpr "5"))
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "read")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "runBoth"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.revertCall
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.ident "Bad")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "value")
                                      [])
                                , L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.call
                                      (L00_SourceSolidity.Expr.ident "read")
                                      []) ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) } ] } ] }

def internalRevertTwoArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalRevertTwoArgumentCallSource

def internalTupleReturnCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalTupleReturnCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "5"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.tuple
                              [ L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "value")
                                    [])
                              , L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.binary
                                    L00_SourceSolidity.BinaryOp.add
                                    (L00_SourceSolidity.Expr.ident "x")
                                    (numberExpr "1")) ]))) } ] } ] }

def internalTupleReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleReturnCallSource

def internalTupleRightReturnCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalTupleRightReturnCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.tuple
                              [ L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.assign
                                    (L00_SourceSolidity.Expr.ident "x")
                                    L00_SourceSolidity.AssignOp.assign
                                    (numberExpr "5"))
                              , L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "read")
                                    []) ]))) } ] } ] }

def internalTupleRightReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleRightReturnCallSource

def internalTupleBothReturnCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalTupleBothReturnCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setFive"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.ident "x")
                                L00_SourceSolidity.AssignOp.assign
                                (numberExpr "5"))
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.ident "x")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some (L00_SourceSolidity.Expr.ident "x"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.tuple
                              [ L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "setFive")
                                    [])
                              , L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.ident "read")
                                    []) ]))) } ] } ] }

def internalTupleBothReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleBothReturnCallSource

def nestedUncheckedFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "nestedUnchecked"
    body :=
      some
        (L00_SourceSolidity.Stmt.unchecked
          (L00_SourceSolidity.Stmt.block
            [L00_SourceSolidity.Stmt.unchecked
              (L00_SourceSolidity.Stmt.block
                [L00_SourceSolidity.Stmt.empty])])) }

def nestedUncheckedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedUnchecked"
            items := [L00_SourceSolidity.ContractItem.function
              nestedUncheckedFunction] } ] }

def nestedUncheckedRejected : Bool :=
  Result.isError (SourceUnit.check nestedUncheckedSource)

def uncheckedPlaceholderModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "uncheckedPlaceholder"
    body :=
      some
        (L00_SourceSolidity.Stmt.unchecked
          (L00_SourceSolidity.Stmt.block
            [L00_SourceSolidity.Stmt.modifierPlaceholder])) }

def uncheckedPlaceholderFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usesUncheckedPlaceholder"
    modifiers :=
      [{ target := userPath "uncheckedPlaceholder", args := [] }] }

def uncheckedPlaceholderSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UncheckedPlaceholder"
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  uncheckedPlaceholderModifier
              , L00_SourceSolidity.ContractItem.function
                  uncheckedPlaceholderFunction ] } ] }

def uncheckedPlaceholderRejected : Bool :=
  Result.isError (SourceUnit.check uncheckedPlaceholderSource)

def unknownModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UnknownModifier"
            items := [L00_SourceSolidity.ContractItem.function
              modifierInvocationFunction] } ] }

def unknownModifierRejected : Bool :=
  Result.isError (SourceUnit.check unknownModifierSource)

def valueOption (amount : String) : L00_SourceSolidity.CallOption :=
  L00_SourceSolidity.CallOption.named "value"
    (L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.number amount))

def gasOption (amount : String) : L00_SourceSolidity.CallOption :=
  L00_SourceSolidity.CallOption.named "gas"
    (L00_SourceSolidity.Expr.literal
      (L00_SourceSolidity.Literal.number amount))

def seedConstructor
    (mutability : L00_SourceSolidity.StateMutability) :
    L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.constructor
    name := none
    params :=
      [ { name := some "seed"
          ty := uint256
          location := none } ]
    returns := []
    visibility := none
    mutability := mutability
    body := some L00_SourceSolidity.Stmt.empty }

def constructorTargetTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "CtorTarget")

def constructorTargetContract : L00_SourceSolidity.ContractDecl :=
  { name := "CtorTarget"
    items :=
      [L00_SourceSolidity.ContractItem.function
        (seedConstructor L00_SourceSolidity.StateMutability.nonpayable)] }

def constructorCreateFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "make"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.newExpr constructorTargetTy
                [L00_SourceSolidity.Arg.named "seed" (numberExpr "7")])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def constructorCreateSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract constructorTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "CtorMaker"
            items :=
              [L00_SourceSolidity.ContractItem.function
                constructorCreateFunction] } ] }

def constructorCreateAccepted : Bool :=
  sourceUnitAccepted? constructorCreateSource

def badConstructorTypeFunction : L00_SourceSolidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeBadType"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.newExpr constructorTargetTy
                [L00_SourceSolidity.Arg.named "seed" (boolExpr true)])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def badConstructorTypeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract constructorTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadCtorMaker"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badConstructorTypeFunction] } ] }

def badConstructorTypeRejected : Bool :=
  Result.isError (SourceUnit.check badConstructorTypeSource)

def missingConstructorArgFunction : L00_SourceSolidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeMissing"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.newExpr constructorTargetTy [])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def missingConstructorArgSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract constructorTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "MissingCtorArgMaker"
            items :=
              [L00_SourceSolidity.ContractItem.function
                missingConstructorArgFunction] } ] }

def missingConstructorArgRejected : Bool :=
  Result.isError (SourceUnit.check missingConstructorArgSource)

def payableConstructorTargetTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "PayableCtorTarget")

def payableConstructorTargetContract : L00_SourceSolidity.ContractDecl :=
  { name := "PayableCtorTarget"
    items :=
      [L00_SourceSolidity.ContractItem.function
        (seedConstructor L00_SourceSolidity.StateMutability.payable)] }

def payableConstructorCreateFunction : L00_SourceSolidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makePayable"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.callWithOptions
                (L00_SourceSolidity.Expr.newExpr
                  payableConstructorTargetTy [])
                [valueOption "1"]
                [L00_SourceSolidity.Arg.named "seed" (numberExpr "7")])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def payableConstructorCreateSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          payableConstructorTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "PayableCtorMaker"
            items :=
              [L00_SourceSolidity.ContractItem.function
                payableConstructorCreateFunction] } ] }

def payableConstructorCreateAccepted : Bool :=
  sourceUnitAccepted? payableConstructorCreateSource

def nonpayableConstructorValueFunction :
    L00_SourceSolidity.FunctionDecl :=
  { payableConstructorCreateFunction with
    name := some "makeNonpayableValue"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.callWithOptions
                (L00_SourceSolidity.Expr.newExpr constructorTargetTy [])
                [valueOption "1"]
                [L00_SourceSolidity.Arg.named "seed" (numberExpr "7")])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def nonpayableConstructorValueSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract constructorTargetContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadValueCtorMaker"
            items :=
              [L00_SourceSolidity.ContractItem.function
                nonpayableConstructorValueFunction] } ] }

def nonpayableConstructorValueRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableConstructorValueSource)

def baseConstructorContract : L00_SourceSolidity.ContractDecl :=
  { name := "CtorBase"
    items :=
      [L00_SourceSolidity.ContractItem.function
        (seedConstructor L00_SourceSolidity.StateMutability.nonpayable)] }

def derivedBaseConstructorGood : L00_SourceSolidity.ContractDecl :=
  { name := "CtorDerived"
    bases :=
      [{ base := userPath "CtorBase"
         args := [L00_SourceSolidity.Arg.positional (numberExpr "4")] }]
    items :=
      [L00_SourceSolidity.ContractItem.function simpleReturnFunction] }

def baseConstructorArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          derivedBaseConstructorGood ] }

def baseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? baseConstructorArgsSource

def namedBaseConstructorContract : L00_SourceSolidity.ContractDecl :=
  { name := "NamedCtorBase"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.constructor
            params :=
              [ { name := some "left"
                  ty := uint256
                  location := none }
              , { name := some "right"
                  ty := uint256
                  location := none } ]
            body := some L00_SourceSolidity.Stmt.empty } ] }

def namedBaseConstructorArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract namedBaseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "NamedCtorDerived"
            bases :=
              [{ base := userPath "NamedCtorBase"
                 args :=
                  [ L00_SourceSolidity.Arg.named "right" (numberExpr "2")
                  , L00_SourceSolidity.Arg.named "left" (numberExpr "1") ] }]
            items :=
              [L00_SourceSolidity.ContractItem.function
                simpleReturnFunction] } ] }

def namedBaseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? namedBaseConstructorArgsSource

def duplicateNamedBaseConstructorArgsSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract namedBaseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateNamedCtorDerived"
            bases :=
              [{ base := userPath "NamedCtorBase"
                 args :=
                  [ L00_SourceSolidity.Arg.named "left" (numberExpr "1")
                  , L00_SourceSolidity.Arg.named "left" (numberExpr "2") ] }]
            items :=
              [L00_SourceSolidity.ContractItem.function
                simpleReturnFunction] } ] }

def duplicateNamedBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check duplicateNamedBaseConstructorArgsSource)

def baseConstructorFileConstantSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "BASE_SEED"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant
            init := some (numberExpr "7") }
      , L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "FileConstantCtorArg"
            bases :=
              [{ base := userPath "CtorBase"
                 args :=
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "BASE_SEED")] }]
            items :=
              [L00_SourceSolidity.ContractItem.function
                simpleReturnFunction] } ] }

def baseConstructorFileConstantAccepted : Bool :=
  sourceUnitAccepted? baseConstructorFileConstantSource

def baseConstructorStateArgSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStateCtorArg"
            bases :=
              [{ base := userPath "CtorBase"
                 args :=
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "seed")] }]
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "seed"
                    ty := uint256
                    init := some (numberExpr "7") }
              , L00_SourceSolidity.ContractItem.function
                  simpleReturnFunction ] } ] }

def baseConstructorStateArgRejected : Bool :=
  Result.isError (SourceUnit.check baseConstructorStateArgSource)

def derivedBaseConstructorBad : L00_SourceSolidity.ContractDecl :=
  { derivedBaseConstructorGood with
    name := "BadCtorDerived"
    bases :=
      [{ base := userPath "CtorBase"
         args := [L00_SourceSolidity.Arg.positional (boolExpr true)] }] }

def badBaseConstructorArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          derivedBaseConstructorBad ] }

def badBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check badBaseConstructorArgsSource)

def derivedBaseConstructorModifierGood :
    L00_SourceSolidity.ContractDecl :=
  { name := "CtorModifierDerived"
    bases := [{ base := userPath "CtorBase" }]
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.constructor
            params :=
              [ { name := some "seed"
                  ty := uint256
                  location := none } ]
            modifiers :=
              [ { target := userPath "CtorBase"
                  args :=
                    [ L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.binary
                          L00_SourceSolidity.BinaryOp.mul
                          (L00_SourceSolidity.Expr.ident "seed")
                          (L00_SourceSolidity.Expr.ident "seed")) ] } ]
            body := some L00_SourceSolidity.Stmt.empty }
      , L00_SourceSolidity.ContractItem.function simpleReturnFunction ] }

def baseConstructorModifierArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          derivedBaseConstructorModifierGood ] }

def baseConstructorModifierArgsAccepted : Bool :=
  sourceUnitAccepted? baseConstructorModifierArgsSource

def derivedBaseConstructorDuplicate :
    L00_SourceSolidity.ContractDecl :=
  { derivedBaseConstructorModifierGood with
    name := "DuplicateCtorArgs"
    bases :=
      [{ base := userPath "CtorBase"
         args := [L00_SourceSolidity.Arg.positional (numberExpr "1")] }] }

def duplicateBaseConstructorArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          derivedBaseConstructorDuplicate ] }

def duplicateBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check duplicateBaseConstructorArgsSource)

def abstractMissingBaseConstructorArgs :
    L00_SourceSolidity.ContractDecl :=
  { name := "AbstractMissingCtorArgs"
    abstract := true
    bases := [{ base := userPath "CtorBase" }]
    items := [] }

def abstractMissingBaseConstructorArgsSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          abstractMissingBaseConstructorArgs ] }

def abstractMissingBaseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? abstractMissingBaseConstructorArgsSource

def concreteMissingBaseConstructorArgs :
    L00_SourceSolidity.ContractDecl :=
  { abstractMissingBaseConstructorArgs with
    name := "ConcreteMissingCtorArgs"
    abstract := false }

def concreteMissingBaseConstructorArgsSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          concreteMissingBaseConstructorArgs ] }

def concreteMissingBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check concreteMissingBaseConstructorArgsSource)

def concreteSuppliesIndirectBaseConstructorArgs :
    L00_SourceSolidity.ContractDecl :=
  { name := "ConcreteSuppliesIndirectCtorArgs"
    bases := [{ base := userPath "AbstractMissingCtorArgs" }]
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.constructor
            params := []
            modifiers :=
              [ { target := userPath "CtorBase"
                  args :=
                    [ L00_SourceSolidity.Arg.positional
                        (numberExpr "10") ] } ]
            body := some L00_SourceSolidity.Stmt.empty }
      , L00_SourceSolidity.ContractItem.function simpleReturnFunction ] }

def indirectBaseConstructorModifierArgsSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          abstractMissingBaseConstructorArgs
      , L00_SourceSolidity.SourceItem.contract
          concreteSuppliesIndirectBaseConstructorArgs ] }

def indirectBaseConstructorModifierArgsAccepted : Bool :=
  sourceUnitAccepted? indirectBaseConstructorModifierArgsSource

def nonconstructorBaseConstructorInvocation :
    L00_SourceSolidity.ContractDecl :=
  { name := "NonconstructorBaseInvocation"
    bases :=
      [{ base := userPath "CtorBase"
         args := [L00_SourceSolidity.Arg.positional (numberExpr "1")] }]
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { simpleReturnFunction with
            modifiers :=
              [ { target := userPath "CtorBase"
                  args := [L00_SourceSolidity.Arg.positional
                    (numberExpr "2")] } ] } ] }

def nonconstructorBaseConstructorInvocationSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseConstructorContract
      , L00_SourceSolidity.SourceItem.contract
          nonconstructorBaseConstructorInvocation ] }

def nonconstructorBaseConstructorInvocationRejected : Bool :=
  Result.isError
    (SourceUnit.check nonconstructorBaseConstructorInvocationSource)

def newStructSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct pairStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "NewStruct"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badNewStruct"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.newExpr pairTy
                                [ L00_SourceSolidity.Arg.positional
                                    (numberExpr "1")
                                , L00_SourceSolidity.Arg.positional
                                    (numberExpr "2") ])
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def newStructRejected : Bool :=
  Result.isError (SourceUnit.check newStructSource)

def payableReturnFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "payMe"
    mutability := L00_SourceSolidity.StateMutability.payable }

def payableValueCaller : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callPayable"
    mutability := L00_SourceSolidity.StateMutability.payable
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.callWithOptions
              (L00_SourceSolidity.Expr.ident "payMe")
              [valueOption "1"] []))) }

def payableValueCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PayableValueCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function payableReturnFunction
              , L00_SourceSolidity.ContractItem.function payableValueCaller ] } ] }

def payableInternalValueCallRejected : Bool :=
  Result.isError (SourceUnit.check payableValueCallSource)

def nonpayableValueCaller : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callNonpayable"
    mutability := L00_SourceSolidity.StateMutability.payable
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.callWithOptions
              (L00_SourceSolidity.Expr.ident "f")
              [valueOption "1"] []))) }

def nonpayableValueCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonpayableValueCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function simpleReturnFunction
              , L00_SourceSolidity.ContractItem.function
                  nonpayableValueCaller ] } ] }

def nonpayableValueCallRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableValueCallSource)

def pingEvent : L00_SourceSolidity.EventDecl :=
  { name := "Ping"
    params := [{ name := some "value", ty := uint256, indexed := false }] }

def boomError : L00_SourceSolidity.ErrorDecl :=
  { name := "Boom"
    params :=
      [{ name := some "value", ty := uint256, location := none }] }

def reservedErrorDecl : L00_SourceSolidity.ErrorDecl :=
  { name := "Error"
    params :=
      [ { name := some "reason"
          ty := L00_SourceSolidity.Ty.string
          location := none } ] }

def reservedErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ReservedError"
            items :=
              [L00_SourceSolidity.ContractItem.errorDecl
                reservedErrorDecl] } ] }

def reservedErrorRejected : Bool :=
  Result.isError (SourceUnit.check reservedErrorSource)

def reservedPanicSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ReservedPanic"
            items :=
              [ L00_SourceSolidity.ContractItem.errorDecl
                  { name := "Panic"
                    params :=
                      [ { name := some "code"
                          ty := uint256
                          location := none } ] } ] } ] }

def reservedPanicRejected : Bool :=
  Result.isError (SourceUnit.check reservedPanicSource)

def emitPingFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emitPing"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.emitEvent
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "Ping")
                [L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "1"))])
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "1"))) ]) }

def emitPingSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "EmitPing"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl pingEvent
              , L00_SourceSolidity.ContractItem.function emitPingFunction ] } ] }

def emitPingAccepted : Bool :=
  sourceUnitAccepted? emitPingSource

def overloadedAddressPingEvent : L00_SourceSolidity.EventDecl :=
  { name := "Ping"
    params :=
      [ { name := some "value"
          ty := L00_SourceSolidity.Ty.address false
          indexed := false } ] }

def overloadedEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "OverloadedEvents"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl pingEvent
              , L00_SourceSolidity.ContractItem.eventDecl
                  overloadedAddressPingEvent ] } ] }

def overloadedEventAccepted : Bool :=
  sourceUnitAccepted? overloadedEventSource

def duplicateCanonicalPingEvent : L00_SourceSolidity.EventDecl :=
  { name := "Ping"
    params := [{ name := some "other", ty := uint256, indexed := false }] }

def duplicateEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateEvent"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl pingEvent
              , L00_SourceSolidity.ContractItem.eventDecl
                  duplicateCanonicalPingEvent ] } ] }

def duplicateEventRejected : Bool :=
  Result.isError (SourceUnit.check duplicateEventSource)

def indexedUintEventParam (name : Name) : L00_SourceSolidity.EventParam :=
  { name := some name, ty := uint256, indexed := true }

def threeIndexedEvent : L00_SourceSolidity.EventDecl :=
  { name := "ThreeIndexed"
    params :=
      [ indexedUintEventParam "a"
      , indexedUintEventParam "b"
      , indexedUintEventParam "c" ] }

def threeIndexedEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ThreeIndexedEvent"
            items := [L00_SourceSolidity.ContractItem.eventDecl
              threeIndexedEvent] } ] }

def threeIndexedEventAccepted : Bool :=
  sourceUnitAccepted? threeIndexedEventSource

def fourIndexedEvent : L00_SourceSolidity.EventDecl :=
  { name := "FourIndexed"
    params :=
      [ indexedUintEventParam "a"
      , indexedUintEventParam "b"
      , indexedUintEventParam "c"
      , indexedUintEventParam "d" ] }

def fourIndexedEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FourIndexedEvent"
            items := [L00_SourceSolidity.ContractItem.eventDecl
              fourIndexedEvent] } ] }

def fourIndexedEventRejected : Bool :=
  Result.isError (SourceUnit.check fourIndexedEventSource)

def anonymousFourIndexedEvent : L00_SourceSolidity.EventDecl :=
  { fourIndexedEvent with name := "AnonymousFourIndexed", anonymous := true }

def anonymousFourIndexedEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AnonymousFourIndexedEvent"
            items := [L00_SourceSolidity.ContractItem.eventDecl
              anonymousFourIndexedEvent] } ] }

def anonymousFourIndexedEventAccepted : Bool :=
  sourceUnitAccepted? anonymousFourIndexedEventSource

def unknownEventSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UnknownEvent"
            items := [L00_SourceSolidity.ContractItem.function
              emitPingFunction] } ] }

def unknownEventRejected : Bool :=
  Result.isError (SourceUnit.check unknownEventSource)

def revertBoomFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertBoom"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.revertCall
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "Boom")
                [L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "1"))])
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "1"))) ]) }

def revertBoomSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError boomError
      , L00_SourceSolidity.SourceItem.contract
          { name := "RevertBoom"
            items := [L00_SourceSolidity.ContractItem.function
              revertBoomFunction] } ] }

def revertBoomAccepted : Bool :=
  sourceUnitAccepted? revertBoomSource

def unknownErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UnknownError"
            items := [L00_SourceSolidity.ContractItem.function
              revertBoomFunction] } ] }

def unknownErrorRejected : Bool :=
  Result.isError (SourceUnit.check unknownErrorSource)

def stringError : L00_SourceSolidity.ErrorDecl :=
  { name := "StringBoom"
    params :=
      [{ name := some "reason"
         ty := L00_SourceSolidity.Ty.string
         location := none }] }

def revertStringErrorFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertStringBoom"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.revertCall
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "StringBoom")
                [L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.string "bad"))])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def revertStringErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError stringError
      , L00_SourceSolidity.SourceItem.contract
          { name := "RevertStringBoom"
            items := [L00_SourceSolidity.ContractItem.function
              revertStringErrorFunction] } ] }

def revertStringErrorAccepted : Bool :=
  sourceUnitAccepted? revertStringErrorSource

def pairNamedEvent : L00_SourceSolidity.EventDecl :=
  { name := "PairSeen"
    params :=
      [ { name := some "left", ty := uint256, indexed := false }
      , { name := some "right", ty := uint256, indexed := false } ] }

def emitPairNamedFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emitPairNamed"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.emitEvent
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "PairSeen")
                [ L00_SourceSolidity.Arg.named "right" (numberExpr "2")
                , L00_SourceSolidity.Arg.named "left" (numberExpr "40") ])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def emitPairNamedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "EmitPairNamed"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl pairNamedEvent
              , L00_SourceSolidity.ContractItem.function
                  emitPairNamedFunction ] } ] }

def emitPairNamedAccepted : Bool :=
  sourceUnitAccepted? emitPairNamedSource

def pairNamedError : L00_SourceSolidity.ErrorDecl :=
  { name := "PairBad"
    params :=
      [ { name := some "left", ty := uint256, location := none }
      , { name := some "right", ty := uint256, location := none } ] }

def revertPairNamedFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertPairNamed"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.revertCall
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "PairBad")
                [ L00_SourceSolidity.Arg.named "right" (numberExpr "2")
                , L00_SourceSolidity.Arg.named "left" (numberExpr "40") ])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def revertPairNamedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError pairNamedError
      , L00_SourceSolidity.SourceItem.contract
          { name := "RevertPairNamed"
            items := [L00_SourceSolidity.ContractItem.function
              revertPairNamedFunction] } ] }

def revertPairNamedAccepted : Bool :=
  sourceUnitAccepted? revertPairNamedSource

def requirePairNamedFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "requirePairNamed"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.ident "require")
                [ L00_SourceSolidity.Arg.positional (boolExpr false)
                , L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.ident "PairBad")
                      [ L00_SourceSolidity.Arg.named "right" (numberExpr "2")
                      , L00_SourceSolidity.Arg.named "left"
                          (numberExpr "40") ]) ])
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def requirePairNamedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError pairNamedError
      , L00_SourceSolidity.SourceItem.contract
          { name := "RequirePairNamed"
            items := [L00_SourceSolidity.ContractItem.function
              requirePairNamedFunction] } ] }

def requirePairNamedAccepted : Bool :=
  sourceUnitAccepted? requirePairNamedSource

def stringErrorWithLocationSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeError
          { stringError with
            params :=
              [ { name := some "reason"
                  ty := L00_SourceSolidity.Ty.string
                  location :=
                    some L00_SourceSolidity.DataLocation.memory } ] } ] }

def stringErrorWithLocationRejected : Bool :=
  Result.isError (SourceUnit.check stringErrorWithLocationSource)

def namedTargetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "target"
    params :=
      [ { name := some "a", ty := uint256, location := none }
      , { name := some "flag"
          ty := L00_SourceSolidity.Ty.bool
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "a"))) }

def namedCallerFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callNamed"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "target")
              [ L00_SourceSolidity.Arg.named "flag"
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.bool true))
              , L00_SourceSolidity.Arg.named "a"
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "3")) ]))) }

def namedArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NamedArgs"
            items :=
              [ L00_SourceSolidity.ContractItem.function namedTargetFunction
              , L00_SourceSolidity.ContractItem.function
                  namedCallerFunction ] } ] }

def namedArgsAccepted : Bool :=
  sourceUnitAccepted? namedArgsSource

def badNamedCallerFunction : L00_SourceSolidity.FunctionDecl :=
  { namedCallerFunction with
    name := some "badNamed"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "target")
              [ L00_SourceSolidity.Arg.named "missing"
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.bool true))
              , L00_SourceSolidity.Arg.named "a"
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "3")) ]))) }

def badNamedArgsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadNamedArgs"
            items :=
              [ L00_SourceSolidity.ContractItem.function namedTargetFunction
              , L00_SourceSolidity.ContractItem.function
                  badNamedCallerFunction ] } ] }

def badNamedArgsRejected : Bool :=
  Result.isError (SourceUnit.check badNamedArgsSource)

def interfaceFunctionDecl : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "read"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.view
    body := none }

def interfaceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IReader"
            items := [L00_SourceSolidity.ContractItem.function
              interfaceFunctionDecl] } ] }

def interfaceAccepted : Bool :=
  sourceUnitAccepted? interfaceSource

def badInterfaceBodySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IBad"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { interfaceFunctionDecl with
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.literal
                              (L00_SourceSolidity.Literal.number "1")))) } ] } ] }

def badInterfaceBodyRejected : Bool :=
  Result.isError (SourceUnit.check badInterfaceBodySource)

def abstractInterfaceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IAbstract"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.function
              interfaceFunctionDecl] } ] }

def abstractInterfaceRejected : Bool :=
  Result.isError (SourceUnit.check abstractInterfaceSource)

def unimplementedFunctionDecl : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with body := none, virtual := true }

def nonAbstractMissingBodySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MissingImpl"
            items := [L00_SourceSolidity.ContractItem.function
              unimplementedFunctionDecl] } ] }

def nonAbstractMissingBodyRejected : Bool :=
  Result.isError (SourceUnit.check nonAbstractMissingBodySource)

def abstractMissingBodySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractMissingImpl"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.function
              unimplementedFunctionDecl] } ] }

def abstractMissingBodyAccepted : Bool :=
  sourceUnitAccepted? abstractMissingBodySource

def inheritedAbstractFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractFunctionBase"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.function
              unimplementedFunctionDecl] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritsAbstractFunction"
            bases := [{ base := userPath "AbstractFunctionBase" }] } ] }

def inheritedAbstractFunctionRejected : Bool :=
  Result.isError (SourceUnit.check inheritedAbstractFunctionSource)

def abstractInheritsAbstractFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractFunctionBase2"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.function
              unimplementedFunctionDecl] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "AbstractInheritsAbstractFunction"
            abstract := true
            bases := [{ base := userPath "AbstractFunctionBase2" }] } ] }

def abstractInheritsAbstractFunctionAccepted : Bool :=
  sourceUnitAccepted? abstractInheritsAbstractFunctionSource

def inheritedInterfaceFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IInheritedReader"
            items := [L00_SourceSolidity.ContractItem.function
              interfaceFunctionDecl] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritsInterfaceFunction"
            bases := [{ base := userPath "IInheritedReader" }] } ] }

def inheritedInterfaceFunctionRejected : Bool :=
  Result.isError (SourceUnit.check inheritedInterfaceFunctionSource)

def implementedInterfaceFunction : L00_SourceSolidity.FunctionDecl :=
  { interfaceFunctionDecl with
    body := some (L00_SourceSolidity.Stmt.returnValues
      (some (numberExpr "1"))) }

def implementedInterfaceFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IImplementedReader"
            items := [L00_SourceSolidity.ContractItem.function
              interfaceFunctionDecl] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ImplementsInterfaceFunction"
            bases := [{ base := userPath "IImplementedReader" }]
            items := [L00_SourceSolidity.ContractItem.function
              implementedInterfaceFunction] } ] }

def implementedInterfaceFunctionAccepted : Bool :=
  sourceUnitAccepted? implementedInterfaceFunctionSource

def bodylessVirtualModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "guard"
    virtual := true
    body := none }

def abstractBodylessModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractBodylessModifier"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              bodylessVirtualModifier] } ] }

def abstractBodylessModifierAccepted : Bool :=
  sourceUnitAccepted? abstractBodylessModifierSource

def abstractBodylessModifierNoVirtualSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractBodylessModifierNoVirtual"
            abstract := true
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  { bodylessVirtualModifier with virtual := false } ] } ] }

def abstractBodylessModifierNoVirtualRejected : Bool :=
  Result.isError (SourceUnit.check
    abstractBodylessModifierNoVirtualSource)

def nonAbstractBodylessModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonAbstractBodylessModifier"
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              bodylessVirtualModifier] } ] }

def nonAbstractBodylessModifierRejected : Bool :=
  Result.isError (SourceUnit.check nonAbstractBodylessModifierSource)

def inheritedAbstractModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractModifierBase"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritsAbstractModifier"
            bases := [{ base := userPath "AbstractModifierBase" }] } ] }

def inheritedAbstractModifierRejected : Bool :=
  Result.isError (SourceUnit.check inheritedAbstractModifierSource)

def abstractInheritsAbstractModifierSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractModifierBase2"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "AbstractInheritsAbstractModifier"
            abstract := true
            bases := [{ base := userPath "AbstractModifierBase2" }] } ] }

def abstractInheritsAbstractModifierAccepted : Bool :=
  sourceUnitAccepted? abstractInheritsAbstractModifierSource

def implementedAbstractModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractModifierBase3"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ImplementsAbstractModifier"
            bases := [{ base := userPath "AbstractModifierBase3" }]
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  { bodylessVirtualModifier with
                    override? := some { bases := [] }
                    body :=
                      some L00_SourceSolidity.Stmt.modifierPlaceholder } ] } ] }

def implementedAbstractModifierAccepted : Bool :=
  sourceUnitAccepted? implementedAbstractModifierSource

def libraryStateVarSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.library
            name := "BadLibrary"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x", ty := uint256 } ] } ] }

def libraryStateVarRejected : Bool :=
  Result.isError (SourceUnit.check libraryStateVarSource)

def emptyLibraryContract : L00_SourceSolidity.ContractDecl :=
  { kind := L00_SourceSolidity.ContractKind.library
    name := "Lib"
    items := [] }

def usingKnownLibrarySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract emptyLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "Lib"
            target := some uint256 }
      , L00_SourceSolidity.SourceItem.contract
          { name := "UsesLib", items := [] } ] }

def usingKnownLibraryAccepted : Bool :=
  sourceUnitAccepted? usingKnownLibrarySource

def usingUnknownLibrarySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "MissingLib"
            target := some uint256 } ] }

def usingUnknownLibraryRejected : Bool :=
  Result.isError (SourceUnit.check usingUnknownLibrarySource)

def usingNonLibrarySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NotALibrary", items := [] }
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "NotALibrary"
            target := some uint256 } ] }

def usingNonLibraryRejected : Bool :=
  Result.isError (SourceUnit.check usingNonLibrarySource)

def usingFileWildcardSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract emptyLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "Lib" } ] }

def usingFileWildcardRejected : Bool :=
  Result.isError (SourceUnit.check usingFileWildcardSource)

def uintLibraryPlusOne : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "plusOne"
    params := [{ name := some "self", ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.public_
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.add
              (L00_SourceSolidity.Expr.ident "self")
              (numberExpr "1")))) }

def uintLibraryContract : L00_SourceSolidity.ContractDecl :=
  { kind := L00_SourceSolidity.ContractKind.library
    name := "UintLib"
    items := [L00_SourceSolidity.ContractItem.function
      uintLibraryPlusOne] }

def directLibraryCallFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "directLibrary"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "UintLib") "plusOne")
              [L00_SourceSolidity.Arg.positional (numberExpr "3")]))) }

def directLibraryCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract uintLibraryContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "DirectLibrary"
            items := [L00_SourceSolidity.ContractItem.function
              directLibraryCallFunction] } ] }

def directLibraryCallAccepted : Bool :=
  sourceUnitAccepted? directLibraryCallSource

def usingLibraryMethodFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingLibrary"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member (numberExpr "3") "plusOne")
              []))) }

def usingLibraryMethodSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract uintLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "UintLib"
            target := some uint256 }
      , L00_SourceSolidity.SourceItem.contract
          { name := "UsingLibrary"
            items := [L00_SourceSolidity.ContractItem.function
              usingLibraryMethodFunction] } ] }

def usingLibraryMethodAccepted : Bool :=
  sourceUnitAccepted? usingLibraryMethodSource

def explicitUsingLibraryMethodSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract uintLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["UintLib", "plusOne"] } }]
            target := some uint256 }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ExplicitUsingLibrary"
            items := [L00_SourceSolidity.ContractItem.function
              usingLibraryMethodFunction] } ] }

def explicitUsingLibraryMethodAccepted : Bool :=
  sourceUnitAccepted? explicitUsingLibraryMethodSource

def freeUsingPlusOneFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "freeInc"
    params := [{ name := some "self", ty := uint256, location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.add
              (L00_SourceSolidity.Expr.ident "self")
              (numberExpr "1")))) }

def usingFreeFunctionMethodFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingFreeFunction"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member (numberExpr "3") "freeInc")
              []))) }

def explicitUsingFreeFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeFunction
          freeUsingPlusOneFunction
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["freeInc"] } }]
            target := some uint256 }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ExplicitUsingFree"
            items := [L00_SourceSolidity.ContractItem.function
              usingFreeFunctionMethodFunction] } ] }

def explicitUsingFreeFunctionAccepted : Bool :=
  sourceUnitAccepted? explicitUsingFreeFunctionSource

def usingHigherOrderInternalFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [uint256] [uint256]
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.internal_

def usingHigherOrderLibraryApply :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "apply"
    visibility := some L00_SourceSolidity.Visibility.internal_
    mutability := L00_SourceSolidity.StateMutability.pure
    params :=
      [ { name := some "self", ty := uint256, location := none }
      , { name := some "fn"
          ty := usingHigherOrderInternalFunctionTy
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "fn")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "self")]))) }

def usingHigherOrderLibrary : L00_SourceSolidity.ContractDecl :=
  { kind := L00_SourceSolidity.ContractKind.library
    name := "Apply"
    items :=
      [L00_SourceSolidity.ContractItem.function
        usingHigherOrderLibraryApply] }

def usingHigherOrderDouble :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "double"
    visibility := some L00_SourceSolidity.Visibility.internal_
    mutability := L00_SourceSolidity.StateMutability.pure
    params := [{ name := some "x", ty := uint256, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.mul
              (L00_SourceSolidity.Expr.ident "x")
              (numberExpr "2")))) }

def usingHigherOrderDoubleOverload :
    L00_SourceSolidity.FunctionDecl :=
  { usingHigherOrderDouble with
    params :=
      [ { name := some "x", ty := uint256, location := none }
      , { name := some "y", ty := uint256, location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "x"))) }

def usingHigherOrderFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingHigherOrder"
    mutability := L00_SourceSolidity.StateMutability.pure
    params := [{ name := some "x", ty := uint256, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "x") "apply")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "double")]))) }

def usingHigherOrderFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract usingHigherOrderLibrary
      , L00_SourceSolidity.SourceItem.contract
          { name := "UsingHigherOrder"
            items :=
              [ L00_SourceSolidity.ContractItem.usingDecl
                  { library := userPath "Apply"
                    target := some uint256 }
              , L00_SourceSolidity.ContractItem.function
                  usingHigherOrderDoubleOverload
              , L00_SourceSolidity.ContractItem.function
                  usingHigherOrderDouble
              , L00_SourceSolidity.ContractItem.function
                  usingHigherOrderFunction ] } ] }

def usingHigherOrderFunctionAccepted : Bool :=
  sourceUnitAccepted? usingHigherOrderFunctionSource

def badExplicitUsingFreeFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["missingFree"] } }]
            target := some uint256 } ] }

def badExplicitUsingFreeFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitUsingFreeFunctionSource)

def badExplicitUsingFunctionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract uintLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["UintLib", "missing"] } }]
            target := some uint256 } ] }

def badExplicitUsingFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitUsingFunctionSource)

def badUsingLibraryReceiverSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract uintLibraryContract
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "UintLib"
            target := some L00_SourceSolidity.Ty.bool }
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadUsingLibrary"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badUsingLibrary"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (boolExpr true) "plusOne")
                              []))) } ] } ] }

def badUsingLibraryReceiverRejected : Bool :=
  Result.isError (SourceUnit.check badUsingLibraryReceiverSource)

def baseContract : L00_SourceSolidity.ContractDecl :=
  { name := "Base"
    items := [L00_SourceSolidity.ContractItem.function
      simpleReturnFunction] }

def derivedContract : L00_SourceSolidity.ContractDecl :=
  { name := "Derived"
    bases := [{ base := userPath "Base", args := [] }]
    items := [] }

def inheritanceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseContract
      , L00_SourceSolidity.SourceItem.contract derivedContract ] }

def inheritanceAccepted : Bool :=
  sourceUnitAccepted? inheritanceSource

def stateShadowBaseContract : L00_SourceSolidity.ContractDecl :=
  { name := "StateShadowBase"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            visibility := some L00_SourceSolidity.Visibility.internal_ } ] }

def stateShadowDerivedContract : L00_SourceSolidity.ContractDecl :=
  { name := "StateShadowDerived"
    bases := [{ base := userPath "StateShadowBase" }]
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := uint256 } ] }

def stateVariableShadowingSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract stateShadowBaseContract
      , L00_SourceSolidity.SourceItem.contract
          stateShadowDerivedContract ] }

def stateVariableShadowingRejected : Bool :=
  Result.isError (SourceUnit.check stateVariableShadowingSource)

def privateStateShadowBaseContract : L00_SourceSolidity.ContractDecl :=
  { name := "PrivateStateShadowBase"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            visibility := some L00_SourceSolidity.Visibility.private_ } ] }

def privateStateShadowDerivedContract : L00_SourceSolidity.ContractDecl :=
  { name := "PrivateStateShadowDerived"
    bases := [{ base := userPath "PrivateStateShadowBase" }]
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x", ty := uint256 } ] }

def privateStateVariableShadowingSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract privateStateShadowBaseContract
      , L00_SourceSolidity.SourceItem.contract
          privateStateShadowDerivedContract ] }

def privateStateVariableShadowingAccepted : Bool :=
  sourceUnitAccepted? privateStateVariableShadowingSource

def inheritedStateReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InheritedStateBase"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritedStateDerived"
            bases := [{ base := userPath "InheritedStateBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "read"
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "x"))) } ] } ] }

def inheritedStateReadAccepted : Bool :=
  sourceUnitAccepted? inheritedStateReadSource

def privateInheritedStateReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PrivateInheritedStateBase"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    visibility :=
                      some L00_SourceSolidity.Visibility.private_
                    init := some (numberExpr "1") } ] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "PrivateInheritedStateDerived"
            bases := [{ base := userPath "PrivateInheritedStateBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "read"
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.ident "x"))) } ] } ] }

def privateInheritedStateReadRejected : Bool :=
  Result.isError (SourceUnit.check privateInheritedStateReadSource)

def superBaseFunctionContract : L00_SourceSolidity.ContractDecl :=
  { name := "SuperTypeBase"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.function
            name := some "setX"
            params := []
            returns := []
            visibility := some L00_SourceSolidity.Visibility.public_
            mutability := L00_SourceSolidity.StateMutability.nonpayable
            body := some L00_SourceSolidity.Stmt.empty }
      , L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.function
            name := some "value"
            params := []
            returns := [{ name := none, ty := uint256, location := none }]
            visibility := some L00_SourceSolidity.Visibility.public_
            mutability := L00_SourceSolidity.StateMutability.view
            virtual := true
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some (numberExpr "1"))) } ] }

def superDerivedFunctionContract : L00_SourceSolidity.ContractDecl :=
  { name := "SuperTypeDerived"
    bases := [{ base := userPath "SuperTypeBase" }]
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.function
            name := some "setViaSuper"
            params := []
            returns := []
            visibility := some L00_SourceSolidity.Visibility.public_
            mutability := L00_SourceSolidity.StateMutability.nonpayable
            body :=
              some
                (L00_SourceSolidity.Stmt.expr
                  (L00_SourceSolidity.Expr.call
                    (L00_SourceSolidity.Expr.member
                      (L00_SourceSolidity.Expr.ident "super") "setX")
                    [])) }
      , L00_SourceSolidity.ContractItem.function
          { kind := L00_SourceSolidity.FunctionKind.function
            name := some "value"
            params := []
            returns := [{ name := none, ty := uint256, location := none }]
            visibility := some L00_SourceSolidity.Visibility.public_
            mutability := L00_SourceSolidity.StateMutability.view
            override? := some {}
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.binary
                      L00_SourceSolidity.BinaryOp.add
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.ident "super") "value")
                        [])
                      (numberExpr "2")))) } ] }

def superCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract superBaseFunctionContract
      , L00_SourceSolidity.SourceItem.contract
          superDerivedFunctionContract ] }

def superCallAccepted : Bool :=
  sourceUnitAccepted? superCallSource

def badSuperCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract superBaseFunctionContract
      , L00_SourceSolidity.SourceItem.contract
          { superDerivedFunctionContract with
            name := "BadSuperTypeDerived"
            bases := [{ base := userPath "SuperTypeBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSuper"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "super")
                                "missing")
                              []))) } ] } ] }

def badSuperCallRejected : Bool :=
  Result.isError (SourceUnit.check badSuperCallSource)

def superCallOptionsSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract superBaseFunctionContract
      , L00_SourceSolidity.SourceItem.contract
          { superDerivedFunctionContract with
            name := "BadSuperOptions"
            bases := [{ base := userPath "SuperTypeBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSuperOptions"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.callWithOptions
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "super")
                                "value")
                              [gasOption "100"]
                              []))) } ] } ] }

def superCallOptionsRejected : Bool :=
  Result.isError (SourceUnit.check superCallOptionsSource)

def explicitBaseValueFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "value"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (numberExpr "11"))) }

def explicitBaseCallBaseContract : L00_SourceSolidity.ContractDecl :=
  { name := "ExplicitBaseTypeBase"
    items :=
      [ L00_SourceSolidity.ContractItem.function
          explicitBaseValueFunction ] }

def explicitBaseCallDerivedContract :
    L00_SourceSolidity.ContractDecl :=
  { name := "ExplicitBaseTypeDerived"
    bases := [{ base := userPath "ExplicitBaseTypeBase" }]
    items :=
      [ L00_SourceSolidity.ContractItem.function
          { simpleReturnFunction with
            name := some "directBase"
            mutability := L00_SourceSolidity.StateMutability.view
            body :=
              some
                (L00_SourceSolidity.Stmt.returnValues
                  (some
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.ident
                          "ExplicitBaseTypeBase")
                        "value")
                      []))) } ] }

def explicitBaseCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          explicitBaseCallBaseContract
      , L00_SourceSolidity.SourceItem.contract
          explicitBaseCallDerivedContract ] }

def explicitBaseCallAccepted : Bool :=
  sourceUnitAccepted? explicitBaseCallSource

def storageLayoutBaseContract : L00_SourceSolidity.ContractDecl :=
  { name := "StorageLayoutBase"
    items :=
      [ L00_SourceSolidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            init := some (numberExpr "1") } ] }

def storageLayoutAcceptedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract storageLayoutBaseContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "StorageLayoutTop"
            layoutBase := some (numberExpr "5")
            bases := [{ base := userPath "StorageLayoutBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "y"
                    ty := uint256
                    init := some (numberExpr "2") } ] } ] }

def storageLayoutAccepted : Bool :=
  sourceUnitAccepted? storageLayoutAcceptedSource

def constantStorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeConstant
          { name := "LAYOUT_SLOT"
            ty := uint256
            mutability := L00_SourceSolidity.VarMutability.constant
            init := some (numberExpr "8") }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ConstantStorageLayout"
            layoutBase :=
              some
                (L00_SourceSolidity.Expr.binary
                  L00_SourceSolidity.BinaryOp.add
                  (L00_SourceSolidity.Expr.ident "LAYOUT_SLOT")
                  (numberExpr "1"))
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def constantStorageLayoutAccepted : Bool :=
  sourceUnitAccepted? constantStorageLayoutSource

def unknownConstantStorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "UnknownConstantStorageLayout"
            layoutBase := some (L00_SourceSolidity.Expr.ident "MISSING")
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def unknownConstantStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check unknownConstantStorageLayoutSource)

def erc7201StorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "Erc7201StorageLayout"
            layoutBase :=
              some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "erc7201")
                  [ L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.string
                          "example.main")) ])
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def erc7201StorageLayoutAccepted : Bool :=
  sourceUnitAccepted? erc7201StorageLayoutSource

def badErc7201StorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadErc7201StorageLayout"
            layoutBase :=
              some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "erc7201")
                  [L00_SourceSolidity.Arg.positional (numberExpr "1")])
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def badErc7201StorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check badErc7201StorageLayoutSource)

def badKeccakStorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadKeccakStorageLayout"
            layoutBase :=
              some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "keccak256")
                  [ L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.literal
                        (L00_SourceSolidity.Literal.string
                          "example.main")) ])
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def badKeccakStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check badKeccakStorageLayoutSource)

def inheritedStorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { storageLayoutBaseContract with
            name := "InheritedLayoutBase"
            layoutBase := some (numberExpr "3") }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritedLayoutChild"
            bases := [{ base := userPath "InheritedLayoutBase" }]
            items :=
              [L00_SourceSolidity.ContractItem.function
                simpleReturnFunction] } ] }

def inheritedStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check inheritedStorageLayoutSource)

def abstractStorageLayoutSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractStorageLayout"
            abstract := true
            layoutBase := some (numberExpr "5")
            items := [] } ] }

def abstractStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check abstractStorageLayoutSource)

def mutableStorageLayoutBaseSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MutableStorageLayoutBase"
            layoutBase := some (L00_SourceSolidity.Expr.ident "x")
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def mutableStorageLayoutBaseRejected : Bool :=
  Result.isError (SourceUnit.check mutableStorageLayoutBaseSource)

def badExplicitBaseCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          explicitBaseCallBaseContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "NotAnExplicitBase"
            items := [L00_SourceSolidity.ContractItem.function
              explicitBaseValueFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { explicitBaseCallDerivedContract with
            name := "BadExplicitBaseTypeDerived"
            bases := [{ base := userPath "ExplicitBaseTypeBase" }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badDirectBase"
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident
                                  "NotAnExplicitBase")
                                "value")
                              []))) } ] } ] }

def badExplicitBaseCallRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitBaseCallSource)

def contractUpcastFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "upcast"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "b"
                  ty := some
                    (L00_SourceSolidity.Ty.user (userPath "Base"))
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "d"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def contractUpcastSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract baseContract
      , L00_SourceSolidity.SourceItem.contract derivedContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "ContractUpcast"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "d"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "Derived") }
              , L00_SourceSolidity.ContractItem.function
                  contractUpcastFunction ] } ] }

def contractUpcastAccepted : Bool :=
  sourceUnitAccepted? contractUpcastSource

def unknownBaseSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DerivedMissing"
            bases := [{ base := userPath "MissingBase", args := [] }]
            items := [] } ] }

def unknownBaseRejected : Bool :=
  Result.isError (SourceUnit.check unknownBaseSource)

def virtualBaseFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "value"
    virtual := true }

def overrideValueFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "value"
    override? := some { bases := [] }
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.literal
              (L00_SourceSolidity.Literal.number "2")))) }

def virtualOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "VirtualBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualBaseFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "VirtualDerived"
            bases := [{ base := userPath "VirtualBase", args := [] }]
            items := [L00_SourceSolidity.ContractItem.function
              overrideValueFunction] } ] }

def virtualOverrideAccepted : Bool :=
  sourceUnitAccepted? virtualOverrideSource

def missingOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MissingOverrideBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualBaseFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "MissingOverrideDerived"
            bases :=
              [{ base := userPath "MissingOverrideBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { overrideValueFunction with override? := none } ] } ] }

def missingOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingOverrideSource)

def nonvirtualOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonvirtualBase"
            items := [L00_SourceSolidity.ContractItem.function
              simpleReturnFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "NonvirtualDerived"
            bases := [{ base := userPath "NonvirtualBase", args := [] }]
            items := [L00_SourceSolidity.ContractItem.function
              overrideValueFunction] } ] }

def nonvirtualOverrideRejected : Bool :=
  Result.isError (SourceUnit.check nonvirtualOverrideSource)

def externalVirtualValueFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.function
    name := some "value"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.view
    virtual := true
    body := none }

def publicOverrideOfExternalSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ExternalBase"
            abstract := true
            items := [L00_SourceSolidity.ContractItem.function
              externalVirtualValueFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicDerived"
            bases := [{ base := userPath "ExternalBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { overrideValueFunction with
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    mutability :=
                      L00_SourceSolidity.StateMutability.pure } ] } ] }

def publicOverrideOfExternalAccepted : Bool :=
  sourceUnitAccepted? publicOverrideOfExternalSource

def publicGetterOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { kind := L00_SourceSolidity.ContractKind.interface
            name := "IValue"
            items := [L00_SourceSolidity.ContractItem.function
              externalVirtualValueFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "GetterOverride"
            bases := [{ base := userPath "IValue", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "value"
                    ty := uint256
                    visibility := some L00_SourceSolidity.Visibility.public_
                    override? := some { bases := [] } } ] } ] }

def publicGetterOverrideAccepted : Bool :=
  sourceUnitAccepted? publicGetterOverrideSource

def calleeGetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "get"
    params := [{ name := some "key", ty := uint256, location := none }]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "key"))) }

def calleeSetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "set"
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.nonpayable }

def calleePayFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pay"
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.payable }

def calleeContract : L00_SourceSolidity.ContractDecl :=
  { name := "Callee"
    items :=
      [ L00_SourceSolidity.ContractItem.function calleeGetFunction
      , L00_SourceSolidity.ContractItem.function calleeSetFunction
      , L00_SourceSolidity.ContractItem.function calleePayFunction ] }

def calleeTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Callee")

def externalMemberCallFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readRemote"
    params := [{ name := some "target", ty := calleeTy, location := none }]
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "target") "get")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "7")) ]))) }

def externalMemberCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract calleeContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "ExternalMemberCaller"
            items := [L00_SourceSolidity.ContractItem.function
              externalMemberCallFunction] } ] }

def externalMemberCallAccepted : Bool :=
  sourceUnitAccepted? externalMemberCallSource

def bareExternalCallFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badBareExternal"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "get")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "7")) ]))) }

def bareExternalCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BareExternalCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function calleeGetFunction
              , L00_SourceSolidity.ContractItem.function
                  bareExternalCallFunction ] } ] }

def bareExternalCallRejected : Bool :=
  Result.isError (SourceUnit.check bareExternalCallSource)

def viewCallsNonpayableExternalSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract calleeContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "ViewCallsNonpayableExternal"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badRemoteWrite"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "target")
                                "set")
                              []))) } ] } ] }

def viewCallsNonpayableExternalRejected : Bool :=
  Result.isError (SourceUnit.check viewCallsNonpayableExternalSource)

def valueCallToNonpayableExternalSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract calleeContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "ValueCallsNonpayableExternal"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badValueRemote"
                    mutability := L00_SourceSolidity.StateMutability.payable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.callWithOptions
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "target")
                                "get")
                              [valueOption "1"]
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.number
                                      "7")) ]))) } ] } ] }

def valueCallToNonpayableExternalRejected : Bool :=
  Result.isError (SourceUnit.check valueCallToNonpayableExternalSource)

def valueCallToPayableExternalSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract calleeContract
      , L00_SourceSolidity.SourceItem.contract
          { name := "ValueCallsPayableExternal"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "payRemote"
                    mutability := L00_SourceSolidity.StateMutability.payable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.callWithOptions
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "target")
                                "pay")
                              [valueOption "1"] []))) } ] } ] }

def valueCallToPayableExternalAccepted : Bool :=
  sourceUnitAccepted? valueCallToPayableExternalSource

def lowLevelSendFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sendIt"
    params :=
      [ { name := some "target"
          ty := L00_SourceSolidity.Ty.address true
          location := none } ]
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.bool
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "target") "send")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.literal
                    (L00_SourceSolidity.Literal.number "1")) ]))) }

def lowLevelSendSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "LowLevelSend"
            items := [L00_SourceSolidity.ContractItem.function
              lowLevelSendFunction] } ] }

def lowLevelSendAccepted : Bool :=
  sourceUnitAccepted? lowLevelSendSource

def lowLevelSendNonpayableAddressSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadLowLevelSend"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { lowLevelSendFunction with
                    params :=
                      [ { name := some "target"
                          ty := L00_SourceSolidity.Ty.address false
                          location := none } ] } ] } ] }

def lowLevelSendNonpayableAddressRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelSendNonpayableAddressSource)

def selfdestructFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "bye"
    visibility := some L00_SourceSolidity.Visibility.public_
    params :=
      [ { name := some "target"
          ty := L00_SourceSolidity.Ty.address true
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.expr
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "selfdestruct")
            [ L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "target") ])) }

def selfdestructSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "SelfdestructUse"
            items :=
              [L00_SourceSolidity.ContractItem.function
                selfdestructFunction] } ] }

def selfdestructAccepted : Bool :=
  sourceUnitAccepted? selfdestructSource

def selfdestructNonpayableAddressSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadSelfdestructTarget"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { selfdestructFunction with
                    params :=
                      [ { name := some "target"
                          ty := L00_SourceSolidity.Ty.address false
                          location := none } ] } ] } ] }

def selfdestructNonpayableAddressRejected : Bool :=
  Result.isError (SourceUnit.check selfdestructNonpayableAddressSource)

def selfdestructViewSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadSelfdestructView"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { selfdestructFunction with
                    mutability :=
                      L00_SourceSolidity.StateMutability.view } ] } ] }

def selfdestructViewRejected : Bool :=
  Result.isError (SourceUnit.check selfdestructViewSource)

def c3XContract : L00_SourceSolidity.ContractDecl :=
  { name := "C3X" }

def c3AContract : L00_SourceSolidity.ContractDecl :=
  { name := "C3A"
    bases := [{ base := userPath "C3X", args := [] }] }

def c3BadContract : L00_SourceSolidity.ContractDecl :=
  { name := "C3Bad"
    bases :=
      [ { base := userPath "C3A", args := [] }
      , { base := userPath "C3X", args := [] } ] }

def c3BadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract c3XContract
      , L00_SourceSolidity.SourceItem.contract c3AContract
      , L00_SourceSolidity.SourceItem.contract c3BadContract ] }

def c3BadRejected : Bool :=
  Result.isError (SourceUnit.check c3BadSource)

def virtualModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "guard"
    virtual := true
    body := some L00_SourceSolidity.Stmt.modifierPlaceholder }

def overrideModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "guard"
    override? := some { bases := [] }
    body := some L00_SourceSolidity.Stmt.modifierPlaceholder }

def modifierOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ModifierBase"
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              virtualModifier] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ModifierDerived"
            bases := [{ base := userPath "ModifierBase", args := [] }]
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              overrideModifier] } ] }

def modifierOverrideAccepted : Bool :=
  sourceUnitAccepted? modifierOverrideSource

def missingModifierOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MissingModifierBase"
            items := [L00_SourceSolidity.ContractItem.modifierDecl
              virtualModifier] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "MissingModifierDerived"
            bases :=
              [{ base := userPath "MissingModifierBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  { overrideModifier with override? := none } ] } ] }

def missingModifierOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingModifierOverrideSource)

def inheritedBaseModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "onlyBase"
    body := some L00_SourceSolidity.Stmt.modifierPlaceholder }

def inheritedModifierFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usesInheritedModifier"
    modifiers := [{ target := userPath "onlyBase", args := [] }] }

def inheritedModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InheritedModifierBase"
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  inheritedBaseModifier ] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "InheritedModifierDerived"
            bases := [{ base := userPath "InheritedModifierBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  inheritedModifierFunction ] } ] }

def inheritedModifierAccepted : Bool :=
  sourceUnitAccepted? inheritedModifierSource

def stateX : L00_SourceSolidity.StateVarDecl :=
  { name := "x", ty := uint256 }

def pureStateReadFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readPure"
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "x"))) }

def pureStateReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureReadsState"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.function
                  pureStateReadFunction ] } ] }

def pureStateReadRejected : Bool :=
  Result.isError (SourceUnit.check pureStateReadSource)

def viewStateReadFunction : L00_SourceSolidity.FunctionDecl :=
  { pureStateReadFunction with
    name := some "readView"
    mutability := L00_SourceSolidity.StateMutability.view }

def viewStateReadSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewReadsState"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.function
                  viewStateReadFunction ] } ] }

def viewStateReadAccepted : Bool :=
  sourceUnitAccepted? viewStateReadSource

def viewStateWriteFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "writeView"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "x")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "2")))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "1"))) ]) }

def viewStateWriteSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewWritesState"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.function
                  viewStateWriteFunction ] } ] }

def viewStateWriteRejected : Bool :=
  Result.isError (SourceUnit.check viewStateWriteSource)

def nonpayableStateWriteFunction : L00_SourceSolidity.FunctionDecl :=
  { viewStateWriteFunction with
    name := some "writeNonpayable"
    mutability := L00_SourceSolidity.StateMutability.nonpayable }

def nonpayableStateWriteSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonpayableWritesState"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.function
                  nonpayableStateWriteFunction ] } ] }

def nonpayableStateWriteAccepted : Bool :=
  sourceUnitAccepted? nonpayableStateWriteSource

def modifierArgFromParam : L00_SourceSolidity.ModifierDecl :=
  { name := "takesValue"
    params := [{ name := some "value", ty := uint256, location := none }]
    body := some L00_SourceSolidity.Stmt.modifierPlaceholder }

def modifierArgFromParamFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "passesParamToModifier"
    params := [{ name := some "v", ty := uint256, location := none }]
    modifiers :=
      [ { target := userPath "takesValue"
          args := [L00_SourceSolidity.Arg.positional
            (L00_SourceSolidity.Expr.ident "v")] } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "v"))) }

def modifierArgFromParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ModifierArgFromParam"
            items :=
              [ L00_SourceSolidity.ContractItem.modifierDecl
                  modifierArgFromParam
              , L00_SourceSolidity.ContractItem.function
                  modifierArgFromParamFunction ] } ] }

def modifierArgFromParamAccepted : Bool :=
  sourceUnitAccepted? modifierArgFromParamSource

def stateReadModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "readsState"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.ident "x")
          , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }

def pureWithStateReadModifierFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pureWithReadModifier"
    mutability := L00_SourceSolidity.StateMutability.pure
    modifiers := [{ target := userPath "readsState", args := [] }] }

def pureWithStateReadModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureWithStateReadModifier"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.modifierDecl
                  stateReadModifier
              , L00_SourceSolidity.ContractItem.function
                  pureWithStateReadModifierFunction ] } ] }

def pureWithStateReadModifierRejected : Bool :=
  Result.isError (SourceUnit.check pureWithStateReadModifierSource)

def viewWithStateReadModifierFunction : L00_SourceSolidity.FunctionDecl :=
  { pureWithStateReadModifierFunction with
    name := some "viewWithReadModifier"
    mutability := L00_SourceSolidity.StateMutability.view }

def viewWithStateReadModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewWithStateReadModifier"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.modifierDecl
                  stateReadModifier
              , L00_SourceSolidity.ContractItem.function
                  viewWithStateReadModifierFunction ] } ] }

def viewWithStateReadModifierAccepted : Bool :=
  sourceUnitAccepted? viewWithStateReadModifierSource

def stateWriteModifier : L00_SourceSolidity.ModifierDecl :=
  { name := "writesState"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "x")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "5")))
          , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }

def viewWithStateWriteModifierFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewWithWriteModifier"
    mutability := L00_SourceSolidity.StateMutability.view
    modifiers := [{ target := userPath "writesState", args := [] }] }

def viewWithStateWriteModifierSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewWithStateWriteModifier"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.modifierDecl
                  stateWriteModifier
              , L00_SourceSolidity.ContractItem.function
                  viewWithStateWriteModifierFunction ] } ] }

def viewWithStateWriteModifierRejected : Bool :=
  Result.isError (SourceUnit.check viewWithStateWriteModifierSource)

def nonpayableWithStateWriteModifierFunction :
    L00_SourceSolidity.FunctionDecl :=
  { viewWithStateWriteModifierFunction with
    name := some "nonpayableWithWriteModifier"
    mutability := L00_SourceSolidity.StateMutability.nonpayable }

def nonpayableWithStateWriteModifierSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonpayableWithStateWriteModifier"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar stateX
              , L00_SourceSolidity.ContractItem.modifierDecl
                  stateWriteModifier
              , L00_SourceSolidity.ContractItem.function
                  nonpayableWithStateWriteModifierFunction ] } ] }

def nonpayableWithStateWriteModifierAccepted : Bool :=
  sourceUnitAccepted? nonpayableWithStateWriteModifierSource

def viewTargetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readOnly"
    mutability := L00_SourceSolidity.StateMutability.view }

def pureCallsViewFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pureCallsView"
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "readOnly") []))) }

def pureCallsViewSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureCallsView"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  viewTargetFunction
              , L00_SourceSolidity.ContractItem.function
                  pureCallsViewFunction ] } ] }

def pureCallsViewRejected : Bool :=
  Result.isError (SourceUnit.check pureCallsViewSource)

def viewCallsPureFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewCallsPure"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "f") []))) }

def viewCallsPureSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewCallsPure"
            items :=
              [ L00_SourceSolidity.ContractItem.function simpleReturnFunction
              , L00_SourceSolidity.ContractItem.function
                  viewCallsPureFunction ] } ] }

def viewCallsPureAccepted : Bool :=
  sourceUnitAccepted? viewCallsPureSource

def viewEmitSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewEmits"
            items :=
              [ L00_SourceSolidity.ContractItem.eventDecl pingEvent
              , L00_SourceSolidity.ContractItem.function
                  { emitPingFunction with
                    name := some "viewEmit"
                    mutability :=
                      L00_SourceSolidity.StateMutability.view } ] } ] }

def viewEmitRejected : Bool :=
  Result.isError (SourceUnit.check viewEmitSource)

def targetContractTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Target")

def viewCreatesContractFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewCreates"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.newExpr targetContractTy [])
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.literal
                  (L00_SourceSolidity.Literal.number "1"))) ]) }

def viewCreatesContractSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "Target", items := [] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ViewCreatesContract"
            items := [L00_SourceSolidity.ContractItem.function
              viewCreatesContractFunction] } ] }

def viewCreatesContractRejected : Bool :=
  Result.isError (SourceUnit.check viewCreatesContractSource)

def externalViewUintFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] [uint256]
    L00_SourceSolidity.StateMutability.view
    L00_SourceSolidity.Visibility.external_

def externalPureUintFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] [uint256]
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.external_

def internalPureUintFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] [uint256]
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.internal_

def internalPureUintUnaryFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [uint256] [uint256]
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.internal_

def publicPureUintFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [] [uint256]
    L00_SourceSolidity.StateMutability.pure
    L00_SourceSolidity.Visibility.public_

def externalFunctionTakingFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [externalPureUintFunctionTy] []
    L00_SourceSolidity.StateMutability.nonpayable
    L00_SourceSolidity.Visibility.external_

def externalFunctionTakingInternalFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [internalPureUintFunctionTy] []
    L00_SourceSolidity.StateMutability.nonpayable
    L00_SourceSolidity.Visibility.external_

def mappingUintToUintTy : Ty :=
  L00_SourceSolidity.Ty.mapping uint256 uint256

def externalFunctionTakingMappingTy : Ty :=
  L00_SourceSolidity.Ty.function [mappingUintToUintTy] []
    L00_SourceSolidity.StateMutability.nonpayable
    L00_SourceSolidity.Visibility.external_

def externalFunctionTakingFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ExternalFunctionTakingFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingFunctionTy } ] } ] }

def externalFunctionTakingFunctionAccepted : Bool :=
  sourceUnitAccepted? externalFunctionTakingFunctionSource

def externalFunctionTakingInternalFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadExternalFunctionTakingInternalFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingInternalFunctionTy } ] } ] }

def externalFunctionTakingInternalFunctionRejected : Bool :=
  Result.isError
    (SourceUnit.check externalFunctionTakingInternalFunctionSource)

def externalFunctionTakingMappingSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadExternalFunctionTakingMapping"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingMappingTy } ] } ] }

def externalFunctionTakingMappingRejected : Bool :=
  Result.isError (SourceUnit.check externalFunctionTakingMappingSource)

def functionTypeMutabilityConversionFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "functionTypeMutability"
    params :=
      [ { name := some "getter"
          ty := externalPureUintFunctionTy
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "asView"
                  ty := some externalViewUintFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "getter"))
          , L00_SourceSolidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def functionTypeMutabilityConversionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FunctionTypeMutability"
            items :=
              [L00_SourceSolidity.ContractItem.function
                functionTypeMutabilityConversionFunction] } ] }

def functionTypeMutabilityConversionAccepted : Bool :=
  sourceUnitAccepted? functionTypeMutabilityConversionSource

def internalFunctionPointerAliasTarget :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "double"
    params :=
      [ { name := some "x"
          ty := uint256
          location := none } ]
    visibility := some L00_SourceSolidity.Visibility.internal_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.mul
              (L00_SourceSolidity.Expr.ident "x")
              (numberExpr "2")))) }

def internalFunctionPointerAliasFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callViaPointer"
    params :=
      [ { name := some "x"
          ty := uint256
          location := none } ]
    visibility := some L00_SourceSolidity.Visibility.public_
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerAliasSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerAlias"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasFunction ] } ] }

def internalFunctionPointerAliasAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerAliasSource

def internalFunctionPointerReassignTarget :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasTarget with
    name := some "triple"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.mul
              (L00_SourceSolidity.Expr.ident "x")
              (numberExpr "3")))) }

def internalFunctionPointerReassignFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaReassignedPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "fp")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.ident "triple"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerReassignSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerReassign"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerReassignFunction ] } ] }

def internalFunctionPointerReassignAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerReassignSource

def internalFunctionPointerAssignAfterDeclFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaAssignedPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "fp")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerAssignAfterDeclSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerAssignAfterDecl"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAssignAfterDeclFunction ] } ] }

def internalFunctionPointerAssignAfterDeclAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerAssignAfterDeclSource

def internalFunctionPointerDeleteThenAssignFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaDeletedThenAssignedPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.unary
                L00_SourceSolidity.UnaryOp.delete
                (L00_SourceSolidity.Expr.ident "fp"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "fp")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.ident "triple"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerDeleteThenAssignSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerDeleteThenAssign"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerDeleteThenAssignFunction ] } ] }

def internalFunctionPointerDeleteThenAssignAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerDeleteThenAssignSource

def internalFunctionPointerUninitializedCallFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callUninitializedPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerUninitializedCallSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerUninitializedCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerUninitializedCallFunction ] } ] }

def internalFunctionPointerUninitializedCallAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerUninitializedCallSource

def internalFunctionPointerDeletedCallFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callDeletedPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.unary
                L00_SourceSolidity.UnaryOp.delete
                (L00_SourceSolidity.Expr.ident "fp"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "fp")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "x")])) ]) }

def internalFunctionPointerDeletedCallSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerDeletedCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerDeletedCallFunction ] } ] }

def internalFunctionPointerDeletedCallAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerDeletedCallSource

def internalFunctionPointerCopyFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "copyPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.varDecl
              [ { name := some "gp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "fp"))
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "fp")
                L00_SourceSolidity.AssignOp.assign
                (L00_SourceSolidity.Expr.ident "triple"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.binary
                  L00_SourceSolidity.BinaryOp.add
                  (L00_SourceSolidity.Expr.call
                    (L00_SourceSolidity.Expr.ident "gp")
                    [L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "x")])
                  (L00_SourceSolidity.Expr.call
                    (L00_SourceSolidity.Expr.ident "fp")
                    [L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "x")]))) ]) }

def internalFunctionPointerCopySource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerCopy"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerCopyFunction ] } ] }

def internalFunctionPointerCopyAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerCopySource

def internalFunctionPointerParamApplyFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "applyPointer"
    visibility := some L00_SourceSolidity.Visibility.internal_
    mutability := L00_SourceSolidity.StateMutability.pure
    params :=
      [ { name := some "fn"
          ty := internalPureUintUnaryFunctionTy
          location := none }
      , { name := some "x"
          ty := uint256
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "fn")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "x")]))) }

def internalFunctionPointerParamCallerFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointer"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (L00_SourceSolidity.Expr.ident "double"))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "applyPointer")
                  [ L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "fp")
                  , L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "x") ])) ]) }

def internalFunctionPointerParamUninitializedCallerFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointerUninitialized"
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.ident "applyPointer")
                  [ L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "fp")
                  , L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.ident "x") ])) ]) }

def internalFunctionPointerParamSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerParam"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerParamApplyFunction
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerParamCallerFunction
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerParamUninitializedCallerFunction ] } ] }

def internalFunctionPointerParamAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerParamSource

def internalFunctionPointerOverloadedTarget :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasTarget with
    params :=
      [ { name := some "x"
          ty := uint256
          location := none }
      , { name := some "y"
          ty := uint256
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "x"))) }

def internalFunctionPointerParamBareOverloadedCallerFunction :
    L00_SourceSolidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointerBare"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "applyPointer")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.ident "double")
              , L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.ident "x") ]))) }

def internalFunctionPointerParamOverloadedSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "InternalFunctionPointerParamOverloaded"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerOverloadedTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerParamApplyFunction
              , L00_SourceSolidity.ContractItem.function
                  internalFunctionPointerParamBareOverloadedCallerFunction ] } ] }

def internalFunctionPointerParamOverloadedAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerParamOverloadedSource

def externalFunctionPointerGasCallFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callGetterWithGas"
    params :=
      [ { name := some "getter"
          ty := externalViewUintFunctionTy
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.callWithOptions
              (L00_SourceSolidity.Expr.ident "getter")
              [gasOption "1000"] []))) }

def externalFunctionPointerGasCallSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ExternalFunctionPointerGasCall"
            items :=
              [L00_SourceSolidity.ContractItem.function
                externalFunctionPointerGasCallFunction] } ] }

def externalFunctionPointerGasCallAccepted : Bool :=
  sourceUnitAccepted? externalFunctionPointerGasCallSource

def publicInternalFunctionPointerParamFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesInternalFunction"
    params :=
      [ { name := some "getter"
          ty := internalPureUintFunctionTy
          location := none } ] }

def publicInternalFunctionPointerParamSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadInternalFunctionPointerParam"
            items :=
              [L00_SourceSolidity.ContractItem.function
                publicInternalFunctionPointerParamFunction] } ] }

def publicInternalFunctionPointerParamRejected : Bool :=
  Result.isError (SourceUnit.check publicInternalFunctionPointerParamSource)

def invalidPublicFunctionTypeParamFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badFunctionTypeVisibility"
    params :=
      [ { name := some "getter"
          ty := publicPureUintFunctionTy
          location := none } ] }

def invalidPublicFunctionTypeParamSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadFunctionTypeVisibility"
            items :=
              [L00_SourceSolidity.ContractItem.function
                invalidPublicFunctionTypeParamFunction] } ] }

def invalidPublicFunctionTypeParamRejected : Bool :=
  Result.isError (SourceUnit.check invalidPublicFunctionTypeParamSource)

def publicExternalFunctionPointerStateVarSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ExternalFunctionPointerGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "getter"
                    ty := externalPureUintFunctionTy
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicExternalFunctionPointerStateVarAccepted : Bool :=
  sourceUnitAccepted? publicExternalFunctionPointerStateVarSource

def publicInternalFunctionPointerStateVarSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadInternalFunctionPointerGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "getter"
                    ty := internalPureUintFunctionTy
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicInternalFunctionPointerStateVarRejected : Bool :=
  Result.isError
    (SourceUnit.check publicInternalFunctionPointerStateVarSource)

def functionFieldStruct : L00_SourceSolidity.StructDecl :=
  { name := "FunctionField"
    fields := [{ name := "getter", ty := internalPureUintFunctionTy }] }

def functionFieldStructTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "FunctionField")

def publicStructInternalFunctionGetterSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct functionFieldStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadStructInternalFunctionGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "entry"
                    ty := functionFieldStructTy
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicStructInternalFunctionGetterRejected : Bool :=
  Result.isError
    (SourceUnit.check publicStructInternalFunctionGetterSource)

def nestedPublicGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedPublicGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.mapping uint256 uint256)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.array uint256 none)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def nestedPublicGetterAccepted : Bool :=
  sourceUnitAccepted? nestedPublicGetterSource

def publicBytesArrayGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PublicBytesArrayGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "blobs"
                    ty := L00_SourceSolidity.Ty.array
                      L00_SourceSolidity.Ty.bytes none
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicBytesArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicBytesArrayGetterSource

def publicStringArrayGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PublicStringArrayGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "names"
                    ty := L00_SourceSolidity.Ty.array
                      L00_SourceSolidity.Ty.string none
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicStringArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicStringArrayGetterSource

def publicFixedBytesArrayGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PublicFixedBytesArrayGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "fixedBlobs"
                    ty := L00_SourceSolidity.Ty.array
                      L00_SourceSolidity.Ty.bytes (some 2)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicFixedBytesArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicFixedBytesArrayGetterSource

def publicStructGetterShapeStruct : L00_SourceSolidity.StructDecl :=
  { name := "PublicStructData"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "skipMap"
          ty := L00_SourceSolidity.Ty.mapping uint256 uint256 }
      , { name := "raw", ty := L00_SourceSolidity.Ty.bytes }
      , { name := "skipItems"
          ty := L00_SourceSolidity.Ty.array uint256 none }
      , { name := "ok", ty := L00_SourceSolidity.Ty.bool } ] }

def publicStructGetterShapeStateVar :
    L00_SourceSolidity.StateVarDecl :=
  { name := "entry"
    ty := L00_SourceSolidity.Ty.user (userPath "PublicStructData")
    visibility := some L00_SourceSolidity.Visibility.public_ }

def publicStructGetterShapeTypes : TypeContext :=
  { TypeContext.empty with
    structs :=
      [(userPath "PublicStructData", publicStructGetterShapeStruct)] }

def publicStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes publicStructGetterShapeStateVar with
  | some sig =>
      sig.returns ==
        [ uint256
        , L00_SourceSolidity.Ty.bytes
        , L00_SourceSolidity.Ty.bool ]
  | none => false

def publicStructGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicStructGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicStructGetterShapeStateVar ] } ] }

def publicStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicStructGetterSource

def publicNestedStructGetterInnerStruct :
    L00_SourceSolidity.StructDecl :=
  { name := "NestedPublicStruct"
    fields :=
      [ { name := "inner", ty := uint256 }
      , { name := "flag", ty := L00_SourceSolidity.Ty.bool } ] }

def publicNestedStructGetterOuterStruct :
    L00_SourceSolidity.StructDecl :=
  { name := "OuterPublicStruct"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "nested"
          ty :=
            L00_SourceSolidity.Ty.user
              (userPath "NestedPublicStruct") }
      , { name := "raw", ty := L00_SourceSolidity.Ty.bytes } ] }

def publicNestedStructGetterStateVar :
    L00_SourceSolidity.StateVarDecl :=
  { name := "entry"
    ty := L00_SourceSolidity.Ty.user (userPath "OuterPublicStruct")
    visibility := some L00_SourceSolidity.Visibility.public_ }

def publicNestedStructGetterTypes : TypeContext :=
  { TypeContext.empty with
    structs :=
      [ (userPath "NestedPublicStruct",
          publicNestedStructGetterInnerStruct)
      , (userPath "OuterPublicStruct",
          publicNestedStructGetterOuterStruct) ] }

def publicNestedStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicNestedStructGetterTypes publicNestedStructGetterStateVar with
  | some sig =>
      sig.returns ==
        [ uint256
        , L00_SourceSolidity.Ty.user (userPath "NestedPublicStruct")
        , L00_SourceSolidity.Ty.bytes ]
  | none => false

def publicNestedStructGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicNestedStructGetterInnerStruct
      , L00_SourceSolidity.SourceItem.freeStruct
          publicNestedStructGetterOuterStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicNestedStructGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicNestedStructGetterStateVar ] } ] }

def publicNestedStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicNestedStructGetterSource

def publicMappingStructGetterShapeStateVar :
    L00_SourceSolidity.StateVarDecl :=
  { name := "entries"
    ty :=
      L00_SourceSolidity.Ty.mapping uint256
        (L00_SourceSolidity.Ty.user (userPath "PublicStructData"))
    visibility := some L00_SourceSolidity.Visibility.public_ }

def publicMappingStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicMappingStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , L00_SourceSolidity.Ty.bytes
          , L00_SourceSolidity.Ty.bool ]
  | none => false

def publicMappingStructGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicMappingStructGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicMappingStructGetterShapeStateVar ] } ] }

def publicMappingStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicMappingStructGetterSource

def publicArrayStructGetterShapeStateVar :
    L00_SourceSolidity.StateVarDecl :=
  { name := "records"
    ty :=
      L00_SourceSolidity.Ty.array
        (L00_SourceSolidity.Ty.user (userPath "PublicStructData"))
        none
    visibility := some L00_SourceSolidity.Visibility.public_ }

def publicArrayStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicArrayStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , L00_SourceSolidity.Ty.bytes
          , L00_SourceSolidity.Ty.bool ]
  | none => false

def publicArrayStructGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicArrayStructGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicArrayStructGetterShapeStateVar ] } ] }

def publicArrayStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicArrayStructGetterSource

def publicFixedArrayStructGetterShapeStateVar :
    L00_SourceSolidity.StateVarDecl :=
  { name := "fixedRecords"
    ty :=
      L00_SourceSolidity.Ty.array
        (L00_SourceSolidity.Ty.user (userPath "PublicStructData"))
        (some 2)
    visibility := some L00_SourceSolidity.Visibility.public_ }

def publicFixedArrayStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicFixedArrayStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , L00_SourceSolidity.Ty.bytes
          , L00_SourceSolidity.Ty.bool ]
  | none => false

def publicFixedArrayStructGetterSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PublicFixedArrayStructGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicFixedArrayStructGetterShapeStateVar ] } ] }

def publicFixedArrayStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicFixedArrayStructGetterSource

def deleteFixedArrayStructSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "DeleteFixedArrayStruct"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  publicFixedArrayStructGetterShapeStateVar
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clear"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.ident
                              "fixedRecords"))) } ] } ] }

def deleteFixedArrayStructAccepted : Bool :=
  sourceUnitAccepted? deleteFixedArrayStructSource

def assignFixedStructArrayStruct : L00_SourceSolidity.StructDecl :=
  { name := "FixedStructArrayRecord"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "flag", ty := L00_SourceSolidity.Ty.bool } ] }

def assignFixedStructArrayRecordTy : L00_SourceSolidity.Ty :=
  L00_SourceSolidity.Ty.user (userPath "FixedStructArrayRecord")

def assignFixedStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "AssignFixedStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        assignFixedStructArrayRecordTy (some 2)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              assignFixedStructArrayRecordTy (some 2)
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "records")
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident "values"))) } ] } ] }

def assignFixedStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignFixedStructArraySource

def assignDynamicStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "AssignDynamicStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              assignFixedStructArrayRecordTy none
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "records")
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident "values"))) } ] } ] }

def assignDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignDynamicStructArraySource

def indexAssignFixedStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "IndexAssignFixedStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        assignFixedStructArrayRecordTy (some 2)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "records")
                              (numberExpr "1"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident "value"))) } ] } ] }

def indexAssignFixedStructArrayAccepted : Bool :=
  sourceUnitAccepted? indexAssignFixedStructArraySource

def indexAssignDynamicStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "IndexAssignDynamicStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "records")
                              (numberExpr "1"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident "value"))) } ] } ] }

def indexAssignDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? indexAssignDynamicStructArraySource

def indexAssignMappingStructSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "IndexAssignMappingStruct"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        assignFixedStructArrayRecordTy
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "entries")
                              (L00_SourceSolidity.Expr.ident "key"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident "value"))) } ] } ] }

def indexAssignMappingStructAccepted : Bool :=
  sourceUnitAccepted? indexAssignMappingStructSource

def pushStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "PushStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "pushValue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "records")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "pushDefault"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "records")
                              "push")
                            [])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "popOne"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "records")
                              "pop")
                            [])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "deleteAll"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.ident
                              "records"))) } ] } ] }

def pushStructArrayAccepted : Bool :=
  sourceUnitAccepted? pushStructArraySource

def deleteNestedStructArrayStruct : L00_SourceSolidity.StructDecl :=
  { name := "NestedArrayRecord"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "items"
          ty := L00_SourceSolidity.Ty.array uint256 none } ] }

def deleteNestedStructArrayRecordTy : L00_SourceSolidity.Ty :=
  L00_SourceSolidity.Ty.user (userPath "NestedArrayRecord")

def deleteNestedStructArraySource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "DeleteNestedStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "dynamicRecords"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        deleteNestedStructArrayRecordTy none }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "fixedRecords"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        deleteNestedStructArrayRecordTy (some 2) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearDynamic"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.ident
                              "dynamicRecords"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearFixed"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.ident
                              "fixedRecords"))) } ] } ] }

def deleteNestedStructArrayAccepted : Bool :=
  sourceUnitAccepted? deleteNestedStructArraySource

def assignNestedDynamicStructArraySource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "AssignNestedDynamicStructArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        deleteNestedStructArrayRecordTy none }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              deleteNestedStructArrayRecordTy none
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.ident "records")
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "values"))) } ] } ] }

def assignNestedDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignNestedDynamicStructArraySource

def assignNestedStructMappingSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "AssignNestedStructMapping"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        deleteNestedStructArrayRecordTy }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := deleteNestedStructArrayRecordTy
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "entries")
                              (L00_SourceSolidity.Expr.ident "key"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) } ] } ] }

def assignNestedStructMappingAccepted : Bool :=
  sourceUnitAccepted? assignNestedStructMappingSource

def indexedDynamicArrayAssignmentSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "IndexedDynamicArrayAssignment"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        (L00_SourceSolidity.Ty.array
                          uint256 none)
                        none }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.array
                          uint256 none) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setMatrix"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "index"
                          ty := uint256
                          location := none }
                      , { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              uint256 none
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "matrix")
                              (L00_SourceSolidity.Expr.ident "index"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "values"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setBucket"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              uint256 none
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "buckets")
                              (L00_SourceSolidity.Expr.ident "key"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "values"))) } ] } ] }

def indexedDynamicArrayAssignmentAccepted : Bool :=
  sourceUnitAccepted? indexedDynamicArrayAssignmentSource

def deleteNestedIndexedStorageSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , L00_SourceSolidity.SourceItem.contract
          { name := "DeleteNestedIndexedStorage"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        (L00_SourceSolidity.Ty.array
                          uint256 none)
                        none }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        deleteNestedStructArrayRecordTy }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearMatrix"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "index"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident "matrix")
                              (L00_SourceSolidity.Expr.ident
                                "index")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearEntry"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident
                                "entries")
                              (L00_SourceSolidity.Expr.ident
                                "key")))) } ] } ] }

def deleteNestedIndexedStorageAccepted : Bool :=
  sourceUnitAccepted? deleteNestedIndexedStorageSource

def nestedStoragePathSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedStoragePath"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        (L00_SourceSolidity.Ty.array
                          uint256 none)
                        none }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.mapping
                          uint256 uint256) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setMatrixCell"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "matrix")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident "inner"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearMatrixCell"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "matrix")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "readMatrixCell"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "matrix")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setNested"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "nested")
                                (L00_SourceSolidity.Expr.ident
                                  "left"))
                              (L00_SourceSolidity.Expr.ident
                                "right"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearNested"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "nested")
                                (L00_SourceSolidity.Expr.ident
                                  "left"))
                              (L00_SourceSolidity.Expr.ident
                                "right")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "readNested"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "nested")
                                (L00_SourceSolidity.Expr.ident
                                  "left"))
                              (L00_SourceSolidity.Expr.ident
                                "right")))) } ] } ] }

def nestedStoragePathAccepted : Bool :=
  sourceUnitAccepted? nestedStoragePathSource

def nestedStoragePathCompoundSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedStoragePathCompound"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        (L00_SourceSolidity.Ty.array
                          uint256 none)
                        none }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.mapping
                          uint256 uint256) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "addMatrix"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "matrix")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner"))
                            L00_SourceSolidity.AssignOp.addAssign
                            (L00_SourceSolidity.Expr.ident
                              "delta"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "incMatrix"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.preIncrement
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "matrix")
                                  (L00_SourceSolidity.Expr.ident
                                    "outer"))
                                (L00_SourceSolidity.Expr.ident
                                  "inner"))))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "addNested"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "nested")
                                (L00_SourceSolidity.Expr.ident
                                  "left"))
                              (L00_SourceSolidity.Expr.ident
                                "right"))
                            L00_SourceSolidity.AssignOp.addAssign
                            (L00_SourceSolidity.Expr.ident
                              "delta"))) } ] } ] }

def nestedStoragePathCompoundAccepted : Bool :=
  sourceUnitAccepted? nestedStoragePathCompoundSource

def structStoragePathRecord : L00_SourceSolidity.StructDecl :=
  { name := "StoragePathRecord"
    fields :=
      [ { name := "count", ty := uint256 }
      , { name := "values"
          ty := L00_SourceSolidity.Ty.array uint256 none }
      , { name := "blob", ty := L00_SourceSolidity.Ty.bytes }
      , { name := "scores"
          ty :=
            L00_SourceSolidity.Ty.mapping uint256 uint256 } ] }

def structStoragePathRecordTy : L00_SourceSolidity.Ty :=
  L00_SourceSolidity.Ty.user (userPath "StoragePathRecord")

def structStoragePathSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeStruct
          structStoragePathRecord
      , L00_SourceSolidity.SourceItem.contract
          { name := "StructStoragePath"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        structStoragePathRecordTy }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "addCount"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "entries")
                                (L00_SourceSolidity.Expr.ident
                                  "key"))
                              "count")
                            L00_SourceSolidity.AssignOp.addAssign
                            (L00_SourceSolidity.Expr.ident
                              "delta"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "addValue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "index"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "values")
                              (L00_SourceSolidity.Expr.ident
                                "index"))
                            L00_SourceSolidity.AssignOp.addAssign
                            (L00_SourceSolidity.Expr.ident
                              "delta"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearValue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "index"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "values")
                              (L00_SourceSolidity.Expr.ident
                                "index")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathArrayPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "values")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathArrayPushAssign"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values")
                                "push")
                              [])
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathArrayPop"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "values")
                              "pop")
                            [])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathBlobPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "blob")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathBlobPushAssign"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob")
                                "push")
                              [])
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "directPathBlobPop"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key"))
                                "blob")
                              "pop")
                            [])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasCount"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "ref"
                                  ty := some structStoragePathRecordTy
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key")))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "ref")
                                  "count")
                                L00_SourceSolidity.AssignOp.addAssign
                                (L00_SourceSolidity.Expr.ident
                                  "delta")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasValue"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "index"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "ref"
                                  ty := some structStoragePathRecordTy
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "entries")
                                  (L00_SourceSolidity.Expr.ident
                                    "key")))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident
                                      "ref")
                                    "values")
                                  (L00_SourceSolidity.Expr.ident
                                    "index"))
                                L00_SourceSolidity.AssignOp.addAssign
                                (L00_SourceSolidity.Expr.ident
                                  "delta")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasArrayPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (L00_SourceSolidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "vals")
                                  "push")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.ident
                                      "value") ]) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasArrayPushAssign"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (L00_SourceSolidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident
                                      "vals")
                                    "push")
                                  [])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ident
                                  "value")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasArrayPop"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (L00_SourceSolidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "vals")
                                  "pop")
                                []) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasBlobPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some L00_SourceSolidity.Ty.bytes
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "blob")
                                  "push")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.ident
                                      "value") ]) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasBlobPushAssign"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some L00_SourceSolidity.Ty.bytes
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.call
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident
                                      "blob")
                                    "push")
                                  [])
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ident
                                  "value")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasBlobPop"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some L00_SourceSolidity.Ty.bytes
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "blob")
                                  "pop")
                                []) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "aliasScoreSet"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.varDecl
                              [ { name := some "scores"
                                  ty :=
                                    some
                                      (L00_SourceSolidity.Ty.mapping
                                        uint256 uint256)
                                  location :=
                                    some
                                      L00_SourceSolidity.DataLocation.storage } ]
                              (some
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "scores"))
                          , L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "scores")
                                  (L00_SourceSolidity.Expr.ident
                                    "subkey"))
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ident
                                  "value")) ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "pushValuesStorage"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    params :=
                      [ { name := some "vals"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              uint256 none
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident
                                "vals")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "pushBlobStorage"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    params :=
                      [ { name := some "blob"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident
                                "blob")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setScoreStorage"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    params :=
                      [ { name := some "scores"
                          ty :=
                            L00_SourceSolidity.Ty.mapping
                              uint256 uint256
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.ident
                                "scores")
                              (L00_SourceSolidity.Expr.ident
                                "subkey"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.modifierDecl
                  { name := "withValues"
                    params :=
                      [ { name := some "vals"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              uint256 none
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "vals")
                                  "push")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.ident
                                      "value") ])
                          , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }
              , L00_SourceSolidity.ContractItem.modifierDecl
                  { name := "withBlob"
                    params :=
                      [ { name := some "blob"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.call
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.ident
                                    "blob")
                                  "push")
                                [ L00_SourceSolidity.Arg.positional
                                    (L00_SourceSolidity.Expr.ident
                                      "value") ])
                          , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }
              , L00_SourceSolidity.ContractItem.modifierDecl
                  { name := "withScore"
                    params :=
                      [ { name := some "scores"
                          ty :=
                            L00_SourceSolidity.Ty.mapping
                              uint256 uint256
                          location :=
                            some
                              L00_SourceSolidity.DataLocation.storage }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.expr
                              (L00_SourceSolidity.Expr.assign
                                (L00_SourceSolidity.Expr.index
                                  (L00_SourceSolidity.Expr.ident
                                    "scores")
                                  (L00_SourceSolidity.Expr.ident
                                    "subkey"))
                                L00_SourceSolidity.AssignOp.assign
                                (L00_SourceSolidity.Expr.ident
                                  "value"))
                          , L00_SourceSolidity.Stmt.modifierPlaceholder ]) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "internalPathArrayPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident
                              "pushValuesStorage")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "internalPathBlobPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident
                              "pushBlobStorage")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "internalPathScoreSet"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident
                              "setScoreStorage")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "scores")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "subkey")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ])) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "modifierPathArrayPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    modifiers :=
                      [ { target := userPath "withValues"
                          args :=
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "values")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ] } ]
                    body := some L00_SourceSolidity.Stmt.empty }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "modifierPathBlobPush"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    modifiers :=
                      [ { target := userPath "withBlob"
                          args :=
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "blob")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ] } ]
                    body := some L00_SourceSolidity.Stmt.empty }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "modifierPathScoreSet"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    modifiers :=
                      [ { target := userPath "withScore"
                          args :=
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.member
                                  (L00_SourceSolidity.Expr.index
                                    (L00_SourceSolidity.Expr.ident
                                      "entries")
                                    (L00_SourceSolidity.Expr.ident
                                      "key"))
                                  "scores")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "subkey")
                            , L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "value") ] } ]
                    body := some L00_SourceSolidity.Stmt.empty } ] } ] }

def structStoragePathAccepted : Bool :=
  sourceUnitAccepted? structStoragePathSource

def nestedBytesStoragePathSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedBytesStoragePath"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "blobs"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        L00_SourceSolidity.Ty.bytes none }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "setByte"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := L00_SourceSolidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.assign
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "blobs")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner"))
                            L00_SourceSolidity.AssignOp.assign
                            (L00_SourceSolidity.Expr.ident
                              "value"))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "clearByte"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.unary
                            L00_SourceSolidity.UnaryOp.delete
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "blobs")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner")))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "readByte"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    returns :=
                      [ { name := none
                          ty := L00_SourceSolidity.Ty.bytesN 1 } ]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.index
                              (L00_SourceSolidity.Expr.index
                                (L00_SourceSolidity.Expr.ident
                                  "blobs")
                                (L00_SourceSolidity.Expr.ident
                                  "outer"))
                              (L00_SourceSolidity.Expr.ident
                                "inner")))) } ] } ] }

def nestedBytesStoragePathAccepted : Bool :=
  sourceUnitAccepted? nestedBytesStoragePathSource

def pushNestedDynamicArraySource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PushNestedDynamicArray"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      L00_SourceSolidity.Ty.array
                        (L00_SourceSolidity.Ty.array
                          uint256 none)
                        none }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "pushValues"
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            L00_SourceSolidity.Ty.array
                              uint256 none
                          location :=
                            some L00_SourceSolidity.DataLocation.calldata } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.expr
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "matrix")
                              "push")
                            [ L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "values") ])) } ] } ] }

def pushNestedDynamicArrayAccepted : Bool :=
  sourceUnitAccepted? pushNestedDynamicArraySource

def publicMappingByteStringsGetterSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PublicMappingByteStringsGetter"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "raw"
                    ty := L00_SourceSolidity.Ty.mapping
                      uint256 L00_SourceSolidity.Ty.bytes
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "text"
                    ty := L00_SourceSolidity.Ty.mapping
                      uint256 L00_SourceSolidity.Ty.string
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ } ] } ] }

def publicMappingByteStringsGetterAccepted : Bool :=
  sourceUnitAccepted? publicMappingByteStringsGetterSource

def nestedPublicGetterMemberCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NestedPublicGetterMemberCalls"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.mapping uint256 uint256)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      L00_SourceSolidity.Ty.mapping uint256
                        (L00_SourceSolidity.Ty.array uint256 none)
                    visibility :=
                      some L00_SourceSolidity.Visibility.public_ }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "readNested"
                    visibility := some L00_SourceSolidity.Visibility.public_
                    returns := [{ name := none, ty := uint256 }]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "this")
                                "nested")
                              [ L00_SourceSolidity.Arg.positional
                                  (numberExpr "4")
                              , L00_SourceSolidity.Arg.positional
                                  (numberExpr "5") ]))) }
              , L00_SourceSolidity.ContractItem.function
                  { name := some "readBucket"
                    visibility := some L00_SourceSolidity.Visibility.public_
                    returns := [{ name := none, ty := uint256 }]
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "this")
                                "buckets")
                              [ L00_SourceSolidity.Arg.positional
                                  (numberExpr "7")
                              , L00_SourceSolidity.Arg.positional
                                  (numberExpr "1") ]))) } ] } ] }

def nestedPublicGetterMemberCallsAccepted : Bool :=
  sourceUnitAccepted? nestedPublicGetterMemberCallSource

def tryCatchZeroClause : L00_SourceSolidity.CatchClause :=
  L00_SourceSolidity.CatchClause.clause none []
    (L00_SourceSolidity.Stmt.returnValues
      (some
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number "0"))))

def tryExternalFunctionCall : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryExternal"
    params :=
      [ { name := some "getter"
          ty := externalViewUintFunctionTy
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryExternalFunctionCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryExternalFunction"
            items := [L00_SourceSolidity.ContractItem.function
              tryExternalFunctionCall] } ] }

def tryExternalFunctionCallAccepted : Bool :=
  sourceUnitAccepted? tryExternalFunctionCallSource

def tryMemberTargetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "read"
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.view }

def tryContractMemberCallFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryMember"
    params :=
      [ { name := some "feed"
          ty := targetContractTy
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.ident "feed") "read") [])
          [{ name := some "value", ty := uint256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryContractMemberCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "Target"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tryMemberTargetFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "TryContractMember"
            items :=
              [L00_SourceSolidity.ContractItem.function
                tryContractMemberCallFunction] } ] }

def tryContractMemberCallAccepted : Bool :=
  sourceUnitAccepted? tryContractMemberCallSource

def tryInternalFunctionCall : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryInternal"
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "f") [])
          [{ name := some "value", ty := uint256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryInternalFunctionCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryInternalFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.function simpleReturnFunction
              , L00_SourceSolidity.ContractItem.function
                  tryInternalFunctionCall ] } ] }

def tryInternalFunctionCallRejected : Bool :=
  Result.isError (SourceUnit.check tryInternalFunctionCallSource)

def tryLowLevelCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryLowLevelCall"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryLowLevel"
                    params :=
                      [ { name := some "addr"
                          ty := L00_SourceSolidity.Ty.address false
                          location := none } ]
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.tryCatch
                              (memberCallExpr
                                (L00_SourceSolidity.Expr.ident "addr")
                                "call"
                                [L00_SourceSolidity.Arg.positional
                                  (memberCallExpr
                                    (L00_SourceSolidity.Expr.ident "abi")
                                    "encode" [])])
                              [tryCatchZeroClause]
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tryLowLevelCallRejected : Bool :=
  Result.isError (SourceUnit.check tryLowLevelCallSource)

def tryArrayPushSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryArrayPush"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryArrayPush"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.tryCatch
                              (arrayPushExpr
                                (L00_SourceSolidity.Expr.ident "arr")
                                [L00_SourceSolidity.Arg.positional
                                  (numberExpr "1")])
                              [tryCatchZeroClause]
                          , L00_SourceSolidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tryArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check tryArrayPushSource)

def tryLiteralSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryLiteral"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryLiteral"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.tryCatch
                              (L00_SourceSolidity.Expr.literal
                                (L00_SourceSolidity.Literal.number "1"))
                              [tryCatchZeroClause]
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.literal
                                  (L00_SourceSolidity.Literal.number "1"))) ]) } ] } ] }

def tryLiteralRejected : Bool :=
  Result.isError (SourceUnit.check tryLiteralSource)

def tryReturnMismatchFunction : L00_SourceSolidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryReturnMismatch"
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "getter") [])
          [ { name := some "flag"
              ty := L00_SourceSolidity.Ty.bool
              location := none } ]
          (L00_SourceSolidity.Stmt.returnValues
            (some
              (L00_SourceSolidity.Expr.literal
                (L00_SourceSolidity.Literal.number "1"))))
          [tryCatchZeroClause]) }

def tryReturnMismatchSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryReturnMismatch"
            items := [L00_SourceSolidity.ContractItem.function
              tryReturnMismatchFunction] } ] }

def tryReturnMismatchRejected : Bool :=
  Result.isError (SourceUnit.check tryReturnMismatchSource)

def catchErrorClause : L00_SourceSolidity.CatchClause :=
  L00_SourceSolidity.CatchClause.clause (some "Error")
    [ { name := some "reason"
        ty := L00_SourceSolidity.Ty.string
        location := some L00_SourceSolidity.DataLocation.memory } ]
    (L00_SourceSolidity.Stmt.returnValues
      (some
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number "0"))))

def tryCatchErrorFunction : L00_SourceSolidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryCatchError"
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          [catchErrorClause]) }

def tryCatchErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryCatchError"
            items := [L00_SourceSolidity.ContractItem.function
              tryCatchErrorFunction] } ] }

def tryCatchErrorAccepted : Bool :=
  sourceUnitAccepted? tryCatchErrorSource

def badCatchErrorClause : L00_SourceSolidity.CatchClause :=
  L00_SourceSolidity.CatchClause.clause (some "Error")
    [{ name := some "code", ty := uint256, location := none }]
    (L00_SourceSolidity.Stmt.returnValues
      (some
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number "0"))))

def badCatchErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCatchError"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "badCatchError"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.tryCatchReturns
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (L00_SourceSolidity.Stmt.returnValues
                            (some (L00_SourceSolidity.Expr.ident "value")))
                          [badCatchErrorClause]) } ] } ] }

def badCatchErrorRejected : Bool :=
  Result.isError (SourceUnit.check badCatchErrorSource)

def catchPanicClause : L00_SourceSolidity.CatchClause :=
  L00_SourceSolidity.CatchClause.clause (some "Panic")
    [{ name := some "code", ty := uint256, location := none }]
    (L00_SourceSolidity.Stmt.returnValues
      (some
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number "0"))))

def catchBytesClause : L00_SourceSolidity.CatchClause :=
  L00_SourceSolidity.CatchClause.clause none
    [ { name := some "data"
        ty := L00_SourceSolidity.Ty.bytes
        location := some L00_SourceSolidity.DataLocation.memory } ]
    (L00_SourceSolidity.Stmt.returnValues
      (some
        (L00_SourceSolidity.Expr.literal
          (L00_SourceSolidity.Literal.number "0"))))

def tryCatchFullFunction : L00_SourceSolidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryCatchFull"
    body :=
      some
        (L00_SourceSolidity.Stmt.tryCatchReturns
          (L00_SourceSolidity.Expr.call
            (L00_SourceSolidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (L00_SourceSolidity.Stmt.returnValues
            (some (L00_SourceSolidity.Expr.ident "value")))
          [catchErrorClause, catchPanicClause, catchBytesClause]) }

def tryCatchFullSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TryCatchFull"
            items := [L00_SourceSolidity.ContractItem.function
              tryCatchFullFunction] } ] }

def tryCatchFullAccepted : Bool :=
  sourceUnitAccepted? tryCatchFullSource

def duplicateCatchErrorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateCatchError"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateCatchError"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.tryCatchReturns
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (L00_SourceSolidity.Stmt.returnValues
                            (some (L00_SourceSolidity.Expr.ident "value")))
                          [catchErrorClause, catchErrorClause]) } ] } ] }

def duplicateCatchErrorRejected : Bool :=
  Result.isError (SourceUnit.check duplicateCatchErrorSource)

def duplicateCatchPanicSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateCatchPanic"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateCatchPanic"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.tryCatchReturns
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (L00_SourceSolidity.Stmt.returnValues
                            (some (L00_SourceSolidity.Expr.ident "value")))
                          [catchPanicClause, catchPanicClause]) } ] } ] }

def duplicateCatchPanicRejected : Bool :=
  Result.isError (SourceUnit.check duplicateCatchPanicSource)

def duplicateLowLevelCatchSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DuplicateLowLevelCatch"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateLowLevelCatch"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.tryCatchReturns
                          (L00_SourceSolidity.Expr.call
                            (L00_SourceSolidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (L00_SourceSolidity.Stmt.returnValues
                            (some (L00_SourceSolidity.Expr.ident "value")))
                          [tryCatchZeroClause, catchBytesClause]) } ] } ] }

def duplicateLowLevelCatchRejected : Bool :=
  Result.isError (SourceUnit.check duplicateLowLevelCatchSource)

def tryContractCreationSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "Target", items := [] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "TryContractCreation"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryCreate"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.block
                          [ L00_SourceSolidity.Stmt.tryCatch
                              (L00_SourceSolidity.Expr.newExpr
                                targetContractTy [])
                              [tryCatchZeroClause]
                          , L00_SourceSolidity.Stmt.returnValues
                              (some
                                (L00_SourceSolidity.Expr.literal
                                  (L00_SourceSolidity.Literal.number "1"))) ]) } ] } ] }

def tryContractCreationAccepted : Bool :=
  sourceUnitAccepted? tryContractCreationSource

def pureMsgSigFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sig"
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.bytesN 4
          location := none } ]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.ident "msg") "sig"))) }

def pureMsgSigSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureMsgSig"
            items := [L00_SourceSolidity.ContractItem.function
              pureMsgSigFunction] } ] }

def pureMsgSigAccepted : Bool :=
  sourceUnitAccepted? pureMsgSigSource

def pureMsgValueFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "msgValue"
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.ident "msg") "value"))) }

def pureMsgValueSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureMsgValue"
            items := [L00_SourceSolidity.ContractItem.function
              pureMsgValueFunction] } ] }

def pureMsgValueRejected : Bool :=
  Result.isError (SourceUnit.check pureMsgValueSource)

def viewBlockTimestampFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "blockTime"
    mutability := L00_SourceSolidity.StateMutability.view
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.member
              (L00_SourceSolidity.Expr.ident "block") "timestamp"))) }

def viewBlockTimestampSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ViewBlockTimestamp"
            items := [L00_SourceSolidity.ContractItem.function
              viewBlockTimestampFunction] } ] }

def viewBlockTimestampAccepted : Bool :=
  sourceUnitAccepted? viewBlockTimestampSource

def pureBlockTimestampSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PureBlockTimestamp"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { viewBlockTimestampFunction with
                    name := some "pureBlockTime"
                    mutability :=
                      L00_SourceSolidity.StateMutability.pure } ] } ] }

def pureBlockTimestampRejected : Bool :=
  Result.isError (SourceUnit.check pureBlockTimestampSource)

def uint8 : Ty := L00_SourceSolidity.Ty.uint 8

def uint16 : Ty := L00_SourceSolidity.Ty.uint 16

def int8 : Ty := L00_SourceSolidity.Ty.int 8

def bytes4 : Ty := L00_SourceSolidity.Ty.bytesN 4

def bytes32 : Ty := L00_SourceSolidity.Ty.bytesN 32

def addressTy : Ty := L00_SourceSolidity.Ty.address false

def payableAddressTy : Ty := L00_SourceSolidity.Ty.address true

def oneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.literal (L00_SourceSolidity.Literal.number "1")

def zeroExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.literal (L00_SourceSolidity.Literal.number "0")

def int8OneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName int8)
    [L00_SourceSolidity.Arg.positional oneExpr]

def uint8OneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName uint8)
    [L00_SourceSolidity.Arg.positional oneExpr]

def badWidthAndSignCastExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName uint16)
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.ident "x")]

def uint160OneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName (L00_SourceSolidity.Ty.uint 160))
    [L00_SourceSolidity.Arg.positional oneExpr]

def addressCastExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName addressTy)
    [L00_SourceSolidity.Arg.positional uint160OneExpr]

def literalUint8ReturnSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "LiteralUint8"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "small"
                    returns := [{ name := none, ty := uint8, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some oneExpr)) } ] } ] }

def literalUint8Accepted : Bool :=
  sourceUnitAccepted? literalUint8ReturnSource

def takesUint8Function : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesSmall"
    params := [{ name := some "x", ty := uint8, location := none }]
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some (L00_SourceSolidity.Expr.ident "x"))) }

def callUint8LiteralFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callSmall"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "takesSmall")
              [L00_SourceSolidity.Arg.positional oneExpr]))) }

def callUint8LiteralSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CallUint8Literal"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  takesUint8Function
              , L00_SourceSolidity.ContractItem.function
                  callUint8LiteralFunction ] } ] }

def callUint8LiteralAccepted : Bool :=
  sourceUnitAccepted? callUint8LiteralSource

def badCallUint8LiteralFunction : L00_SourceSolidity.FunctionDecl :=
  { callUint8LiteralFunction with
    name := some "badCallSmall"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.ident "takesSmall")
              [L00_SourceSolidity.Arg.positional
                (numberExpr "300")]))) }

def badCallUint8LiteralSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCallUint8Literal"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  takesUint8Function
              , L00_SourceSolidity.ContractItem.function
                  badCallUint8LiteralFunction ] } ] }

def badCallUint8LiteralRejected : Bool :=
  Result.isError (SourceUnit.check badCallUint8LiteralSource)

def uint16TwoExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName uint16)
    [L00_SourceSolidity.Arg.positional (numberExpr "2")]

def arrayLiteralWideningFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "arrayWiden"
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.array uint16 (some 2)
          location := some L00_SourceSolidity.DataLocation.memory } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.array
              [uint8OneExpr, uint16TwoExpr]))) }

def arrayLiteralWideningSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ArrayLiteralWidening"
            items :=
              [L00_SourceSolidity.ContractItem.function
                arrayLiteralWideningFunction] } ] }

def arrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? arrayLiteralWideningSource

def bytes1TwelveExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName
      (L00_SourceSolidity.Ty.bytesN 1))
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [0x12]))]

def bytes2ThirtyFourExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName
      (L00_SourceSolidity.Ty.bytesN 2))
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [0x34, 0x56]))]

def fixedBytesArrayLiteralWideningFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "fixedBytesArrayWiden"
    returns :=
      [ { name := none
          ty :=
            L00_SourceSolidity.Ty.array
              (L00_SourceSolidity.Ty.bytesN 2) (some 2)
          location := some L00_SourceSolidity.DataLocation.memory } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.array
              [bytes1TwelveExpr, bytes2ThirtyFourExpr]))) }

def fixedBytesArrayLiteralWideningSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FixedBytesArrayLiteralWidening"
            items :=
              [L00_SourceSolidity.ContractItem.function
                fixedBytesArrayLiteralWideningFunction] } ] }

def fixedBytesArrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? fixedBytesArrayLiteralWideningSource

def legacyFixedBytes1TwelveExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName
      (L00_SourceSolidity.Ty.fixedBytes 1))
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [0x12]))]

def legacyFixedBytes2ThirtyFourExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName
      (L00_SourceSolidity.Ty.fixedBytes 2))
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [0x34, 0x56]))]

def legacyFixedBytesArrayLiteralWideningFunction :
    L00_SourceSolidity.FunctionDecl :=
  { fixedBytesArrayLiteralWideningFunction with
    name := some "legacyFixedBytesArrayWiden"
    returns :=
      [ { name := none
          ty :=
            L00_SourceSolidity.Ty.array
              (L00_SourceSolidity.Ty.fixedBytes 2) (some 2)
          location := some L00_SourceSolidity.DataLocation.memory } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.array
              [ legacyFixedBytes1TwelveExpr
              , legacyFixedBytes2ThirtyFourExpr ]))) }

def legacyFixedBytesArrayLiteralWideningSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "LegacyFixedBytesArrayLiteralWidening"
            items :=
              [L00_SourceSolidity.ContractItem.function
                legacyFixedBytesArrayLiteralWideningFunction] } ] }

def legacyFixedBytesArrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? legacyFixedBytesArrayLiteralWideningSource

def badArrayLiteralCommonTypeFunction :
    L00_SourceSolidity.FunctionDecl :=
  { arrayLiteralWideningFunction with
    name := some "badArrayCommon"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.array
              [uint8OneExpr, boolExpr true]))) }

def badArrayLiteralCommonTypeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadArrayLiteralCommonType"
            items :=
              [L00_SourceSolidity.ContractItem.function
                badArrayLiteralCommonTypeFunction] } ] }

def badArrayLiteralCommonTypeRejected : Bool :=
  Result.isError (SourceUnit.check badArrayLiteralCommonTypeSource)

def bytes4ValueExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.typeName bytes4)
    [L00_SourceSolidity.Arg.positional
      (L00_SourceSolidity.Expr.literal
        (L00_SourceSolidity.Literal.bytes [1, 2, 3, 4]))]

def shiftWideCountFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "shiftWide"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.shl
              uint8OneExpr
              uint16TwoExpr))) }

def shiftWideCountSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ShiftWideCount"
            items := [L00_SourceSolidity.ContractItem.function
              shiftWideCountFunction] } ] }

def shiftWideCountAccepted : Bool :=
  sourceUnitAccepted? shiftWideCountSource

def badShiftSignedCountFunction : L00_SourceSolidity.FunctionDecl :=
  { shiftWideCountFunction with
    name := some "badShiftSigned"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.shl
              uint8OneExpr
              int8OneExpr))) }

def badShiftSignedCountSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadShiftSignedCount"
            items := [L00_SourceSolidity.ContractItem.function
              badShiftSignedCountFunction] } ] }

def badShiftSignedCountRejected : Bool :=
  Result.isError (SourceUnit.check badShiftSignedCountSource)

def bytesBitwiseFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "bytesBitwise"
    returns := [{ name := none, ty := bytes4, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.bitAnd
              bytes4ValueExpr
              bytes4ValueExpr))) }

def bytesBitwiseSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BytesBitwise"
            items := [L00_SourceSolidity.ContractItem.function
              bytesBitwiseFunction] } ] }

def bytesBitwiseAccepted : Bool :=
  sourceUnitAccepted? bytesBitwiseSource

def badBytesArithmeticFunction : L00_SourceSolidity.FunctionDecl :=
  { bytesBitwiseFunction with
    name := some "badBytesArithmetic"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.add
              bytes4ValueExpr
              bytes4ValueExpr))) }

def badBytesArithmeticSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadBytesArithmetic"
            items := [L00_SourceSolidity.ContractItem.function
              badBytesArithmeticFunction] } ] }

def badBytesArithmeticRejected : Bool :=
  Result.isError (SourceUnit.check badBytesArithmeticSource)

def compoundShiftFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "compoundShift"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [ { name := some "x"
                  ty := some uint8
                  location := none } ]
              (some uint8OneExpr)
          , L00_SourceSolidity.Stmt.expr
              (L00_SourceSolidity.Expr.assign
                (L00_SourceSolidity.Expr.ident "x")
                L00_SourceSolidity.AssignOp.shlAssign
                uint16TwoExpr)
          , L00_SourceSolidity.Stmt.returnValues
              (some (L00_SourceSolidity.Expr.ident "x")) ]) }

def compoundShiftSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "CompoundShift"
            items := [L00_SourceSolidity.ContractItem.function
              compoundShiftFunction] } ] }

def compoundShiftAccepted : Bool :=
  sourceUnitAccepted? compoundShiftSource

def widthAndSignCastSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadCast"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCast"
                    params := [{ name := some "x", ty := int8, location := none }]
                    returns := [{ name := none, ty := uint16, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some badWidthAndSignCastExpr)) } ] } ] }

def widthAndSignCastRejected : Bool :=
  Result.isError (SourceUnit.check widthAndSignCastSource)

def addressCastAcceptedSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AddressCast"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "addr"
                    returns := [{ name := none, ty := addressTy, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some addressCastExpr)) } ] } ] }

def addressCastAccepted : Bool :=
  sourceUnitAccepted? addressCastAcceptedSource

def directPayableTypeConversionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "DirectPayableCast"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableCast"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.typeName payableAddressTy)
                              [L00_SourceSolidity.Arg.positional
                                zeroExpr]))) } ] } ] }

def directPayableTypeConversionRejected : Bool :=
  Result.isError (SourceUnit.check directPayableTypeConversionSource)

def payableZeroSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PayableZero"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableZero"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.payableConversion
                              zeroExpr))) } ] } ] }

def payableZeroAccepted : Bool :=
  sourceUnitAccepted? payableZeroSource

def payableReceiveFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.receive
    name := none
    params := []
    returns := []
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.payable
    body := some L00_SourceSolidity.Stmt.empty }

def typedFallbackFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.fallback
    name := none
    params :=
      [ { name := some "input"
          ty := L00_SourceSolidity.Ty.bytes
          location := some L00_SourceSolidity.DataLocation.calldata } ]
    returns :=
      [ { name := some "output"
          ty := L00_SourceSolidity.Ty.bytes
          location := some L00_SourceSolidity.DataLocation.memory } ]
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body := some L00_SourceSolidity.Stmt.empty }

def typedFallbackSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "TypedFallback"
            items := [L00_SourceSolidity.ContractItem.function
              typedFallbackFunction] } ] }

def typedFallbackAccepted : Bool :=
  sourceUnitAccepted? typedFallbackSource

def badFallbackViewSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadFallbackView"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { typedFallbackFunction with
                    mutability :=
                      L00_SourceSolidity.StateMutability.view } ] } ] }

def badFallbackViewRejected : Bool :=
  Result.isError (SourceUnit.check badFallbackViewSource)

def badFallbackParamSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadFallbackParam"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { typedFallbackFunction with
                    params :=
                      [{ name := some "input"
                         ty := uint256
                         location := none }]
                    returns := [] } ] } ] }

def badFallbackParamRejected : Bool :=
  Result.isError (SourceUnit.check badFallbackParamSource)

def untypedFallbackFunction : L00_SourceSolidity.FunctionDecl :=
  { kind := L00_SourceSolidity.FunctionKind.fallback
    name := none
    params := []
    returns := []
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body := some L00_SourceSolidity.Stmt.empty }

def virtualFallbackFunction : L00_SourceSolidity.FunctionDecl :=
  { untypedFallbackFunction with virtual := true }

def fallbackOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "FallbackBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualFallbackFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "FallbackDerived"
            bases := [{ base := userPath "FallbackBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { typedFallbackFunction with
                    override? := some { bases := [] } } ] } ] }

def fallbackOverrideAccepted : Bool :=
  sourceUnitAccepted? fallbackOverrideSource

def missingFallbackOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "MissingFallbackBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualFallbackFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "MissingFallbackDerived"
            bases := [{ base := userPath "MissingFallbackBase", args := [] }]
            items := [L00_SourceSolidity.ContractItem.function
              untypedFallbackFunction] } ] }

def missingFallbackOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingFallbackOverrideSource)

def payableFallbackOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonpayableFallbackBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualFallbackFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "PayableFallbackDerived"
            bases :=
              [{ base := userPath "NonpayableFallbackBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { untypedFallbackFunction with
                    mutability :=
                      L00_SourceSolidity.StateMutability.payable
                    override? := some { bases := [] } } ] } ] }

def payableFallbackOverrideRejected : Bool :=
  Result.isError (SourceUnit.check payableFallbackOverrideSource)

def virtualReceiveFunction : L00_SourceSolidity.FunctionDecl :=
  { payableReceiveFunction with virtual := true }

def receiveOverrideSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ReceiveBase"
            items := [L00_SourceSolidity.ContractItem.function
              virtualReceiveFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "ReceiveDerived"
            bases := [{ base := userPath "ReceiveBase", args := [] }]
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { payableReceiveFunction with
                    override? := some { bases := [] } } ] } ] }

def receiveOverrideAccepted : Bool :=
  sourceUnitAccepted? receiveOverrideSource

def constructorVirtualSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ConstructorVirtual"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { (seedConstructor
                      L00_SourceSolidity.StateMutability.nonpayable) with
                    virtual := true } ] } ] }

def constructorVirtualRejected : Bool :=
  Result.isError (SourceUnit.check constructorVirtualSource)

def freeVirtualSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeFunction
          { simpleReturnFunction with
            visibility := none
            virtual := true } ] }

def freeVirtualRejected : Bool :=
  Result.isError (SourceUnit.check freeVirtualSource)

def freePayableSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeFunction
          { simpleReturnFunction with
            visibility := none
            mutability :=
              L00_SourceSolidity.StateMutability.payable } ] }

def freePayableRejected : Bool :=
  Result.isError (SourceUnit.check freePayableSource)

def abstractFallbackWithoutVirtualSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbstractFallbackWithoutVirtual"
            abstract := true
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { untypedFallbackFunction with body := none } ] } ] }

def abstractFallbackWithoutVirtualRejected : Bool :=
  Result.isError (SourceUnit.check abstractFallbackWithoutVirtualSource)

def payableContractConversionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "PayableTarget"
            items := [L00_SourceSolidity.ContractItem.function
              payableReceiveFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "PayableContractConversion"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "target"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "PayableTarget") }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "asPayable"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.payableConversion
                              (L00_SourceSolidity.Expr.ident "target")))) } ] } ] }

def payableContractConversionAccepted : Bool :=
  sourceUnitAccepted? payableContractConversionSource

def nonpayableContractConversionSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "NonpayableTarget", items := [] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadPayableContractConversion"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "target"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "NonpayableTarget") }
              , L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "asPayable"
                    mutability :=
                      L00_SourceSolidity.StateMutability.nonpayable
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.payableConversion
                              (L00_SourceSolidity.Expr.ident "target")))) } ] } ] }

def nonpayableContractConversionRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableContractConversionSource)

def priceTy : Ty :=
  L00_SourceSolidity.Ty.user (userPath "Price")

def priceDecl : L00_SourceSolidity.UserValueTypeDecl :=
  { name := "Price", underlying := uint256 }

def wrappedPriceOneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
    [L00_SourceSolidity.Arg.positional oneExpr]

def unwrappedPriceOneExpr : L00_SourceSolidity.Expr :=
  L00_SourceSolidity.Expr.call
    (L00_SourceSolidity.Expr.member
      (L00_SourceSolidity.Expr.typeName priceTy) "unwrap")
    [L00_SourceSolidity.Arg.positional wrappedPriceOneExpr]

def userValueWrapUnwrapSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.contract
          { name := "UserValueWrap"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "unwrap"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some unwrappedPriceOneExpr)) } ] } ] }

def userValueWrapUnwrapAccepted : Bool :=
  sourceUnitAccepted? userValueWrapUnwrapSource

def badUserValueUnwrapSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadUserValueUnwrap"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "unwrap"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.typeName priceTy)
                                "unwrap")
                              [L00_SourceSolidity.Arg.positional
                                oneExpr]))) } ] } ] }

def badUserValueUnwrapRejected : Bool :=
  Result.isError (SourceUnit.check badUserValueUnwrapSource)

def priceMathPlusOneFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "inc"
    visibility := some L00_SourceSolidity.Visibility.internal_
    params :=
      [{ name := some "self"
         ty := priceTy
         location := none }]
    returns :=
      [{ name := some "out"
         ty := priceTy
         location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.binary
                    L00_SourceSolidity.BinaryOp.add
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.typeName priceTy)
                        "unwrap")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "self")])
                    (numberExpr "1")) ]))) }

def priceMathLibrary : L00_SourceSolidity.ContractDecl :=
  { kind := L00_SourceSolidity.ContractKind.library
    name := "PriceMath"
    items :=
      [L00_SourceSolidity.ContractItem.function
        priceMathPlusOneFunction] }

def globalUsingPriceFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "run"
    params :=
      [{ name := some "raw"
         ty := uint256
         location := none }]
    returns :=
      [{ name := some "out"
         ty := uint256
         location := none }]
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [{ name := some "price"
                 ty := some priceTy
                 location := none }]
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.member
                    (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "raw")]))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.member
                    (L00_SourceSolidity.Expr.typeName priceTy) "unwrap")
                  [ L00_SourceSolidity.Arg.positional
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.ident "price") "inc")
                        []) ])) ]) }

def globalUsingPriceSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.contract priceMathLibrary
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "PriceMath"
            target := some priceTy
            global := true }
      , L00_SourceSolidity.SourceItem.contract
          { name := "GlobalUsingPrice"
            items :=
              [L00_SourceSolidity.ContractItem.function
                globalUsingPriceFunction] } ] }

def globalUsingPriceAccepted : Bool :=
  sourceUnitAccepted? globalUsingPriceSource

def priceOperatorAddFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "priceAdd"
    params :=
      [ { name := some "left", ty := priceTy, location := none }
      , { name := some "right", ty := priceTy, location := none } ]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.binary
                    L00_SourceSolidity.BinaryOp.add
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.typeName priceTy)
                        "unwrap")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "left")])
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.typeName priceTy)
                        "unwrap")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "right")])) ]))) }

def priceOperatorLtFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "priceLt"
    params :=
      [ { name := some "left", ty := priceTy, location := none }
      , { name := some "right", ty := priceTy, location := none } ]
    returns := [{ name := some "out", ty := L00_SourceSolidity.Ty.bool }]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.binary
              L00_SourceSolidity.BinaryOp.lt
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.member
                  (L00_SourceSolidity.Expr.typeName priceTy) "unwrap")
                [L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.ident "left")])
              (L00_SourceSolidity.Expr.call
                (L00_SourceSolidity.Expr.member
                  (L00_SourceSolidity.Expr.typeName priceTy) "unwrap")
                [L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.ident "right")])))) }

def priceOperatorNegFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "priceNeg"
    params := [{ name := some "value", ty := priceTy, location := none }]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.binary
                    L00_SourceSolidity.BinaryOp.add
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.typeName priceTy)
                        "unwrap")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "value")])
                    (numberExpr "1")) ]))) }

def priceOperatorBitNotFunction : L00_SourceSolidity.FunctionDecl :=
  { name := some "priceBitNot"
    params := [{ name := some "value", ty := priceTy, location := none }]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := L00_SourceSolidity.StateMutability.pure
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
              [ L00_SourceSolidity.Arg.positional
                  (L00_SourceSolidity.Expr.binary
                    L00_SourceSolidity.BinaryOp.add
                    (L00_SourceSolidity.Expr.call
                      (L00_SourceSolidity.Expr.member
                        (L00_SourceSolidity.Expr.typeName priceTy)
                        "unwrap")
                      [L00_SourceSolidity.Arg.positional
                        (L00_SourceSolidity.Expr.ident "value")])
                    (numberExpr "2")) ]))) }

def globalUsingPriceOperatorFunction :
    L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "runOperator"
    params :=
      [ { name := some "left", ty := uint256, location := none }
      , { name := some "right", ty := uint256, location := none } ]
    returns :=
      [ { name := some "sum", ty := uint256, location := none }
      , { name := some "less", ty := L00_SourceSolidity.Ty.bool,
          location := none }
      , { name := some "negated", ty := uint256, location := none }
      , { name := some "inverted", ty := uint256, location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.block
          [ L00_SourceSolidity.Stmt.varDecl
              [{ name := some "a", ty := some priceTy, location := none }]
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.member
                    (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "left")]))
          , L00_SourceSolidity.Stmt.varDecl
              [{ name := some "b", ty := some priceTy, location := none }]
              (some
                (L00_SourceSolidity.Expr.call
                  (L00_SourceSolidity.Expr.member
                    (L00_SourceSolidity.Expr.typeName priceTy) "wrap")
                  [L00_SourceSolidity.Arg.positional
                    (L00_SourceSolidity.Expr.ident "right")]))
          , L00_SourceSolidity.Stmt.returnValues
              (some
                (L00_SourceSolidity.Expr.tuple
                  [ L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.typeName priceTy)
                          "unwrap")
                        [ L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.binary
                              L00_SourceSolidity.BinaryOp.add
                              (L00_SourceSolidity.Expr.ident "a")
                              (L00_SourceSolidity.Expr.ident "b")) ])
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.binary
                        L00_SourceSolidity.BinaryOp.lt
                        (L00_SourceSolidity.Expr.ident "a")
                        (L00_SourceSolidity.Expr.ident "b"))
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.typeName priceTy)
                          "unwrap")
                        [ L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.neg
                              (L00_SourceSolidity.Expr.ident "a")) ])
                  , L00_SourceSolidity.TupleItem.value
                      (L00_SourceSolidity.Expr.call
                        (L00_SourceSolidity.Expr.member
                          (L00_SourceSolidity.Expr.typeName priceTy)
                          "unwrap")
                        [ L00_SourceSolidity.Arg.positional
                            (L00_SourceSolidity.Expr.unary
                              L00_SourceSolidity.UnaryOp.bitNot
                              (L00_SourceSolidity.Expr.ident "a")) ]) ])) ]) }

def globalUsingPriceOperatorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorLtFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorNegFunction
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorBitNotFunction
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [ { function := { segments := ["priceAdd"] }
                  operator? := some
                    (L00_SourceSolidity.UsingOperator.binary
                      L00_SourceSolidity.BinaryOp.add) }
              , { function := { segments := ["priceLt"] }
                  operator? := some
                    (L00_SourceSolidity.UsingOperator.binary
                      L00_SourceSolidity.BinaryOp.lt) }
              , { function := { segments := ["priceNeg"] }
                  operator? := some
                    (L00_SourceSolidity.UsingOperator.unary
                      L00_SourceSolidity.UnaryOp.neg) }
              , { function := { segments := ["priceBitNot"] }
                  operator? := some
                    (L00_SourceSolidity.UsingOperator.unary
                      L00_SourceSolidity.UnaryOp.bitNot) } ]
            target := some priceTy
            global := true }
      , L00_SourceSolidity.SourceItem.contract
          { name := "GlobalUsingPriceOperator"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  globalUsingPriceOperatorFunction ] } ] }

def globalUsingPriceOperatorAccepted : Bool :=
  sourceUnitAccepted? globalUsingPriceOperatorSource

def contractUsingOperatorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadContractUsingOperator"
            items :=
              [ L00_SourceSolidity.ContractItem.usingDecl
                  { library := { segments := [] }
                    functions :=
                      [{ function := { segments := ["priceAdd"] }
                         operator? := some
                          (L00_SourceSolidity.UsingOperator.binary
                            L00_SourceSolidity.BinaryOp.add) }]
                    target := some priceTy } ] } ] }

def contractUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check contractUsingOperatorSource)

def nonPurePriceOperatorAddFunction :
    L00_SourceSolidity.FunctionDecl :=
  { priceOperatorAddFunction with
    mutability := L00_SourceSolidity.StateMutability.view }

def nonPureUsingOperatorSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.freeFunction
          nonPurePriceOperatorAddFunction
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAdd"] }
                 operator? := some
                  (L00_SourceSolidity.UsingOperator.binary
                    L00_SourceSolidity.BinaryOp.add) }]
            target := some priceTy
            global := true } ] }

def nonPureUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check nonPureUsingOperatorSource)

def contractGlobalUsingSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.contract priceMathLibrary
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadContractGlobalUsing"
            items :=
              [ L00_SourceSolidity.ContractItem.usingDecl
                  { library := userPath "PriceMath"
                    target := some priceTy
                    global := true } ] } ] }

def contractGlobalUsingRejected : Bool :=
  Result.isError (SourceUnit.check contractGlobalUsingSource)

def globalUsingNonUserValueSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.freeUserValueType priceDecl
      , L00_SourceSolidity.SourceItem.contract priceMathLibrary
      , L00_SourceSolidity.SourceItem.usingDecl
          { library := userPath "PriceMath"
            target := some uint256
            global := true } ] }

def globalUsingNonUserValueRejected : Bool :=
  Result.isError (SourceUnit.check globalUsingNonUserValueSource)

def bytesReturnFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    returns :=
      [ { name := none
          ty := L00_SourceSolidity.Ty.bytes
          location := some L00_SourceSolidity.DataLocation.memory } ] }

def abiEncodeExternalFunctionPointerFunction :
    L00_SourceSolidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some "packExternalFunction"
    params :=
      [ { name := some "getter"
          ty := externalPureUintFunctionTy
          location := none } ]
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "abi")
                "encode")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "getter")]))) }

def abiEncodeExternalFunctionPointerSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbiEncodeExternalFunctionPointer"
            items :=
              [L00_SourceSolidity.ContractItem.function
                abiEncodeExternalFunctionPointerFunction] } ] }

def abiEncodeExternalFunctionPointerAccepted : Bool :=
  sourceUnitAccepted? abiEncodeExternalFunctionPointerSource

def abiEncodeInternalFunctionPointerFunction :
    L00_SourceSolidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some "packInternalFunction"
    body :=
      some
        (L00_SourceSolidity.Stmt.returnValues
          (some
            (L00_SourceSolidity.Expr.call
              (L00_SourceSolidity.Expr.member
                (L00_SourceSolidity.Expr.ident "abi")
                "encode")
              [L00_SourceSolidity.Arg.positional
                (L00_SourceSolidity.Expr.ident "internalTarget")]))) }

def abiEncodeInternalFunctionPointerSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiEncodeInternalFunctionPointer"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "internalTarget"
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_ }
              , L00_SourceSolidity.ContractItem.function
                  abiEncodeInternalFunctionPointerFunction ] } ] }

def abiEncodeInternalFunctionPointerRejected : Bool :=
  Result.isError
    (SourceUnit.check abiEncodeInternalFunctionPointerSource)

def abiDecodeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbiDecode"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "decode"
                    params :=
                      [ { name := some "data"
                          ty := L00_SourceSolidity.Ty.bytes
                          location :=
                            some L00_SourceSolidity.DataLocation.memory } ]
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "decode")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident "data")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.typeName
                                    uint256) ]))) } ] } ] }

def abiDecodeAccepted : Bool :=
  sourceUnitAccepted? abiDecodeSource

def badAbiDecodeSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiDecode"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "decode"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "decode")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.bool true))
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.typeName
                                    uint256) ]))) } ] } ] }

def badAbiDecodeRejected : Bool :=
  Result.isError (SourceUnit.check badAbiDecodeSource)

def bytesConcatSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BytesConcat"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "bytes")
                                "concat")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.literal
                                    (L00_SourceSolidity.Literal.bytes [1]))
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.call
                                    (L00_SourceSolidity.Expr.typeName bytes4)
                                    [L00_SourceSolidity.Arg.positional
                                      zeroExpr]) ]))) } ] } ] }

def bytesConcatAccepted : Bool :=
  sourceUnitAccepted? bytesConcatSource

def badBytesConcatSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadBytesConcat"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "bytes")
                                "concat")
                              [L00_SourceSolidity.Arg.positional
                                oneExpr]))) } ] } ] }

def badBytesConcatRejected : Bool :=
  Result.isError (SourceUnit.check badBytesConcatSource)

def encodeCallTargetFunction : L00_SourceSolidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "set"
    params := [{ name := some "value", ty := uint256, location := none }]
    returns := []
    visibility := some L00_SourceSolidity.Visibility.external_
    mutability := L00_SourceSolidity.StateMutability.nonpayable
    body := some L00_SourceSolidity.Stmt.empty }

def abiEncodeCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [L00_SourceSolidity.ContractItem.function
              encodeCallTargetFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "AbiEncodeCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "target"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident "target")
                                    "set")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallSource

def badAbiEncodeCallSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [L00_SourceSolidity.ContractItem.function
              encodeCallTargetFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiEncodeCall"
            items :=
              [ L00_SourceSolidity.ContractItem.stateVar
                  { name := "target"
                    ty := L00_SourceSolidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := L00_SourceSolidity.StateMutability.view
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident "target")
                                    "set")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      (L00_SourceSolidity.Expr.literal
                                        (L00_SourceSolidity.Literal.bool
                                          true))]) ]))) } ] } ] }

def badAbiEncodeCallRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallSource)

def abiEncodeCallTypeNameSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [L00_SourceSolidity.ContractItem.function
              encodeCallTargetFunction] }
      , L00_SourceSolidity.SourceItem.contract
          { name := "AbiEncodeCallTypeName"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.typeName
                                      (L00_SourceSolidity.Ty.user
                                        (userPath "EncodeCallTarget")))
                                    "set")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallTypeNameAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallTypeNameSource

def externalUintSetterFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [uint256] []
    L00_SourceSolidity.StateMutability.nonpayable
    L00_SourceSolidity.Visibility.external_

def internalUintSetterFunctionTy : Ty :=
  L00_SourceSolidity.Ty.function [uint256] []
    L00_SourceSolidity.StateMutability.nonpayable
    L00_SourceSolidity.Visibility.internal_

def abiEncodeCallExternalFunctionPointerSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "AbiEncodeCallExternalPointer"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    params :=
                      [ { name := some "setter"
                          ty := externalUintSetterFunctionTy
                          location := none } ]
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident "setter")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallExternalFunctionPointerAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallExternalFunctionPointerSource

def externalFunctionPointerMembersSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "ExternalFunctionPointerMembers"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "members"
                    params :=
                      [ { name := some "setter"
                          ty := externalUintSetterFunctionTy
                          location := none } ]
                    returns :=
                      [ { name := some "selector"
                          ty := bytes4
                          location := none }
                      , { name := some "target"
                          ty := addressTy
                          location := none } ]
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.tuple
                              [ L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident
                                      "setter")
                                    "selector")
                              , L00_SourceSolidity.TupleItem.value
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident
                                      "setter")
                                    "address") ]))) } ] } ] }

def externalFunctionPointerMembersAccepted : Bool :=
  sourceUnitAccepted? externalFunctionPointerMembersSource

def badInternalFunctionPointerSelectorSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadInternalFunctionPointerSelector"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "selector"
                    params :=
                      [ { name := some "setter"
                          ty := internalUintSetterFunctionTy
                          location := none } ]
                    returns :=
                      [{ name := some "selector"
                         ty := bytes4
                         location := none }]
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.member
                              (L00_SourceSolidity.Expr.ident "setter")
                              "selector"))) } ] } ] }

def badInternalFunctionPointerSelectorRejected : Bool :=
  Result.isError
    (SourceUnit.check badInternalFunctionPointerSelectorSource)

def badAbiEncodeCallInternalFunctionPointerSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiEncodeCallInternalPointer"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    params :=
                      [ { name := some "setter"
                          ty := internalUintSetterFunctionTy
                          location := none } ]
                    visibility :=
                      some L00_SourceSolidity.Visibility.internal_
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident "setter")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallInternalFunctionPointerRejected : Bool :=
  Result.isError
    (SourceUnit.check badAbiEncodeCallInternalFunctionPointerSource)

def badAbiEncodeCallBareFunctionSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiEncodeCallBareFunction"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  encodeCallTargetFunction
              , L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.ident "set")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallBareFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallBareFunctionSource)

def badAbiEncodeCallThisInPureSource :
    L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadAbiEncodeCallThisInPure"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  encodeCallTargetFunction
              , L00_SourceSolidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.member
                                (L00_SourceSolidity.Expr.ident "abi")
                                "encodeCall")
                              [ L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.member
                                    (L00_SourceSolidity.Expr.ident "this")
                                    "set")
                              , L00_SourceSolidity.Arg.positional
                                  (L00_SourceSolidity.Expr.tuple
                                    [L00_SourceSolidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallThisInPureRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallThisInPureSource)

def badPureAddressThisSource : L00_SourceSolidity.SourceUnit :=
  { items :=
      [ L00_SourceSolidity.SourceItem.contract
          { name := "BadPureAddressThis"
            items :=
              [ L00_SourceSolidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "self"
                    returns :=
                      [ { name := none
                          ty := addressTy
                          location := none } ]
                    mutability := L00_SourceSolidity.StateMutability.pure
                    body :=
                      some
                        (L00_SourceSolidity.Stmt.returnValues
                          (some
                            (L00_SourceSolidity.Expr.call
                              (L00_SourceSolidity.Expr.typeName addressTy)
                              [L00_SourceSolidity.Arg.positional
                                (L00_SourceSolidity.Expr.ident
                                  "this")]))) } ] } ] }

def badPureAddressThisRejected : Bool :=
  Result.isError (SourceUnit.check badPureAddressThisSource)

end Examples

end TypeCheck
end L00_SourceSolidity
end Spine
end SolidCore

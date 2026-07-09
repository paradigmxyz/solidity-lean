/-
Witness corpus extracted verbatim from TypeCheck.lean (Phase 3, sub-step a).

Hand-written example/witness definitions moved out of the semantics module.
Declaration names and namespaces are unchanged so the harness manifest's
`SolidCore.Solidity.TypeCheck.Examples` eval expressions still resolve; only the manifest `lean.imports` target
gains this module.
-/
import SolidCore.Solidity.TypeCheck
import SolidCore.Witness.Interface

namespace SolidCore
namespace Solidity
namespace TypeCheck

namespace Examples

def uint256 : Ty := Solidity.Ty.uint 256

def int256 : Ty := Solidity.Ty.int 256

def numberExpr (value : String) : Solidity.Expr :=
  Solidity.Expr.literal
    (Solidity.Literal.number value)

def boolExpr (value : Bool) : Solidity.Expr :=
  Solidity.Expr.literal
    (Solidity.Literal.bool value)

def userPath (name : Name) : Path :=
  { segments := [name] }

def simpleReturnFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "f"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.literal
              (Solidity.Literal.number "7")))) }

def simpleSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "C"
          items := [Solidity.ContractItem.function
            simpleReturnFunction] }] }

def simpleSourceAccepted : Bool :=
  sourceUnitAccepted? simpleSource

def pragmaSimpleSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "solidity" "^0.8.35"
      , Solidity.SourceItem.contract
          { name := "PragmaC"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaSimpleSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaSimpleSource

def pragmaSourceWithVersion
    (version contractName : String) : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "solidity" version
      , Solidity.SourceItem.contract
          { name := contractName
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaWildcardSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "0.8.x" "PragmaWildcard"

def pragmaWildcardSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaWildcardSource

def pragmaStarSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "*" "PragmaStar"

def pragmaStarSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaStarSource

def pragmaWildcardComparatorSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion ">=0.8.x" "PragmaWildcardComparator"

def pragmaWildcardComparatorSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaWildcardComparatorSource

def pragmaHyphenSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "0.8.34 - 0.8.36" "PragmaHyphen"

def pragmaHyphenSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaHyphenSource

def pragmaCompactHyphenSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "0.8.34-0.8.36" "PragmaCompactHyphen"

def pragmaCompactHyphenSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaCompactHyphenSource

def pragmaHyphenWildcardSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "0.8.34 - 0.8.x" "PragmaHyphenWildcard"

def pragmaHyphenWildcardSourceAccepted : Bool :=
  sourceUnitAccepted? pragmaHyphenWildcardSource

def pragmaVersionSyntaxAccepted : Bool :=
  pragmaSimpleSourceAccepted &&
    pragmaWildcardSourceAccepted &&
    pragmaStarSourceAccepted &&
    pragmaWildcardComparatorSourceAccepted &&
    pragmaHyphenSourceAccepted &&
    pragmaCompactHyphenSourceAccepted &&
    pragmaHyphenWildcardSourceAccepted

def pragmaBadHyphenSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "0.8.36 - 0.8.40" "PragmaBadHyphen"

def pragmaBadWildcardRangeSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "^0.9.x" "PragmaBadWildcardRange"

def pragmaBadGreaterSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion ">0.8.35" "PragmaBadGreater"

def pragmaBadLessWildcardSource : Solidity.SourceUnit :=
  pragmaSourceWithVersion "<0.8.x" "PragmaBadLessWildcard"

def pragmaVersionSyntaxRejected : Bool :=
  Result.isError (SourceUnit.check pragmaBadHyphenSource) &&
    Result.isError (SourceUnit.check pragmaBadWildcardRangeSource) &&
    Result.isError (SourceUnit.check pragmaBadGreaterSource) &&
    Result.isError (SourceUnit.check pragmaBadLessWildcardSource)

def unknownPragmaSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "unknown" "feature"
      , Solidity.SourceItem.contract
          { name := "UnknownPragma"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def badExperimentalPragmaSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "experimental" "UnknownFeature"
      , Solidity.SourceItem.contract
          { name := "BadExperimentalPragma"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def duplicateExperimentalPragmaSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "experimental" "SMTChecker"
      , Solidity.SourceItem.pragma "experimental" "SMTChecker"
      , Solidity.SourceItem.contract
          { name := "DuplicateExperimentalPragma"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaDirectiveSyntaxRejected : Bool :=
  Result.isError (SourceUnit.check unknownPragmaSource) &&
    Result.isError (SourceUnit.check badExperimentalPragmaSource) &&
    Result.isError (SourceUnit.check duplicateExperimentalPragmaSource)

def unresolvedImportSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.importPath "./Other.sol" none
      , Solidity.SourceItem.contract
          { name := "ImportC"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def unresolvedImportRejected : Bool :=
  Result.isError (SourceUnit.check unresolvedImportSource)

def badIfFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    body :=
      some
        (Solidity.Stmt.ifElse
          (Solidity.Expr.literal
            (Solidity.Literal.number "1"))
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.literal
                (Solidity.Literal.number "1"))))
          (some
            (Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "0")))))) }

def badIfSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "C"
          items := [Solidity.ContractItem.function badIfFunction] }] }

def badIfRejected : Bool :=
  Result.isError (SourceUnit.check badIfSource)

def pointStruct : Solidity.StructDecl :=
  { name := "Point"
    fields := [{ name := "x", ty := uint256 }] }

def pointTy : Ty :=
  Solidity.Ty.user (userPath "Point")

def pairStruct : Solidity.StructDecl :=
  { name := "Pair"
    fields :=
      [ { name := "x", ty := uint256 }
      , { name := "y", ty := uint256 } ] }

def pairTy : Ty :=
  Solidity.Ty.user (userPath "Pair")

def pairConstructorNamedReverseExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName pairTy)
    [ Solidity.Arg.named "y" (numberExpr "2")
    , Solidity.Arg.named "x" (numberExpr "1") ]

def pairConstructorFieldFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pairX"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              pairConstructorNamedReverseExpr "x"))) }

def pairConstructorFieldSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "StructCtor"
            items :=
              [Solidity.ContractItem.function
                pairConstructorFieldFunction] } ] }

def pairConstructorFieldAccepted : Bool :=
  sourceUnitAccepted? pairConstructorFieldSource

def badPairConstructorMissingFieldFunction :
    Solidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName pairTy)
              [Solidity.Arg.named "x" (numberExpr "1")]))) }

def badPairConstructorMissingFieldSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "BadStructCtor"
            items :=
              [Solidity.ContractItem.function
                badPairConstructorMissingFieldFunction] } ] }

def badPairConstructorMissingFieldRejected : Bool :=
  Result.isError (SourceUnit.check badPairConstructorMissingFieldSource)

def badPairConstructorMixedArgsFunction :
    Solidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName pairTy)
              [ Solidity.Arg.positional (numberExpr "1")
              , Solidity.Arg.named "y" (numberExpr "2") ]))) }

def badPairConstructorMixedArgsSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "BadMixedStructCtor"
            items :=
              [Solidity.ContractItem.function
                badPairConstructorMixedArgsFunction] } ] }

def badPairConstructorMixedArgsRejected : Bool :=
  Result.isError (SourceUnit.check badPairConstructorMixedArgsSource)

def badStructFieldFunction : Solidity.FunctionDecl :=
  { pairConstructorFieldFunction with
    name := some "badField"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              pairConstructorNamedReverseExpr "z"))) }

def badStructFieldSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "BadStructField"
            items :=
              [Solidity.ContractItem.function
                badStructFieldFunction] } ] }

def badStructFieldRejected : Bool :=
  Result.isError (SourceUnit.check badStructFieldSource)

def mutualRecursiveStructATy : Ty :=
  Solidity.Ty.user (userPath "MutualRecursiveA")

def mutualRecursiveStructBTy : Ty :=
  Solidity.Ty.user (userPath "MutualRecursiveB")

def mutualRecursiveStructA : Solidity.StructDecl :=
  { name := "MutualRecursiveA"
    fields := [{ name := "b", ty := mutualRecursiveStructBTy }] }

def mutualRecursiveStructB : Solidity.StructDecl :=
  { name := "MutualRecursiveB"
    fields := [{ name := "a", ty := mutualRecursiveStructATy }] }

def mutualRecursiveStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct mutualRecursiveStructA
      , Solidity.SourceItem.freeStruct mutualRecursiveStructB ] }

def mutualRecursiveStructRejected : Bool :=
  Result.isError (SourceUnit.check mutualRecursiveStructSource)

def dynamicRecursiveStructTy : Ty :=
  Solidity.Ty.user (userPath "DynamicRecursive")

def dynamicRecursiveStruct : Solidity.StructDecl :=
  { name := "DynamicRecursive"
    fields :=
      [ { name := "items"
          ty := Solidity.Ty.array dynamicRecursiveStructTy none } ] }

def dynamicRecursiveStructSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.freeStruct dynamicRecursiveStruct] }

def dynamicRecursiveStructAccepted : Bool :=
  sourceUnitAccepted? dynamicRecursiveStructSource

def functionPointerRecursiveStructTy : Ty :=
  Solidity.Ty.user (userPath "FunctionPointerRecursive")

def functionPointerRecursiveStruct : Solidity.StructDecl :=
  { name := "FunctionPointerRecursive"
    fields :=
      [ { name := "fn"
          ty :=
            Solidity.Ty.function
              [functionPointerRecursiveStructTy] []
              Solidity.StateMutability.nonpayable
              Solidity.Visibility.internal_ } ] }

def functionPointerRecursiveStructSource :
    Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.freeStruct
        functionPointerRecursiveStruct] }

def functionPointerRecursiveStructAccepted : Bool :=
  sourceUnitAccepted? functionPointerRecursiveStructSource

def structFieldAssignFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "writeField"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.member
                  (Solidity.Expr.ident "p") "x")
                Solidity.AssignOp.assign
                (numberExpr "3"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def structFieldAssignViewFunction : Solidity.FunctionDecl :=
  { structFieldAssignFunction with
    name := some "writeFieldView"
    mutability := Solidity.StateMutability.view }

def structFieldAssignSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "StructStorage"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "p", ty := pairTy }
              , Solidity.ContractItem.function
                  structFieldAssignFunction ] } ] }

def structFieldAssignAccepted : Bool :=
  sourceUnitAccepted? structFieldAssignSource

def structFieldAssignViewSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "BadStructStorage"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "p", ty := pairTy }
              , Solidity.ContractItem.function
                  structFieldAssignViewFunction ] } ] }

def structFieldAssignViewRejected : Bool :=
  Result.isError (SourceUnit.check structFieldAssignViewSource)

def uintArrayTy : Ty :=
  Solidity.Ty.array uint256 none

def storageAliasFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "storageAlias"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.storage } ]
              (some (Solidity.Expr.ident "arr"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))
                Solidity.AssignOp.assign
                (numberExpr "1"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageAliasSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageAlias"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  storageAliasFunction ] } ] }

def storageAliasAccepted : Bool :=
  sourceUnitAccepted? storageAliasSource

def storageReturnGetterFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "getArr"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.view
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "arr"))) }

def storageReturnSingleBindingFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "bindReturnedStorage"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.storage } ]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "getArr") []))
          , Solidity.Stmt.expr
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "push")
                [Solidity.Arg.positional (numberExpr "1")])
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "length")) ]) }

def storageReturnTupleFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "getArrAndValue"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.view
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage }
      , { name := none
          ty := uint256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value
                  (Solidity.Expr.ident "arr")
              , Solidity.TupleItem.value (numberExpr "1") ]))) }

def storageReturnTupleBindingFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "bindReturnedStorageTuple"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.storage }
              , { name := some "value"
                  ty := some uint256
                  location := none } ]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "getArrAndValue") []))
          , Solidity.Stmt.expr
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "push")
                [Solidity.Arg.positional
                  (Solidity.Expr.ident "value")])
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "length")) ]) }

def storageReturnDirectMutationFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "mutateReturnedStorage"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "getArr") []) "push")
                [Solidity.Arg.positional (numberExpr "1")])
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.index
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "getArr") [])
                  (numberExpr "0"))
                Solidity.AssignOp.assign
                (numberExpr "2"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageReturnBindingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageReturnBinding"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  storageReturnGetterFunction
              , Solidity.ContractItem.function
                  storageReturnSingleBindingFunction
              , Solidity.ContractItem.function
                  storageReturnTupleFunction
              , Solidity.ContractItem.function
                  storageReturnTupleBindingFunction
              , Solidity.ContractItem.function
                  storageReturnDirectMutationFunction ] } ] }

def storageReturnBindingAccepted : Bool :=
  sourceUnitAccepted? storageReturnBindingSource

def memoryToStorageReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStorageReturn"
            items :=
              [ Solidity.ContractItem.function
                  { storageReturnGetterFunction with
                    name := some "badStorageReturn"
                    mutability :=
                      Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (Solidity.Expr.newExpr uintArrayTy
                                  [ Solidity.Arg.positional
                                      (numberExpr "1") ]))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "local")) ]) } ] } ] }

def memoryToStorageReturnRejected : Bool :=
  Result.isError (SourceUnit.check memoryToStorageReturnSource)

def uninitializedStorageAliasSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStorageAlias"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badStorageAlias"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              none
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def uninitializedStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check uninitializedStorageAliasSource)

def memoryToStorageAliasSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryToStorageAlias"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMemoryAlias"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.ident "input"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryToStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check memoryToStorageAliasSource)

def viewWritesStorageAliasSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewWritesStorageAlias"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { storageAliasFunction with
                    name := some "badViewAliasWrite"
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def viewWritesStorageAliasRejected : Bool :=
  Result.isError (SourceUnit.check viewWritesStorageAliasSource)

def storageParamHelperFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "touch"
    params :=
      [ { name := some "a"
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage } ]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.index
                  (Solidity.Expr.ident "a")
                  (numberExpr "0"))
                Solidity.AssignOp.assign
                (numberExpr "1"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageParamCallerFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callTouch"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "touch")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "arr")]))) }

def storageParamCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageParamCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  storageParamHelperFunction
              , Solidity.ContractItem.function
                  storageParamCallerFunction ] } ] }

def storageParamCallAccepted : Bool :=
  sourceUnitAccepted? storageParamCallSource

def memoryToStorageParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStorageParamCall"
            items :=
              [ Solidity.ContractItem.function
                  storageParamHelperFunction
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCallTouch"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "touch")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "input")])))} ] } ] }

def memoryToStorageParamRejected : Bool :=
  Result.isError (SourceUnit.check memoryToStorageParamSource)

def publicStorageParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicStorageParam"
            items :=
              [ Solidity.ContractItem.function
                  { storageParamHelperFunction with
                    name := some "badPublicStorageParam"
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicStorageParamRejected : Bool :=
  Result.isError (SourceUnit.check publicStorageParamSource)

def libraryStorageParamFunction : Solidity.FunctionDecl :=
  { storageParamHelperFunction with
    name := some "touchPublic"
    visibility := some Solidity.Visibility.public_ }

def libraryStorageParamCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callLibraryTouch"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "ArrayLib")
                "touchPublic")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "arr")]))) }

def libraryStorageParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "ArrayLib"
            items :=
              [Solidity.ContractItem.function
                libraryStorageParamFunction] }
      , Solidity.SourceItem.contract
          { name := "LibraryStorageParam"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  libraryStorageParamCallFunction ] } ] }

def libraryStorageParamAccepted : Bool :=
  sourceUnitAccepted? libraryStorageParamSource

def payableLibraryFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "payMe"
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.payable }

def payableLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "PayableLibrary"
            items :=
              [Solidity.ContractItem.function
                payableLibraryFunction] } ] }

def payableLibraryRejected : Bool :=
  Result.isError (SourceUnit.check payableLibrarySource)

def calldataArrayCopyFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "copyFromCalldata"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some (Solidity.Expr.ident "input"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))) ]) }

def calldataArrayCopySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArrayCopy"
            items :=
              [Solidity.ContractItem.function
                calldataArrayCopyFunction] } ] }

def calldataArrayCopyAccepted : Bool :=
  sourceUnitAccepted? calldataArrayCopySource

def memoryToCalldataLocalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badMemoryToCalldataLocal"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some (Solidity.Expr.ident "input"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def memoryToCalldataReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badMemoryToCalldataReturn"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "input"))) }

def calldataInternalHelperFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "calldataHelper"
    visibility := some Solidity.Visibility.internal_
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ] }

def memoryToCalldataInternalCallFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badMemoryToCalldataCall"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "calldataHelper")
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "input") ]))) }

def storageToCalldataLocalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badStorageToCalldataLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some (Solidity.Expr.ident "stored"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageToCalldataReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badStorageToCalldataReturn"
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "stored"))) }

def storageToCalldataInternalCallFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badStorageToCalldataCall"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "calldataHelper")
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "stored") ]))) }

def calldataToCalldataLocalFunction : Solidity.FunctionDecl :=
  { memoryToCalldataLocalFunction with
    name := some "calldataToCalldataLocal"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ] }

def calldataToCalldataReturnFunction : Solidity.FunctionDecl :=
  { memoryToCalldataReturnFunction with
    name := some "calldataToCalldataReturn"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ] }

def calldataToCalldataInternalCallFunction :
    Solidity.FunctionDecl :=
  { memoryToCalldataInternalCallFunction with
    name := some "calldataToCalldataCall"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ] }

def calldataAliasReassignmentFunction
    (name rhs : Name) : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [ { name := some "memoryInput"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory }
      , { name := some "calldataInput"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some (Solidity.Expr.ident "calldataInput"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "local")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident rhs))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageToCalldataReassignmentFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badStorageToCalldataReassignment"
    params :=
      [ { name := some "calldataInput"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some (Solidity.Expr.ident "calldataInput"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "local")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "stored"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def referencePairFunction (name : Name)
    (location : Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    visibility := some Solidity.Visibility.internal_
    params :=
      [ { name := some "left"
          ty := uintArrayTy
          location := some location }
      , { name := some "right"
          ty := uintArrayTy
          location := some location } ]
    returns :=
      [ { name := none, ty := uintArrayTy, location := some location }
      , { name := none, ty := uintArrayTy, location := some location } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value
                  (Solidity.Expr.ident "left")
              , Solidity.TupleItem.value
                  (Solidity.Expr.ident "right") ]))) }

def referencePairBindingFunction (name helper : Name)
    (paramLocation : Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [ { name := some "left"
          ty := uintArrayTy
          location := some paramLocation }
      , { name := some "right"
          ty := uintArrayTy
          location := some paramLocation } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "leftAlias"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata }
              , { name := some "rightAlias"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident helper)
                  [ Solidity.Arg.positional
                      (Solidity.Expr.ident "left")
                  , Solidity.Arg.positional
                      (Solidity.Expr.ident "right") ]))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storagePairBindingFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badStorageToCalldataTuple"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "leftAlias"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata }
              , { name := some "rightAlias"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "storagePair")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.ident "stored")
                  , Solidity.Arg.positional
                      (Solidity.Expr.ident "other") ]))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataOriginSource
    (contractName : Name) (functions : List Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items := functions.map Solidity.ContractItem.function } ] }

def calldataOriginStorageSource
    (contractName : Name) (functions : List Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := uintArrayTy }
              , Solidity.ContractItem.stateVar
                  { name := "other", ty := uintArrayTy } ] ++
                functions.map Solidity.ContractItem.function } ] }

def calldataOriginDisciplineAccepted : Bool :=
  sourceUnitAccepted?
      (calldataOriginSource "CalldataAliasAccepted"
        [ calldataToCalldataLocalFunction
        , calldataToCalldataReturnFunction
        , calldataInternalHelperFunction
        , calldataToCalldataInternalCallFunction
        , calldataAliasReassignmentFunction
            "calldataToCalldataReassignment" "calldataInput"
        , referencePairFunction "calldataPair"
            Solidity.DataLocation.calldata
        , referencePairBindingFunction "calldataPairBinding"
            "calldataPair" Solidity.DataLocation.calldata ])

def calldataOriginDisciplineRejected : Bool :=
  Result.isError
      (SourceUnit.check
        (calldataOriginSource "BadMemoryToCalldataLocal"
          [memoryToCalldataLocalFunction])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginSource "BadMemoryToCalldataReturn"
          [memoryToCalldataReturnFunction])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginSource "BadMemoryToCalldataCall"
          [ calldataInternalHelperFunction
          , memoryToCalldataInternalCallFunction ])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginSource "BadMemoryToCalldataReassignment"
          [ calldataAliasReassignmentFunction
              "memoryToCalldataReassignment" "memoryInput" ])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginSource "BadMemoryToCalldataTuple"
          [ referencePairFunction "memoryPair"
              Solidity.DataLocation.memory
          , referencePairBindingFunction "memoryPairBinding"
              "memoryPair" Solidity.DataLocation.memory ])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginStorageSource "BadStorageToCalldataLocal"
          [storageToCalldataLocalFunction])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginStorageSource "BadStorageToCalldataReturn"
          [storageToCalldataReturnFunction])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginStorageSource "BadStorageToCalldataCall"
          [ calldataInternalHelperFunction
          , storageToCalldataInternalCallFunction ])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginStorageSource "BadStorageToCalldataReassignment"
          [storageToCalldataReassignmentFunction])) &&
    Result.isError
      (SourceUnit.check
        (calldataOriginStorageSource "BadStorageToCalldataTuple"
          [ referencePairFunction "storagePair"
              Solidity.DataLocation.storage
          , storagePairBindingFunction ]))

def calldataOriginDisciplineMatches : Bool :=
  calldataOriginDisciplineAccepted && calldataOriginDisciplineRejected

def referenceDeleteFunction (name : Name)
    (location : Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some location } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.unary
                Solidity.UnaryOp.delete
                (Solidity.Expr.ident "input"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "0")) ]) }

def referenceDeleteSource (contractName : Name)
    (location : Solidity.DataLocation) :
    Solidity.SourceUnit :=
  calldataOriginSource contractName
    [referenceDeleteFunction "deleteInput" location]

def memoryReferenceDeleteAccepted : Bool :=
  sourceUnitAccepted?
    (referenceDeleteSource "MemoryReferenceDelete"
      Solidity.DataLocation.memory)

def calldataReferenceDeleteRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (referenceDeleteSource "CalldataReferenceDelete"
        Solidity.DataLocation.calldata))

def storageReferenceDeleteSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageReferenceDelete"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "values", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "deleteStorageReference"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "aliasValue"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.ident "values"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.unary
                                Solidity.UnaryOp.delete
                                (Solidity.Expr.ident "aliasValue"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "0")) ]) } ] } ] }

def storageReferenceDeleteRejected : Bool :=
  Result.isError (SourceUnit.check storageReferenceDeleteSource)

def referenceDeleteDisciplineMatches : Bool :=
  memoryReferenceDeleteAccepted && calldataReferenceDeleteRejected &&
    storageReferenceDeleteRejected

def pointerReturnParam (name : Option Name)
    (location : Solidity.DataLocation) :
    Solidity.Parameter :=
  { name := name, ty := uintArrayTy, location := some location }

def pointerReturnAssignment (target : Name) : Solidity.Stmt :=
  Solidity.Stmt.expr
    (Solidity.Expr.assign
      (Solidity.Expr.ident "result")
      Solidity.AssignOp.assign
      (Solidity.Expr.ident target))

def pointerReturnBranchFunction : Solidity.FunctionDecl :=
  { name := some "branch"
    params := [{ name := some "pick", ty := Solidity.Ty.bool }]
    returns :=
      [pointerReturnParam (some "result")
        Solidity.DataLocation.storage]
    visibility := some Solidity.Visibility.internal_
    body :=
      some
        (Solidity.Stmt.ifElse
          (Solidity.Expr.ident "pick")
          (pointerReturnAssignment "first")
          (some (pointerReturnAssignment "second"))) }

def pointerReturnGateModifier : Solidity.ModifierDecl :=
  { name := "gate"
    params := [{ name := some "pass", ty := Solidity.Ty.bool }]
    body :=
      some
        (Solidity.Stmt.ifElse
          (Solidity.Expr.ident "pass")
          Solidity.Stmt.modifierPlaceholder
          (some
            (Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "revert") [])))) }

def pointerReturnModifiedFunction : Solidity.FunctionDecl :=
  { name := some "modified"
    returns :=
      [pointerReturnParam (some "result")
        Solidity.DataLocation.storage]
    visibility := some Solidity.Visibility.internal_
    modifiers :=
      [{ target := userPath "gate"
         args := [Solidity.Arg.positional (boolExpr true)] }]
    body := some (pointerReturnAssignment "first") }

def pointerReturnValidSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PointerReturnValid"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "first", ty := uintArrayTy }
              , Solidity.ContractItem.stateVar
                  { name := "second", ty := uintArrayTy }
              , Solidity.ContractItem.modifierDecl
                  pointerReturnGateModifier
              , Solidity.ContractItem.function
                  pointerReturnBranchFunction
              , Solidity.ContractItem.function
                  pointerReturnModifiedFunction ] } ] }

def unassignedStoragePointerReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnassignedStoragePointerReturn"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    returns :=
                      [pointerReturnParam (some "result")
                        Solidity.DataLocation.storage]
                    visibility :=
                      some Solidity.Visibility.internal_
                    body := some (Solidity.Stmt.block []) } ] } ] }

def unassignedCalldataPointerReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnassignedCalldataPointerReturn"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    returns :=
                      [pointerReturnParam (some "result")
                        Solidity.DataLocation.calldata]
                    visibility :=
                      some Solidity.Visibility.internal_
                    mutability := Solidity.StateMutability.pure
                    body := some (Solidity.Stmt.block []) } ] } ] }

def missingBranchPointerReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MissingBranchPointerReturn"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { pointerReturnBranchFunction with
                    name := some "bad"
                    body :=
                      some
                        (Solidity.Stmt.ifElse
                          (Solidity.Expr.ident "pick")
                          (pointerReturnAssignment "stored") none) } ] } ] }

def maybeLoopPointerReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MaybeLoopPointerReturn"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { pointerReturnBranchFunction with
                    name := some "bad"
                    params :=
                      [{ name := some "run", ty := Solidity.Ty.bool }]
                    body :=
                      some
                        (Solidity.Stmt.whileLoop
                          (Solidity.Expr.ident "run")
                          (Solidity.Stmt.block
                            [ pointerReturnAssignment "stored"
                            , Solidity.Stmt.break ])) } ] } ] }

def explicitUnassignedPointerReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExplicitUnassignedPointerReturn"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    returns :=
                      [pointerReturnParam (some "result")
                        Solidity.DataLocation.calldata]
                    visibility :=
                      some Solidity.Visibility.internal_
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "result"))) } ] } ] }

def skippedModifierPointerReturnSource : Solidity.SourceUnit :=
  let maybeModifier : Solidity.ModifierDecl :=
    { name := "maybe"
      params := [{ name := some "run", ty := Solidity.Ty.bool }]
      body :=
        some
          (Solidity.Stmt.ifElse
            (Solidity.Expr.ident "run")
            Solidity.Stmt.modifierPlaceholder none) }
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SkippedModifierPointerReturn"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := uintArrayTy }
              , Solidity.ContractItem.modifierDecl maybeModifier
              , Solidity.ContractItem.function
                  { pointerReturnModifiedFunction with
                    name := some "bad"
                    modifiers :=
                      [{ target := userPath "maybe"
                         args :=
                           [Solidity.Arg.positional
                              (boolExpr false)] }]
                    body := some (pointerReturnAssignment "stored") } ] } ] }

def modifierWithoutPlaceholderSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierWithoutPlaceholder"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { name := "bad", body := some Solidity.Stmt.empty }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    modifiers := [{ target := userPath "bad" }] } ] } ] }

def pointerReturnDefiniteAssignmentMatches : Bool :=
  sourceUnitAccepted? pointerReturnValidSource &&
    Result.isError (SourceUnit.check unassignedStoragePointerReturnSource) &&
    Result.isError (SourceUnit.check unassignedCalldataPointerReturnSource) &&
    Result.isError (SourceUnit.check missingBranchPointerReturnSource) &&
    Result.isError (SourceUnit.check maybeLoopPointerReturnSource) &&
    Result.isError (SourceUnit.check explicitUnassignedPointerReturnSource) &&
    Result.isError (SourceUnit.check skippedModifierPointerReturnSource) &&
    Result.isError (SourceUnit.check modifierWithoutPlaceholderSource)

def signedArrayIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedArrayIndex"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSignedArrayIndex"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some Solidity.DataLocation.calldata }
                      , { name := some "idx"
                          ty := int256
                          location := none } ]
                    visibility :=
                      some Solidity.Visibility.external_
                    mutability :=
                      Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "input")
                              (Solidity.Expr.ident
                                "idx")))) } ] } ] }

def signedArrayIndexRejected : Bool :=
  Result.isError (SourceUnit.check signedArrayIndexSource)

def signedNewArrayLengthSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedArrayLength"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSignedArrayLength"
                    params :=
                      [ { name := some "length"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (Solidity.Expr.newExpr
                                  uintArrayTy
                                  [ Solidity.Arg.positional
                                      (Solidity.Expr.ident
                                        "length") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def signedNewArrayLengthRejected : Bool :=
  Result.isError (SourceUnit.check signedNewArrayLengthSource)

def calldataToStorageAssignFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "copyCalldataToStorage"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "arr")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "input"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataToStorageAssignSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataToStorageAssign"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  calldataToStorageAssignFunction ] } ] }

def calldataToStorageAssignAccepted : Bool :=
  sourceUnitAccepted? calldataToStorageAssignSource

def calldataArrayWriteSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataArrayWrite"
            items :=
              [ Solidity.ContractItem.function
                  { calldataArrayCopyFunction with
                    name := some "writeInput"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident "input")
                                  (numberExpr "0"))
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataArrayWriteRejected : Bool :=
  Result.isError (SourceUnit.check calldataArrayWriteSource)

def calldataStructFieldWriteSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "BadCalldataStructFieldWrite"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "writePair"
                    params :=
                      [ { name := some "p"
                          ty := pairTy
                          location :=
                            some
                              Solidity.DataLocation.calldata } ]
                    visibility :=
                      some Solidity.Visibility.external_
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident "p")
                                  "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataStructFieldWriteRejected : Bool :=
  Result.isError (SourceUnit.check calldataStructFieldWriteSource)

def memberCallExpr (base : Solidity.Expr) (member : Name)
    (args : List Solidity.Arg) : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.member base member) args

def arrayPushExpr (base : Solidity.Expr)
    (args : List Solidity.Arg) : Solidity.Expr :=
  memberCallExpr base "push" args

def arrayPopExpr (base : Solidity.Expr) :
    Solidity.Expr :=
  memberCallExpr base "pop" []

def storageArrayPushPopFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pushPop"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (arrayPushExpr (Solidity.Expr.ident "arr")
                [Solidity.Arg.positional (numberExpr "1")])
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (arrayPushExpr (Solidity.Expr.ident "arr") [])
                Solidity.AssignOp.assign
                (numberExpr "2"))
          , Solidity.Stmt.expr
              (arrayPopExpr (Solidity.Expr.ident "arr"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageArrayPushPopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageArrayPushPop"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  storageArrayPushPopFunction ] } ] }

def storageArrayPushPopAccepted : Bool :=
  sourceUnitAccepted? storageArrayPushPopSource

def viewArrayPushSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewArrayPush"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badViewPush"
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def viewArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check viewArrayPushSource)

def memoryArrayPushSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryArrayPush"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMemoryPush"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPushExpr
                                (Solidity.Expr.ident "input")
                                [Solidity.Arg.positional
                                  (numberExpr "1")])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check memoryArrayPushSource)

def fixedUintArrayTy : Ty :=
  Solidity.Ty.array uint256 (some 2)

def fixedArrayPushSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FixedArrayPush"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := fixedUintArrayTy }
              , Solidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badFixedPush"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPushExpr
                                (Solidity.Expr.ident "arr")
                                [Solidity.Arg.positional
                                  (numberExpr "1")])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def fixedArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check fixedArrayPushSource)

def bytes1SevenExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 1))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [7]))]

def storageBytesPushPopFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pushPopBytes"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (arrayPushExpr (Solidity.Expr.ident "data") [])
          , Solidity.Stmt.expr
              (arrayPushExpr (Solidity.Expr.ident "data")
                [Solidity.Arg.positional bytes1SevenExpr])
          , Solidity.Stmt.expr
              (arrayPopExpr (Solidity.Expr.ident "data"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def storageBytesPushPopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageBytesPushPop"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "data", ty := Solidity.Ty.bytes }
              , Solidity.ContractItem.function
                  storageBytesPushPopFunction ] } ] }

def storageBytesPushPopAccepted : Bool :=
  sourceUnitAccepted? storageBytesPushPopSource

def calldataBytesPopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesPop"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCalldataBytesPop"
                    params :=
                      [ { name := some "data"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.calldata } ]
                    visibility :=
                      some Solidity.Visibility.external_
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPopExpr
                                (Solidity.Expr.ident "data"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataBytesPopRejected : Bool :=
  Result.isError (SourceUnit.check calldataBytesPopSource)

def calldataArrayMutationSource (contractName functionName member : Name)
    (args : List Solidity.Arg) : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some functionName
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    visibility :=
                      some Solidity.Visibility.external_
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (memberCallExpr
                                (Solidity.Expr.ident "input")
                                member args)
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataArrayPushRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (calldataArrayMutationSource "CalldataArrayPush"
        "badCalldataArrayPush" "push"
        [Solidity.Arg.positional (numberExpr "1")]))

def calldataArrayPopRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (calldataArrayMutationSource "CalldataArrayPop"
        "badCalldataArrayPop" "pop" []))

def memoryBytesMutationSource (contractName functionName member : Name)
    (args : List Solidity.Arg) : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some functionName
                    params :=
                      [ { name := some "data"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (memberCallExpr
                                (Solidity.Expr.ident "data")
                                member args)
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryBytesPushRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (memoryBytesMutationSource "MemoryBytesPush"
        "badMemoryBytesPush" "push"
        [Solidity.Arg.positional bytes1SevenExpr]))

def memoryBytesPopRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (memoryBytesMutationSource "MemoryBytesPop"
        "badMemoryBytesPop" "pop" []))

def fixedArrayPopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FixedArrayPop"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := fixedUintArrayTy }
              , Solidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badFixedPop"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPopExpr
                                (Solidity.Expr.ident "arr"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def fixedArrayPopRejected : Bool :=
  Result.isError (SourceUnit.check fixedArrayPopSource)

def stringMutationSource (contractName functionName member : Name) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "text", ty := Solidity.Ty.string }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some functionName
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (memberCallExpr
                                (Solidity.Expr.ident "text")
                                member [])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def stringPushRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (stringMutationSource "StringPush" "badStringPush" "push"))

def stringPopRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (stringMutationSource "StringPop" "badStringPop" "pop"))

def namedArrayPushSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NamedArrayPush"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badNamedPush"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPushExpr
                                (Solidity.Expr.ident "arr")
                                [ Solidity.Arg.named "value"
                                    (numberExpr "1") ])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def namedArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check namedArrayPushSource)

def bytes2SevenExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 2))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [7, 8]))]

def bytesPushWrongTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BytesPushWrongType"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "data", ty := Solidity.Ty.bytes }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badBytesPushWrongType"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (arrayPushExpr
                                (Solidity.Expr.ident "data")
                                [ Solidity.Arg.positional
                                    bytes2SevenExpr ])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def bytesPushWrongTypeRejected : Bool :=
  Result.isError (SourceUnit.check bytesPushWrongTypeSource)

def arrayPopArgumentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ArrayPopArgument"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { storageArrayPushPopFunction with
                    name := some "badPopArgument"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (memberCallExpr
                                (Solidity.Expr.ident "arr")
                                "pop"
                                [ Solidity.Arg.positional
                                    (numberExpr "1") ])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def arrayPopArgumentRejected : Bool :=
  Result.isError (SourceUnit.check arrayPopArgumentSource)

def arrayMutationMemberDisciplineMatches : Bool :=
  storageArrayPushPopAccepted &&
    storageBytesPushPopAccepted &&
    viewArrayPushRejected &&
    memoryArrayPushRejected &&
    calldataArrayPushRejected &&
    calldataArrayPopRejected &&
    fixedArrayPushRejected &&
    fixedArrayPopRejected &&
    memoryBytesPushRejected &&
    memoryBytesPopRejected &&
    calldataBytesPopRejected &&
    stringPushRejected &&
    stringPopRejected &&
    namedArrayPushRejected &&
    bytesPushWrongTypeRejected &&
    arrayPopArgumentRejected

def lengthMemberExpr (base : Solidity.Expr) :
    Solidity.Expr :=
  Solidity.Expr.member base "length"

def lengthAssignmentStmt (base : Solidity.Expr) :
    Solidity.Stmt :=
  Solidity.Stmt.expr
    (Solidity.Expr.assign
      (lengthMemberExpr base)
      Solidity.AssignOp.assign
      (numberExpr "1"))

def lengthUpdateStmt (op : Solidity.UnaryOp)
    (base : Solidity.Expr) : Solidity.Stmt :=
  Solidity.Stmt.expr
    (Solidity.Expr.unary op (lengthMemberExpr base))

def storageLengthMutationSource (contractName functionName fieldName : Name)
    (fieldTy : Ty) (stmt : Solidity.Stmt) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := fieldName, ty := fieldTy }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some functionName
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ stmt
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def storageArrayLengthAssignRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (storageLengthMutationSource "StorageArrayLengthAssign"
        "badStorageArrayLengthAssign" "arr" uintArrayTy
        (lengthAssignmentStmt (Solidity.Expr.ident "arr"))))

def storageBytesLengthAssignRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (storageLengthMutationSource "StorageBytesLengthAssign"
        "badStorageBytesLengthAssign" "data"
        Solidity.Ty.bytes
        (lengthAssignmentStmt (Solidity.Expr.ident "data"))))

def fixedArrayLengthAssignRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (storageLengthMutationSource "FixedArrayLengthAssign"
        "badFixedArrayLengthAssign" "arr" fixedUintArrayTy
        (lengthAssignmentStmt (Solidity.Expr.ident "arr"))))

def storageArrayLengthIncrementRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (storageLengthMutationSource "StorageArrayLengthIncrement"
        "badStorageArrayLengthIncrement" "arr" uintArrayTy
        (lengthUpdateStmt Solidity.UnaryOp.preIncrement
          (Solidity.Expr.ident "arr"))))

def storageBytesLengthDecrementRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (storageLengthMutationSource "StorageBytesLengthDecrement"
        "badStorageBytesLengthDecrement" "data"
        Solidity.Ty.bytes
        (lengthUpdateStmt Solidity.UnaryOp.postDecrement
          (Solidity.Expr.ident "data"))))

def memoryArrayLengthAssignSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryArrayLengthAssign"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMemoryArrayLengthAssign"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ lengthAssignmentStmt
                              (Solidity.Expr.ident "input")
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def memoryArrayLengthAssignRejected : Bool :=
  Result.isError (SourceUnit.check memoryArrayLengthAssignSource)

def lengthMemberLValueDisciplineMatches : Bool :=
  storageArrayLengthAssignRejected &&
    storageBytesLengthAssignRejected &&
    fixedArrayLengthAssignRejected &&
    storageArrayLengthIncrementRejected &&
    storageBytesLengthDecrementRejected &&
    memoryArrayLengthAssignRejected

def signedBytesIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedBytesIndex"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSignedBytesIndex"
                    params :=
                      [ { name := some "data"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.calldata }
                      , { name := some "idx"
                          ty := int256
                          location := none } ]
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    visibility :=
                      some Solidity.Visibility.external_
                    mutability :=
                      Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "data")
                              (Solidity.Expr.ident
                                "idx")))) } ] } ] }

def signedBytesIndexRejected : Bool :=
  Result.isError (SourceUnit.check signedBytesIndexSource)

def signedNewBytesLengthSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedBytesLength"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSignedBytesLength"
                    params :=
                      [ { name := some "length"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "data"
                                  ty := some Solidity.Ty.bytes
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (Solidity.Expr.newExpr
                                  Solidity.Ty.bytes
                                  [ Solidity.Arg.positional
                                      (Solidity.Expr.ident
                                        "length") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def signedNewBytesLengthRejected : Bool :=
  Result.isError (SourceUnit.check signedNewBytesLengthSource)

def newStringFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "makeString"
    params :=
      [ { name := some "length"
          ty := uint256
          location := none } ]
    returns :=
      [ { name := none
          ty := Solidity.Ty.string
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.newExpr
              Solidity.Ty.string
              [Solidity.Arg.positional
                (Solidity.Expr.ident "length")]))) }

def newStringSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NewString"
            items := [Solidity.ContractItem.function
              newStringFunction] } ] }

def newStringAccepted : Bool :=
  sourceUnitAccepted? newStringSource

def namedNewStringLengthSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadNamedNewString"
            items :=
              [ Solidity.ContractItem.function
                  { newStringFunction with
                    name := some "badNamedString"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.newExpr
                              Solidity.Ty.string
                              [ Solidity.Arg.named "length"
                                  (Solidity.Expr.ident
                                    "length") ]))) } ] } ] }

def namedNewStringLengthRejected : Bool :=
  Result.isError (SourceUnit.check namedNewStringLengthSource)

def signedNewStringLengthSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedStringLength"
            items :=
              [ Solidity.ContractItem.function
                  { newStringFunction with
                    name := some "badSignedStringLength"
                    params :=
                      [ { name := some "length"
                          ty := int256
                          location := none } ] } ] } ] }

def signedNewStringLengthRejected : Bool :=
  Result.isError (SourceUnit.check signedNewStringLengthSource)

def sliceExpr (base : Solidity.Expr)
    (start? stop? : Option Solidity.Expr) :
    Solidity.Expr :=
  Solidity.Expr.slice base start? stop?

def calldataBytesSliceFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sliceBytes"
    params :=
      [ { name := some "payload"
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.calldata } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.bytes
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "0")) (some (numberExpr "4"))))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataBytesSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesSlice"
            items :=
              [Solidity.ContractItem.function
                calldataBytesSliceFunction] } ] }

def calldataBytesSliceAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceSource

def calldataStringSliceFunction : Solidity.FunctionDecl :=
  { calldataBytesSliceFunction with
    name := some "sliceString"
    params :=
      [ { name := some "payload"
          ty := Solidity.Ty.string
          location := some Solidity.DataLocation.calldata } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.string
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "0")) (some (numberExpr "4"))))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def calldataStringSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataStringSlice"
            items :=
              [Solidity.ContractItem.function
                calldataStringSliceFunction] } ] }

def calldataStringSliceAccepted : Bool :=
  sourceUnitAccepted? calldataStringSliceSource

def calldataBytesSliceIndexFunction : Solidity.FunctionDecl :=
  { calldataBytesSliceFunction with
    name := some "sliceByte"
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytesN 1
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (sliceExpr (Solidity.Expr.ident "payload")
                (some (numberExpr "1")) (some (numberExpr "3")))
              (numberExpr "0")))) }

def calldataBytesSliceIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesSliceIndex"
            items :=
              [Solidity.ContractItem.function
                calldataBytesSliceIndexFunction] } ] }

def calldataBytesSliceIndexAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceIndexSource

def calldataBytesSliceLocalFunction : Solidity.FunctionDecl :=
  { calldataBytesSliceFunction with
    name := some "sliceBytesLocal"
    returns :=
      [ { name := none
          ty := Solidity.Ty.uint 256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.bytes
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "length")) ]) }

def calldataBytesSliceLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesSliceLocal"
            items :=
              [Solidity.ContractItem.function
                calldataBytesSliceLocalFunction] } ] }

def calldataBytesSliceLocalAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceLocalSource

def calldataBytesSliceMemoryLocalFunction : Solidity.FunctionDecl :=
  { calldataBytesSliceLocalFunction with
    name := some "sliceBytesMemoryLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.bytes
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.member
                  (Solidity.Expr.ident "local") "length")) ]) }

def calldataBytesSliceMemoryLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesSliceMemoryLocal"
            items :=
              [Solidity.ContractItem.function
                calldataBytesSliceMemoryLocalFunction] } ] }

def calldataBytesSliceMemoryLocalAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceMemoryLocalSource

def bytes1MaxExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 1))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [255]))]

def calldataBytesSliceMemoryLocalMutationFunction :
    Solidity.FunctionDecl :=
  { calldataBytesSliceFunction with
    name := some "sliceBytesMemoryLocalMutation"
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytesN 1
          location := none }
      , { name := none
          ty := Solidity.Ty.bytesN 1
          location := none } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.bytes
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))
                Solidity.AssignOp.assign
                bytes1MaxExpr)
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.index
                        (Solidity.Expr.ident "local")
                        (numberExpr "0"))
                  , Solidity.TupleItem.value
                      (Solidity.Expr.index
                        (Solidity.Expr.ident "payload")
                        (numberExpr "1")) ])) ]) }

def calldataBytesSliceMemoryLocalMutationSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataBytesSliceMemoryLocalMutation"
            items :=
              [Solidity.ContractItem.function
                calldataBytesSliceMemoryLocalMutationFunction] } ] }

def calldataBytesSliceMemoryLocalMutationAccepted : Bool :=
  sourceUnitAccepted? calldataBytesSliceMemoryLocalMutationSource

def calldataStringSliceLocalFunction : Solidity.FunctionDecl :=
  { calldataStringSliceFunction with
    name := some "sliceStringLocal"
    returns :=
      [ { name := none
          ty := Solidity.Ty.string
          location :=
            some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.string
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "local")) ]) }

def calldataStringSliceLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataStringSliceLocal"
            items :=
              [Solidity.ContractItem.function
                calldataStringSliceLocalFunction] } ] }

def calldataStringSliceLocalAccepted : Bool :=
  sourceUnitAccepted? calldataStringSliceLocalSource

def calldataStringSliceMemoryLocalFunction : Solidity.FunctionDecl :=
  { calldataStringSliceLocalFunction with
    name := some "sliceStringMemoryLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some Solidity.Ty.string
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "payload")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "local")) ]) }

def calldataStringSliceMemoryLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataStringSliceMemoryLocal"
            items :=
              [Solidity.ContractItem.function
                calldataStringSliceMemoryLocalFunction] } ] }

def calldataStringSliceMemoryLocalAccepted : Bool :=
  sourceUnitAccepted? calldataStringSliceMemoryLocalSource

def memoryBytesSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryBytesSlice"
            items :=
              [ Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badMemorySlice"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.memory } ] } ] } ] }

def memoryBytesSliceRejected : Bool :=
  Result.isError (SourceUnit.check memoryBytesSliceSource)

def memoryStringSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryStringSlice"
            items :=
              [ Solidity.ContractItem.function
                  { calldataStringSliceFunction with
                    name := some "badMemoryStringSlice"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.memory } ] } ] } ] }

def memoryStringSliceRejected : Bool :=
  Result.isError (SourceUnit.check memoryStringSliceSource)

def stringIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStringIndex"
            items :=
              [ Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badStringIndex"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.calldata } ]
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "payload")
                              (numberExpr "0")))) } ] } ] }

def stringIndexRejected : Bool :=
  Result.isError (SourceUnit.check stringIndexSource)

def stringLengthMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStringLength"
            items :=
              [ Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badStringLength"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "payload")
                              "length"))) } ] } ] }

def stringLengthMemberRejected : Bool :=
  Result.isError (SourceUnit.check stringLengthMemberSource)

def calldataArraySliceFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sliceArray"
    params :=
      [ { name := some "input"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "input")
                  (some (numberExpr "0")) (some (numberExpr "2"))))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))) ]) }

def calldataArraySliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArraySlice"
            items :=
              [Solidity.ContractItem.function
                calldataArraySliceFunction] } ] }

def calldataArraySliceAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceSource

def calldataArraySliceMemoryLocalFunction : Solidity.FunctionDecl :=
  { calldataArraySliceFunction with
    name := some "sliceArrayMemoryLocal" }

def calldataArraySliceMemoryLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArraySliceMemoryLocal"
            items :=
              [Solidity.ContractItem.function
                calldataArraySliceMemoryLocalFunction] } ] }

def calldataArraySliceMemoryLocalAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceMemoryLocalSource

def calldataArraySliceMemoryLocalMutationFunction :
    Solidity.FunctionDecl :=
  { calldataArraySliceFunction with
    name := some "sliceArrayMemoryLocalMutation"
    returns :=
      [ { name := none
          ty := Solidity.Ty.uint 256
          location := none }
      , { name := none
          ty := Solidity.Ty.uint 256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.memory } ]
              (some
                (sliceExpr (Solidity.Expr.ident "input")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))
                Solidity.AssignOp.assign
                (numberExpr "99"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.index
                        (Solidity.Expr.ident "local")
                        (numberExpr "0"))
                  , Solidity.TupleItem.value
                      (Solidity.Expr.index
                        (Solidity.Expr.ident "input")
                        (numberExpr "1")) ])) ]) }

def calldataArraySliceMemoryLocalMutationSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArraySliceMemoryLocalMutation"
            items :=
              [Solidity.ContractItem.function
                calldataArraySliceMemoryLocalMutationFunction] } ] }

def calldataArraySliceMemoryLocalMutationAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceMemoryLocalMutationSource

def calldataArraySliceIndexFunction : Solidity.FunctionDecl :=
  { calldataArraySliceFunction with
    name := some "sliceArrayFirst"
    returns :=
      [ { name := none
          ty := Solidity.Ty.uint 256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (sliceExpr (Solidity.Expr.ident "input")
                (some (numberExpr "1")) (some (numberExpr "3")))
              (numberExpr "0")))) }

def calldataArraySliceIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArraySliceIndex"
            items :=
              [Solidity.ContractItem.function
                calldataArraySliceIndexFunction] } ] }

def calldataArraySliceIndexAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceIndexSource

def calldataArraySliceLocalFunction : Solidity.FunctionDecl :=
  { calldataArraySliceFunction with
    name := some "sliceArrayLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "local"
                  ty := some uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
              (some
                (sliceExpr (Solidity.Expr.ident "input")
                  (some (numberExpr "1")) (some (numberExpr "3"))))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.index
                  (Solidity.Expr.ident "local")
                  (numberExpr "0"))) ]) }

def calldataArraySliceLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataArraySliceLocal"
            items :=
              [Solidity.ContractItem.function
                calldataArraySliceLocalFunction] } ] }

def calldataArraySliceLocalAccepted : Bool :=
  sourceUnitAccepted? calldataArraySliceLocalSource

def memoryArraySliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryArraySlice"
            items :=
              [ Solidity.ContractItem.function
                  { calldataArraySliceFunction with
                    name := some "badMemoryArraySlice"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.memory } ] } ] } ] }

def memoryArraySliceRejected : Bool :=
  Result.isError (SourceUnit.check memoryArraySliceSource)

def storageBytesSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageBytesSlice"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := Solidity.Ty.bytes }
              , Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badStorageBytesSlice"
                    params := []
                    mutability := Solidity.StateMutability.view
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (sliceExpr
                              (Solidity.Expr.ident "stored")
                              (some (numberExpr "0"))
                              (some (numberExpr "2"))))) } ] } ] }

def storageBytesSliceRejected : Bool :=
  Result.isError (SourceUnit.check storageBytesSliceSource)

def storageStringSliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageStringSlice"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := Solidity.Ty.string }
              , Solidity.ContractItem.function
                  { calldataStringSliceFunction with
                    name := some "badStorageStringSlice"
                    params := []
                    mutability := Solidity.StateMutability.view
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (sliceExpr
                              (Solidity.Expr.ident "stored")
                              (some (numberExpr "0"))
                              (some (numberExpr "2"))))) } ] } ] }

def storageStringSliceRejected : Bool :=
  Result.isError (SourceUnit.check storageStringSliceSource)

def storageArraySliceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StorageArraySlice"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "stored", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { calldataArraySliceFunction with
                    name := some "badStorageArraySlice"
                    params := []
                    mutability := Solidity.StateMutability.view
                    returns :=
                      [ { name := none
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (sliceExpr
                              (Solidity.Expr.ident "stored")
                              (some (numberExpr "0"))
                              (some (numberExpr "2"))))) } ] } ] }

def storageArraySliceRejected : Bool :=
  Result.isError (SourceUnit.check storageArraySliceSource)

def calldataSliceSignedIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataSliceSignedIndex"
            items :=
              [ Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badSignedIndex"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.calldata }
                      , { name := some "offset"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some Solidity.Ty.bytes
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (sliceExpr
                                  (Solidity.Expr.ident "payload")
                                  (some
                                    (Solidity.Expr.ident "offset"))
                                  (some (numberExpr "4"))))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataSliceSignedIndexRejected : Bool :=
  Result.isError (SourceUnit.check calldataSliceSignedIndexSource)

def calldataStringSliceSignedIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataStringSliceSignedIndex"
            items :=
              [ Solidity.ContractItem.function
                  { calldataStringSliceFunction with
                    name := some "badSignedStringIndex"
                    params :=
                      [ { name := some "payload"
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.calldata }
                      , { name := some "offset"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some Solidity.Ty.string
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (sliceExpr
                                  (Solidity.Expr.ident "payload")
                                  (some
                                    (Solidity.Expr.ident "offset"))
                                  (some (numberExpr "4"))))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def calldataStringSliceSignedIndexRejected : Bool :=
  Result.isError (SourceUnit.check calldataStringSliceSignedIndexSource)

def calldataArraySliceSignedIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataArraySliceSignedIndex"
            items :=
              [ Solidity.ContractItem.function
                  { calldataArraySliceFunction with
                    name := some "badSignedArrayIndex"
                    params :=
                      [ { name := some "input"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.calldata }
                      , { name := some "offset"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some uintArrayTy
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              (some
                                (sliceExpr
                                  (Solidity.Expr.ident "input")
                                  (some
                                    (Solidity.Expr.ident "offset"))
                                  (some (numberExpr "2"))))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident "local")
                                  (numberExpr "0"))) ]) } ] } ] }

def calldataArraySliceSignedIndexRejected : Bool :=
  Result.isError (SourceUnit.check calldataArraySliceSignedIndexSource)

def calldataSliceMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataSliceMember"
            items :=
              [ Solidity.ContractItem.function
                  { calldataBytesSliceFunction with
                    name := some "badSliceMember"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (sliceExpr
                                (Solidity.Expr.ident "payload")
                                none (some (numberExpr "4")))
                              "length"))) } ] } ] }

def calldataSliceMemberRejected : Bool :=
  Result.isError (SourceUnit.check calldataSliceMemberSource)

def calldataStringSliceMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataStringSliceMember"
            items :=
              [ Solidity.ContractItem.function
                  { calldataStringSliceFunction with
                    name := some "badStringSliceMember"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (sliceExpr
                                (Solidity.Expr.ident "payload")
                                none (some (numberExpr "4")))
                              "length"))) } ] } ] }

def calldataStringSliceMemberRejected : Bool :=
  Result.isError (SourceUnit.check calldataStringSliceMemberSource)

def calldataStringSliceIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataStringSliceIndex"
            items :=
              [ Solidity.ContractItem.function
                  { calldataStringSliceFunction with
                    name := some "badStringSliceIndex"
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (sliceExpr
                                (Solidity.Expr.ident "payload")
                                (some (numberExpr "1"))
                                (some (numberExpr "3")))
                              (numberExpr "0")))) } ] } ] }

def calldataStringSliceIndexRejected : Bool :=
  Result.isError (SourceUnit.check calldataStringSliceIndexSource)

def calldataArraySliceMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCalldataArraySliceMember"
            items :=
              [ Solidity.ContractItem.function
                  { calldataArraySliceFunction with
                    name := some "badArraySliceMember"
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.uint 256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (sliceExpr
                                (Solidity.Expr.ident "input")
                                none (some (numberExpr "2")))
                              "length"))) } ] } ] }

def calldataArraySliceMemberRejected : Bool :=
  Result.isError (SourceUnit.check calldataArraySliceMemberSource)

def calldataArraySliceUsingLibrary : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "SliceMemberLib"
    items :=
      [ Solidity.ContractItem.function
          { simpleReturnFunction with
            name := some "first"
            params :=
              [ { name := some "input"
                  ty := uintArrayTy
                  location :=
                    some Solidity.DataLocation.calldata } ]
            returns :=
              [ { name := none
                  ty := Solidity.Ty.uint 256
                  location := none } ]
            visibility := some Solidity.Visibility.internal_
            mutability := Solidity.StateMutability.pure
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.index
                      (Solidity.Expr.ident "input")
                      (numberExpr "0")))) } ] }

def calldataArraySliceUsingMemberCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          calldataArraySliceUsingLibrary
      , Solidity.SourceItem.contract
          { name := "BadCalldataArraySliceUsingMemberCall"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "SliceMemberLib"
                    target := some uintArrayTy }
              , Solidity.ContractItem.function
                  { calldataArraySliceFunction with
                    name := some "badArraySliceUsingMemberCall"
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.uint 256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (sliceExpr
                                  (Solidity.Expr.ident "input")
                                  (some (numberExpr "1"))
                                  (some (numberExpr "3")))
                                "first")
                              []))) } ] } ] }

def calldataArraySliceUsingMemberCallRejected : Bool :=
  Result.isError (SourceUnit.check
    calldataArraySliceUsingMemberCallSource)

def structParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usePoint"
    params :=
      [ { name := some "point"
          ty := pointTy
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.literal
              (Solidity.Literal.number "1")))) }

def structSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "StructUser"
            items := [Solidity.ContractItem.function
              structParamFunction] } ] }

def structSourceAccepted : Bool :=
  sourceUnitAccepted? structSource

def pragmaAbiCoderV1SimpleSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.contract
          { name := "AbiCoderV1Simple"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaAbiCoderV1SimpleAccepted : Bool :=
  sourceUnitAccepted? pragmaAbiCoderV1SimpleSource

def dynamicArrayParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "useArray"
    params :=
      [ { name := some "values"
          ty := Solidity.Ty.array uint256 none
          location := some Solidity.DataLocation.memory } ] }

def pragmaAbiCoderV1DynamicArrayParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.contract
          { name := "AbiCoderV1DynamicArray"
            items :=
              [Solidity.ContractItem.function
                dynamicArrayParamFunction] } ] }

def pragmaAbiCoderV1DynamicArrayParamAccepted : Bool :=
  sourceUnitAccepted? pragmaAbiCoderV1DynamicArrayParamSource

def pragmaAbiCoderV2StructParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v2"
      , Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "AbiCoderV2StructParam"
            items :=
              [Solidity.ContractItem.function
                structParamFunction] } ] }

def pragmaAbiCoderV2StructParamAccepted : Bool :=
  sourceUnitAccepted? pragmaAbiCoderV2StructParamSource

def pragmaAbiCoderV1StructParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "AbiCoderV1StructParam"
            items :=
              [Solidity.ContractItem.function
                structParamFunction] } ] }

def pragmaAbiCoderV1StructParamRejected : Bool :=
  Result.isError (SourceUnit.check pragmaAbiCoderV1StructParamSource)

def nestedDynamicArrayParamFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "useNestedArray"
    params :=
      [ { name := some "values"
          ty :=
            Solidity.Ty.array
              (Solidity.Ty.array uint256 none) none
          location := some Solidity.DataLocation.memory } ] }

def pragmaAbiCoderV1NestedDynamicArrayParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.contract
          { name := "AbiCoderV1NestedDynamicArray"
            items :=
              [Solidity.ContractItem.function
                nestedDynamicArrayParamFunction] } ] }

def pragmaAbiCoderV1NestedDynamicArrayParamRejected : Bool :=
  Result.isError
    (SourceUnit.check pragmaAbiCoderV1NestedDynamicArrayParamSource)

def abiEncodePointFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "encodePoint"
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "abi") "encode")
              [ Solidity.Arg.positional
                  (Solidity.Expr.call
                    (Solidity.Expr.typeName pointTy)
                    [Solidity.Arg.positional
                      (numberExpr "1")]) ]))) }

def pragmaAbiCoderV1AbiEncodeStructSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "AbiCoderV1EncodeStruct"
            items :=
              [Solidity.ContractItem.function
                abiEncodePointFunction] } ] }

def pragmaAbiCoderV1AbiEncodeStructRejected : Bool :=
  Result.isError (SourceUnit.check pragmaAbiCoderV1AbiEncodeStructSource)

def pragmaAbiCoderDuplicateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v1"
      , Solidity.SourceItem.pragma "abicoder" "v2"
      , Solidity.SourceItem.contract
          { name := "AbiCoderDuplicate"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaAbiCoderDuplicateRejected : Bool :=
  Result.isError (SourceUnit.check pragmaAbiCoderDuplicateSource)

def pragmaAbiCoderBadValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v3"
      , Solidity.SourceItem.contract
          { name := "AbiCoderBadValue"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaAbiCoderBadValueRejected : Bool :=
  Result.isError (SourceUnit.check pragmaAbiCoderBadValueSource)

def pragmaAbiCoderV2ThenExperimentalSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma "abicoder" "v2"
      , Solidity.SourceItem.pragma
          "experimental" "ABIEncoderV2"
      , Solidity.SourceItem.contract
          { name := "AbiCoderV2ThenExperimental"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaAbiCoderV2ThenExperimentalAccepted : Bool :=
  sourceUnitAccepted? pragmaAbiCoderV2ThenExperimentalSource

def pragmaAbiCoderExperimentalThenV2Source :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.pragma
          "experimental" "ABIEncoderV2"
      , Solidity.SourceItem.pragma "abicoder" "v2"
      , Solidity.SourceItem.contract
          { name := "AbiCoderExperimentalThenV2"
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def pragmaAbiCoderExperimentalThenV2Rejected : Bool :=
  Result.isError (SourceUnit.check pragmaAbiCoderExperimentalThenV2Source)

def pragmaAbiCoderV1DisciplineAccepted : Bool :=
  pragmaAbiCoderV1SimpleAccepted &&
    pragmaAbiCoderV1DynamicArrayParamAccepted &&
    pragmaAbiCoderV2StructParamAccepted &&
    pragmaAbiCoderV2ThenExperimentalAccepted

def pragmaAbiCoderV1DisciplineRejected : Bool :=
  pragmaAbiCoderV1StructParamRejected &&
    pragmaAbiCoderV1NestedDynamicArrayParamRejected &&
    pragmaAbiCoderV1AbiEncodeStructRejected &&
    pragmaAbiCoderDuplicateRejected &&
    pragmaAbiCoderBadValueRejected &&
    pragmaAbiCoderExperimentalThenV2Rejected

def missingStructLocationFunction : Solidity.FunctionDecl :=
  { structParamFunction with
    params := [{ name := some "point", ty := pointTy, location := none }] }

def missingStructLocationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "BadStructLocation"
            items := [Solidity.ContractItem.function
              missingStructLocationFunction] } ] }

def missingStructLocationRejected : Bool :=
  Result.isError (SourceUnit.check missingStructLocationSource)

def missingStructReturnLocationFunction : Solidity.FunctionDecl :=
  { structParamFunction with
    name := some "badReturnLocation"
    params := []
    returns := [{ name := none, ty := pointTy, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName pointTy)
              [Solidity.Arg.positional (numberExpr "1")]))) }

def missingStructReturnLocationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := "BadStructReturnLocation"
            items := [Solidity.ContractItem.function
              missingStructReturnLocationFunction] } ] }

def missingStructReturnLocationRejected : Bool :=
  Result.isError (SourceUnit.check missingStructReturnLocationSource)

def tupleReturnFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "tupleReturn"
    params := []
    returns :=
      [ { name := none
          ty := Solidity.Ty.uint 8
          location := none }
      , { name := none
          ty := Solidity.Ty.bool
          location := none } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value (numberExpr "1")
              , Solidity.TupleItem.value (boolExpr true) ]))) }

def tupleReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleReturn"
            items :=
              [Solidity.ContractItem.function
                tupleReturnFunction] } ] }

def tupleReturnAccepted : Bool :=
  sourceUnitAccepted? tupleReturnSource

def tupleVarDeclFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleDecl"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "a"
                  ty := some uint256
                  location := none }
              , { name := some "b"
                  ty := some Solidity.Ty.bool
                  location := none } ]
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value (numberExpr "1")
                  , Solidity.TupleItem.value
                      (boolExpr true) ]))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def tupleVarDeclSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleDecl"
            items :=
              [Solidity.ContractItem.function
                tupleVarDeclFunction] } ] }

def tupleVarDeclAccepted : Bool :=
  sourceUnitAccepted? tupleVarDeclSource

def tupleVarDeclOmittedLiteralFunction :
    Solidity.FunctionDecl :=
  { tupleVarDeclFunction with
    name := some "tupleDeclOmittedLiteral"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := none
                  ty := none
                  location := none }
              , { name := some "b"
                  ty := some uint256
                  location := none } ]
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value (numberExpr "1")
                  , Solidity.TupleItem.value (numberExpr "2") ]))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "b")) ]) }

def tupleVarDeclOmittedLiteralSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleDeclOmittedLiteral"
            items :=
              [Solidity.ContractItem.function
                tupleVarDeclOmittedLiteralFunction] } ] }

def tupleVarDeclOmittedLiteralAccepted : Bool :=
  sourceUnitAccepted? tupleVarDeclOmittedLiteralSource

def tupleVarDeclOmittedReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleDeclOmittedReturn"
            items :=
              [ Solidity.ContractItem.function
                  { tupleReturnFunction with
                    name := some "pair"
                    returns :=
                      [ { name := none, ty := uint256, location := none }
                      , { name := none, ty := uint256, location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (numberExpr "1")
                              , Solidity.TupleItem.value
                                  (numberExpr "2") ]))) }
              , Solidity.ContractItem.function
                  { tupleVarDeclFunction with
                    name := some "run"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := none
                                  ty := none
                                  location := none }
                              , { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              (some
                                (Solidity.Expr.call
                                  (Solidity.Expr.ident "pair")
                                  []))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "b")) ]) } ] } ] }

def tupleVarDeclOmittedReturnAccepted : Bool :=
  sourceUnitAccepted? tupleVarDeclOmittedReturnSource

def tupleHoleReturnValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleHoleReturnValue"
            items :=
              [ Solidity.ContractItem.function
                  { tupleReturnFunction with
                    name := some "badReturnHole"
                    returns :=
                      [ { name := none, ty := uint256, location := none }
                      , { name := none, ty := uint256, location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.hole
                              , Solidity.TupleItem.value
                                  (numberExpr "1") ]))) } ] } ] }

def tupleHoleReturnValueRejected : Bool :=
  Result.isError (SourceUnit.check tupleHoleReturnValueSource)

def tupleVarDeclOmittedNoInitSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleDeclOmittedNoInit"
            items :=
              [ Solidity.ContractItem.function
                  { tupleVarDeclFunction with
                    name := some "badOmittedNoInit"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := none
                                  ty := none
                                  location := none }
                              , { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tupleVarDeclOmittedNoInitRejected : Bool :=
  Result.isError (SourceUnit.check tupleVarDeclOmittedNoInitSource)

def tupleHoleVarDeclInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleHoleVarDeclInit"
            items :=
              [ Solidity.ContractItem.function
                  { tupleVarDeclFunction with
                    name := some "badVarDeclInitHole"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none }
                              , { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              (some
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.hole
                                  , Solidity.TupleItem.value
                                      (numberExpr "1") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tupleHoleVarDeclInitRejected : Bool :=
  Result.isError (SourceUnit.check tupleHoleVarDeclInitSource)

def badTupleVarDeclFunction : Solidity.FunctionDecl :=
  { tupleVarDeclFunction with
    name := some "badTupleDecl"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "a"
                  ty := some uint256
                  location := none }
              , { name := some "b"
                  ty := some Solidity.Ty.bool
                  location := none } ]
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value (numberExpr "1")
                  , Solidity.TupleItem.value (numberExpr "2") ]))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def badTupleVarDeclSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTupleDecl"
            items :=
              [Solidity.ContractItem.function
                badTupleVarDeclFunction] } ] }

def badTupleVarDeclRejected : Bool :=
  Result.isError (SourceUnit.check badTupleVarDeclSource)

def duplicateBlockLocalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "duplicateBlockLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "value", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , Solidity.Stmt.varDecl
              [{ name := some "value", ty := some uint256, location := none }]
              (some (numberExpr "2"))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "value")) ]) }

def duplicateBlockLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateBlockLocal"
            items :=
              [Solidity.ContractItem.function
                duplicateBlockLocalFunction] } ] }

def duplicateBlockLocalRejected : Bool :=
  Result.isError (SourceUnit.check duplicateBlockLocalSource)

def nestedBlockLocalShadowFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "nestedBlockLocalShadow"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "value", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , Solidity.Stmt.block
              [ Solidity.Stmt.varDecl
                  [ { name := some "value"
                      ty := some uint256
                      location := none } ]
                  (some (numberExpr "2")) ]
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "value")) ]) }

def nestedBlockLocalShadowSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedBlockLocalShadow"
            items :=
              [Solidity.ContractItem.function
                nestedBlockLocalShadowFunction] } ] }

def nestedBlockLocalShadowAccepted : Bool :=
  sourceUnitAccepted? nestedBlockLocalShadowSource

def localBindingScopeDisciplineMatches : Bool :=
  duplicateBlockLocalRejected && nestedBlockLocalShadowAccepted

def tupleAssignmentFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleAssign"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "a", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , Solidity.Stmt.varDecl
              [{ name := some "b", ty := some uint256, location := none }]
              (some (numberExpr "2"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.ident "a")
                  , Solidity.TupleItem.value
                      (Solidity.Expr.ident "b") ])
                Solidity.AssignOp.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.ident "b")
                  , Solidity.TupleItem.value
                      (Solidity.Expr.ident "a") ]))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "a")) ]) }

def tupleAssignmentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleAssign"
            items :=
              [Solidity.ContractItem.function
                tupleAssignmentFunction] } ] }

def tupleAssignmentAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentSource

def tupleAssignmentHoleFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tupleAssignHole"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "a", ty := some uint256, location := none }]
              (some (numberExpr "0"))
          , Solidity.Stmt.varDecl
              [{ name := some "b", ty := some uint256, location := none }]
              (some (numberExpr "0"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.ident "a")
                  , Solidity.TupleItem.hole
                  , Solidity.TupleItem.value
                      (Solidity.Expr.ident "b") ])
                Solidity.AssignOp.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value (numberExpr "4")
                  , Solidity.TupleItem.value (numberExpr "99")
                  , Solidity.TupleItem.value (numberExpr "2") ]))
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "a")) ]) }

def tupleAssignmentHoleSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleAssignHole"
            items :=
              [Solidity.ContractItem.function
                tupleAssignmentHoleFunction] } ] }

def tupleAssignmentHoleAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentHoleSource

def tupleAssignmentFromReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleAssignReturn"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "pair"
                    returns :=
                      [ { name := none, ty := uint256, location := none }
                      , { name := none, ty := uint256, location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (numberExpr "4")
                              , Solidity.TupleItem.value
                                  (numberExpr "2") ]))) }
              , Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "run"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (Solidity.Expr.ident "a")
                                  , Solidity.TupleItem.value
                                      (Solidity.Expr.ident "b") ])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.call
                                  (Solidity.Expr.ident "pair")
                                  []))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "a")) ]) } ] } ] }

def tupleAssignmentFromReturnAccepted : Bool :=
  sourceUnitAccepted? tupleAssignmentFromReturnSource

def tupleIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleIndex"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badLiteralTupleIndex"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.tuple
                                [ Solidity.TupleItem.value
                                    (numberExpr "1")
                                , Solidity.TupleItem.value
                                    (numberExpr "2") ])
                              (numberExpr "0")))) } ] } ] }

def tupleIndexRejected : Bool :=
  Result.isError (SourceUnit.check tupleIndexSource)

def tupleHoleAssignmentRhsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TupleHoleAssignRhs"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badAssignRhsHole"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              (some (numberExpr "0"))
                          , Solidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              (some (numberExpr "0"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (Solidity.Expr.ident "a")
                                  , Solidity.TupleItem.value
                                      (Solidity.Expr.ident "b") ])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.hole
                                  , Solidity.TupleItem.value
                                      (numberExpr "1") ]))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "b")) ]) } ] } ] }

def tupleHoleAssignmentRhsRejected : Bool :=
  Result.isError (SourceUnit.check tupleHoleAssignmentRhsSource)

def tupleHoleValuePositionDisciplineMatches : Bool :=
  tupleHoleReturnValueRejected &&
    tupleHoleVarDeclInitRejected &&
    tupleHoleAssignmentRhsRejected

def badTupleAssignmentAritySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTupleAssignArity"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badArity"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (Solidity.Expr.ident "a")
                                  , Solidity.TupleItem.value
                                      (Solidity.Expr.ident "b") ])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (numberExpr "1") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentArityRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentAritySource)

def badTupleAssignmentTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTupleAssignType"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badType"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.varDecl
                              [ { name := some "b"
                                  ty := some Solidity.Ty.bool
                                  location := none } ]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (Solidity.Expr.ident "a")
                                  , Solidity.TupleItem.value
                                      (Solidity.Expr.ident "b") ])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (numberExpr "1")
                                  , Solidity.TupleItem.value
                                      (numberExpr "2") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentTypeRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentTypeSource)

def badTupleAssignmentTargetSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTupleAssignTarget"
            items :=
              [ Solidity.ContractItem.function
                  { tupleAssignmentFunction with
                    name := some "badTarget"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "a"
                                  ty := some uint256
                                  location := none } ]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (Solidity.Expr.ident "a")
                                  , Solidity.TupleItem.value
                                      (numberExpr "1") ])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.tuple
                                  [ Solidity.TupleItem.value
                                      (numberExpr "1")
                                  , Solidity.TupleItem.value
                                      (numberExpr "2") ]))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def badTupleAssignmentTargetRejected : Bool :=
  Result.isError (SourceUnit.check badTupleAssignmentTargetSource)

def tupleDestructuringStaticRejectionDisciplineMatches : Bool :=
  tupleVarDeclOmittedNoInitRejected &&
    badTupleVarDeclRejected &&
    badTupleAssignmentArityRejected &&
    badTupleAssignmentTypeRejected &&
    badTupleAssignmentTargetRejected &&
    tupleIndexRejected

def valueTypeMemoryParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadValueLocation"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badValueLocation"
                    params :=
                      [ { name := some "x"
                          ty := uint256
                          location :=
                            some
                              Solidity.DataLocation.memory } ] } ] } ] }

def valueTypeMemoryParamRejected : Bool :=
  Result.isError (SourceUnit.check valueTypeMemoryParamSource)

def constantWithInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "ANSWER"
            ty := uint256
            mutability := Solidity.VarMutability.constant
            init :=
              some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "42")) } ] }

def constantWithInitAccepted : Bool :=
  sourceUnitAccepted? constantWithInitSource

def constantWithoutInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "MISSING"
            ty := uint256
            mutability := Solidity.VarMutability.constant } ] }

def constantWithoutInitRejected : Bool :=
  Result.isError (SourceUnit.check constantWithoutInitSource)

def bytesConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "BLOB"
            ty := Solidity.Ty.bytes
            mutability := Solidity.VarMutability.constant
            init :=
              some
                (Solidity.Expr.literal
                  (Solidity.Literal.bytes [1, 2])) } ] }

def bytesConstantAccepted : Bool :=
  sourceUnitAccepted? bytesConstantSource

def stringLiteralBytesConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "STRING_BLOB"
            ty := Solidity.Ty.bytes
            mutability := Solidity.VarMutability.constant
            init :=
              some
                (Solidity.Expr.literal
                  (Solidity.Literal.string "hi")) } ] }

def stringLiteralBytesConstantAccepted : Bool :=
  sourceUnitAccepted? stringLiteralBytesConstantSource

def badArrayConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadArrayConstant"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "values"
                    ty := Solidity.Ty.array uint256 (some 1)
                    mutability :=
                      Solidity.VarMutability.constant
                    init :=
                      some
                        (Solidity.Expr.array
                          [numberExpr "1"]) } ] } ] }

def badArrayConstantRejected : Bool :=
  Result.isError (SourceUnit.check badArrayConstantSource)

def badFreeMutableSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "NOT_CONSTANT"
            ty := uint256
            init := some (numberExpr "1") } ] }

def badFreeMutableRejected : Bool :=
  Result.isError (SourceUnit.check badFreeMutableSource)

def addmodConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "MODDED"
            ty := uint256
            mutability := Solidity.VarMutability.constant
            init :=
              some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "addmod")
                  [ Solidity.Arg.positional (numberExpr "1")
                  , Solidity.Arg.positional (numberExpr "2")
                  , Solidity.Arg.positional (numberExpr "3") ]) } ] }

def addmodConstantAccepted : Bool :=
  sourceUnitAccepted? addmodConstantSource

def addmodVariableModulusSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddmodVariableModulus"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "modded"
                    params :=
                      [{ name := some "m"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "addmod")
                              [ Solidity.Arg.positional
                                  (numberExpr "1")
                              , Solidity.Arg.positional
                                  (numberExpr "2")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.ident "m") ]))) } ] } ] }

def addmodVariableModulusAccepted : Bool :=
  sourceUnitAccepted? addmodVariableModulusSource

def addmodSignedArgumentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAddmodSignedArgument"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badAddmodSigned"
                    params :=
                      [ { name := some "a"
                          ty := int256
                          location := none }
                      , { name := some "m"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "addmod")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident "a")
                              , Solidity.Arg.positional
                                  (numberExpr "2")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.ident "m") ]))) } ] } ] }

def addmodSignedArgumentRejected : Bool :=
  Result.isError (SourceUnit.check addmodSignedArgumentSource)

def addmodZeroLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddmodZeroLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "addmodLiteralZero"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "addmod")
                              [ Solidity.Arg.positional
                                  (numberExpr "1")
                              , Solidity.Arg.positional
                                  (numberExpr "2")
                              , Solidity.Arg.positional
                                  (numberExpr "0") ]))) } ] } ] }

-- MULMOD0: a compile-time-CONSTANT zero modulus in addmod/mulmod is Error 4195
-- "Arithmetic modulo zero" in solc's constant evaluator — a COMPILE reject, not
-- the runtime Panic 0x12 this witness formerly pinned as accepted.
def addmodZeroLiteralRejected : Bool :=
  Result.isError (SourceUnit.check addmodZeroLiteralSource)

def mulmodZeroLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MulmodZeroLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "mulmodLiteralZero"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "mulmod")
                              [ Solidity.Arg.positional
                                  (numberExpr "1")
                              , Solidity.Arg.positional
                                  (numberExpr "2")
                              , Solidity.Arg.positional
                                  (numberExpr "0") ]))) } ] } ] }

def mulmodZeroLiteralRejected : Bool :=
  Result.isError (SourceUnit.check mulmodZeroLiteralSource)

def mulmodSignedModulusSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadMulmodSignedModulus"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMulmodSigned"
                    params :=
                      [{ name := some "m"
                         ty := int256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "mulmod")
                              [ Solidity.Arg.positional
                                  (numberExpr "1")
                              , Solidity.Arg.positional
                                  (numberExpr "2")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.ident "m") ]))) } ] } ] }

def mulmodSignedModulusRejected : Bool :=
  Result.isError (SourceUnit.check mulmodSignedModulusSource)

def keccakBytesSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "KeccakBytes"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "hash"
                    returns :=
                      [{ name := none
                         ty := Solidity.Ty.bytesN 32
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "keccak256")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2, 3])) ]))) } ] } ] }

def keccakBytesAccepted : Bool :=
  sourceUnitAccepted? keccakBytesSource

def badKeccakUintSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadKeccakUint"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "hash"
                    returns :=
                      [{ name := none
                         ty := Solidity.Ty.bytesN 32
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident "keccak256")
                              [ Solidity.Arg.positional
                                  (numberExpr "1") ]))) } ] } ] }

def badKeccakUintRejected : Bool :=
  Result.isError (SourceUnit.check badKeccakUintSource)

def globalPrimitiveBuiltinDisciplineMatches : Bool :=
  addmodConstantAccepted &&
    addmodVariableModulusAccepted &&
    addmodZeroLiteralRejected &&
    mulmodZeroLiteralRejected &&
    keccakBytesAccepted &&
    addmodSignedArgumentRejected &&
    mulmodSignedModulusRejected &&
    badKeccakUintRejected

def constantFromStateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadConstantFromState"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") }
              , Solidity.ContractItem.stateVar
                  { name := "Y"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.constant
                    init :=
                      some (Solidity.Expr.ident "x") } ] } ] }

def constantFromStateRejected : Bool :=
  Result.isError (SourceUnit.check constantFromStateSource)

def fileConstantInContractSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "K"
            ty := uint256
            mutability := Solidity.VarMutability.constant
            init := some (numberExpr "1") }
      , Solidity.SourceItem.contract
          { name := "UsesFileConstant"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "K"))) } ] } ] }

def fileConstantInContractAccepted : Bool :=
  sourceUnitAccepted? fileConstantInContractSource

def stateConstantPureReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StateConstantPureRead"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "K"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.constant
                    init := some (numberExpr "1") }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "K"))) } ] } ] }

def stateConstantPureReadAccepted : Bool :=
  sourceUnitAccepted? stateConstantPureReadSource

def assignConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAssignConstant"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "K"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.constant
                    init := some (numberExpr "1") }
              , Solidity.ContractItem.function
                  { kind := Solidity.FunctionKind.function
                    name := some "f"
                    params := []
                    returns := []
                    visibility :=
                      some Solidity.Visibility.public_
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "K")
                            Solidity.AssignOp.assign
                            (numberExpr "2"))) } ] } ] }

def assignConstantRejected : Bool :=
  Result.isError (SourceUnit.check assignConstantSource)

def badFileConstantVisibilitySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "VISIBLE"
            ty := uint256
            visibility := some Solidity.Visibility.public_
            mutability := Solidity.VarMutability.constant
            init := some (numberExpr "1") } ] }

def badFileConstantVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check badFileConstantVisibilitySource)

def badFileConstantOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "OVERRIDES"
            ty := uint256
            override? := some { bases := [] }
            mutability := Solidity.VarMutability.constant
            init := some (numberExpr "1") } ] }

def badFileConstantOverrideRejected : Bool :=
  Result.isError (SourceUnit.check badFileConstantOverrideSource)

def badExternalStateVarSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadExternalStateVar"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    visibility :=
                      some Solidity.Visibility.external_ } ] } ] }

def badExternalStateVarRejected : Bool :=
  Result.isError (SourceUnit.check badExternalStateVarSource)

def immutableInternalFunctionTy : Ty :=
  Solidity.Ty.function [] []
    Solidity.StateMutability.pure
    Solidity.Visibility.internal_

def immutableExternalFunctionTy : Ty :=
  Solidity.Ty.function [] []
    Solidity.StateMutability.pure
    Solidity.Visibility.external_

def immutableInternalFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ImmutableInternalFunction"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := immutableInternalFunctionTy
                    mutability :=
                      Solidity.VarMutability.immutable } ] } ] }

def immutableInternalFunctionAccepted : Bool :=
  sourceUnitAccepted? immutableInternalFunctionSource

def badImmutableExternalFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadImmutableExternalFunction"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := immutableExternalFunctionTy
                    mutability :=
                      Solidity.VarMutability.immutable } ] } ] }

def badImmutableExternalFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badImmutableExternalFunctionSource)

def badImmutableStringSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadImmutableString"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "text"
                    ty := Solidity.Ty.string
                    mutability :=
                      Solidity.VarMutability.immutable } ] } ] }

def badImmutableStringRejected : Bool :=
  Result.isError (SourceUnit.check badImmutableStringSource)

def immutableAssignedInConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ImmutableAssignedInConstructor"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.immutable }
              , Solidity.ContractItem.function
                  { kind := Solidity.FunctionKind.constructor
                    params := []
                    returns := []
                    visibility := none
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "x")
                            Solidity.AssignOp.assign
                            (numberExpr "1"))) } ] } ] }

def immutableAssignedInConstructorAccepted : Bool :=
  sourceUnitAccepted? immutableAssignedInConstructorSource

def immutableAssignedInFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadImmutableAssignedInFunction"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.immutable }
              , Solidity.ContractItem.function
                  { kind := Solidity.FunctionKind.function
                    name := some "f"
                    params := []
                    returns := []
                    visibility :=
                      some Solidity.Visibility.public_
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "x")
                            Solidity.AssignOp.assign
                            (numberExpr "1"))) } ] } ] }

def immutableAssignedInFunctionRejected : Bool :=
  Result.isError (SourceUnit.check immutableAssignedInFunctionSource)

def immutableInlineConstantPureReadSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ImmutableInlineConstantPureRead"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.immutable
                    init := some (numberExpr "1") }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "x"))) } ] } ] }

def immutableInlineConstantPureReadAccepted : Bool :=
  sourceUnitAccepted? immutableInlineConstantPureReadSource

def immutableRuntimePureReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadImmutableRuntimePureRead"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.immutable }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "x"))) } ] } ] }

def immutableRuntimePureReadRejected : Bool :=
  Result.isError (SourceUnit.check immutableRuntimePureReadSource)

def transientUintSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TransientUint"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "flag"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.transient } ] } ] }

def transientUintAccepted : Bool :=
  sourceUnitAccepted? transientUintSource

def badTransientInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTransientInit"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "flag"
                    ty := uint256
                    mutability :=
                      Solidity.VarMutability.transient
                    init := some (numberExpr "1") } ] } ] }

def badTransientInitRejected : Bool :=
  Result.isError (SourceUnit.check badTransientInitSource)

def badTransientStringSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTransientString"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "text"
                    ty := Solidity.Ty.string
                    mutability :=
                      Solidity.VarMutability.transient } ] } ] }

def badTransientStringRejected : Bool :=
  Result.isError (SourceUnit.check badTransientStringSource)

def unknownUserTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnknownType"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := Solidity.Ty.user
                      (userPath "Missing") } ] } ] }

def unknownUserTypeRejected : Bool :=
  Result.isError (SourceUnit.check unknownUserTypeSource)

def zeroFixedArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ZeroFixedArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "xs"
                    ty := Solidity.Ty.array uint256
                      (some 0) } ] } ] }

def zeroFixedArrayRejected : Bool :=
  Result.isError (SourceUnit.check zeroFixedArraySource)

def emptyEnumSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum
          { name := "Empty", cases := [] } ] }

def emptyEnumRejected : Bool :=
  Result.isError (SourceUnit.check emptyEnumSource)

def colorEnum : Solidity.EnumDecl :=
  { name := "Color", cases := ["Red", "Blue"] }

def colorTy : Ty :=
  Solidity.Ty.user (userPath "Color")

def enumMemberFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "red"
    params := []
    returns := [{ name := none, ty := colorTy, location := none }]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName colorTy) "Red"))) }

def enumMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum colorEnum
      , Solidity.SourceItem.contract
          { name := "EnumUser"
            items :=
              [Solidity.ContractItem.function
                enumMemberFunction] } ] }

def enumMemberAccepted : Bool :=
  sourceUnitAccepted? enumMemberSource

def badEnumMemberFunction : Solidity.FunctionDecl :=
  { enumMemberFunction with
    name := some "green"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName colorTy) "Green"))) }

def badEnumMemberSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum colorEnum
      , Solidity.SourceItem.contract
          { name := "BadEnumUser"
            items :=
              [Solidity.ContractItem.function
                badEnumMemberFunction] } ] }

def badEnumMemberRejected : Bool :=
  Result.isError (SourceUnit.check badEnumMemberSource)

def enumMinMemberFunction : Solidity.FunctionDecl :=
  { enumMemberFunction with
    name := some "minimum"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName colorTy) "min"))) }

def enumMaxMemberFunction : Solidity.FunctionDecl :=
  { enumMemberFunction with
    name := some "maximum"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName colorTy) "max"))) }

def enumMinMaxSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum colorEnum
      , Solidity.SourceItem.contract
          { name := "EnumMinMax"
            items :=
              [ Solidity.ContractItem.function
                  enumMinMemberFunction
              , Solidity.ContractItem.function
                  enumMaxMemberFunction ] } ] }

def enumMinMaxAccepted : Bool :=
  sourceUnitAccepted? enumMinMaxSource

def enumConversionFunction (name : Name)
    (inner : Solidity.Expr) : Solidity.FunctionDecl :=
  { enumMemberFunction with
    name := some name
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName colorTy)
              [Solidity.Arg.positional inner]))) }

def enumConversionSource (contractName : Name)
    (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum colorEnum
      , Solidity.SourceItem.contract
          { name := contractName
            items := [Solidity.ContractItem.function fn] } ] }

def enumLiteralConversionAccepted : Bool :=
  sourceUnitAccepted?
    (enumConversionSource "EnumLiteralConversion"
      (enumConversionFunction "fromLiteral" (numberExpr "1")))

def enumOutOfRangeLiteralConversionRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (enumConversionSource "BadEnumOutOfRangeLiteral"
        (enumConversionFunction "fromLiteral" (numberExpr "2"))))

def enumNegativeLiteralConversionRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (enumConversionSource "BadEnumNegativeLiteral"
        (enumConversionFunction "fromLiteral"
          (Solidity.Expr.unary
            Solidity.UnaryOp.neg
            (numberExpr "1")))))

def enumTypedOutOfRangeConversionAccepted : Bool :=
  sourceUnitAccepted?
    (enumConversionSource "EnumTypedOutOfRangeConversion"
      (enumConversionFunction "fromTyped"
        (Solidity.Expr.call
          (Solidity.Expr.typeName uint256)
          [Solidity.Arg.positional (numberExpr "2")])))

def enumToUintFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "asUint"
    params := [{ name := some "choice", ty := colorTy, location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName uint256)
              [Solidity.Arg.positional
                (Solidity.Expr.ident "choice")]))) }

def enumToUintAccepted : Bool :=
  sourceUnitAccepted?
    (enumConversionSource "EnumToUint" enumToUintFunction)

def enumToIntSource : Solidity.SourceUnit :=
  enumConversionSource "BadEnumToInt"
    { enumToUintFunction with
      name := some "asInt"
      returns :=
        [{ name := none
           ty := Solidity.Ty.int 16
           location := none }]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.call
                (Solidity.Expr.typeName
                  (Solidity.Ty.int 16))
                [Solidity.Arg.positional
                  (Solidity.Expr.ident "choice")]))) }

def enumToIntRejected : Bool :=
  Result.isError (SourceUnit.check enumToIntSource)

def typeMaxFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "maxValue"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName uint256) "max"))) }

def typeMaxSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "TypeMax"
          items :=
            [Solidity.ContractItem.function
              typeMaxFunction] }] }

def typeMaxAccepted : Bool :=
  sourceUnitAccepted? typeMaxSource

def unitNumberReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "unitNumber"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.literal
              (Solidity.Literal.unitNumber "2.5"
                Solidity.UnitDenomination.ether)))) }

def unitNumberReturnSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "UnitNumber"
          items :=
            [Solidity.ContractItem.function
              unitNumberReturnFunction] }] }

def unitNumberReturnAccepted : Bool :=
  sourceUnitAccepted? unitNumberReturnSource

def fractionalWeiReturnSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "FractionalWei"
          items :=
            [ Solidity.ContractItem.function
                { unitNumberReturnFunction with
                  body :=
                    some
                      (Solidity.Stmt.returnValues
                        (some
                          (Solidity.Expr.literal
                            (Solidity.Literal.unitNumber "0.5"
                              Solidity.UnitDenomination.wei)))) } ] }] }

def fractionalWeiReturnRejected : Bool :=
  Result.isError (SourceUnit.check fractionalWeiReturnSource)

def subWeiEtherReturnSource : Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := "SubWeiEther"
          items :=
            [ Solidity.ContractItem.function
                { unitNumberReturnFunction with
                  body :=
                    some
                      (Solidity.Stmt.returnValues
                        (some
                          (Solidity.Expr.literal
                            (Solidity.Literal.unitNumber "1e-19"
                              Solidity.UnitDenomination.ether)))) } ] }] }

def subWeiEtherReturnRejected : Bool :=
  Result.isError (SourceUnit.check subWeiEtherReturnSource)

def contractCodeReturnFunction (contractName member : Name) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some member
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.typeName
                (Solidity.Ty.user (userPath contractName)))
              member))) }

def typeCreationCodeOtherSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CodeTarget" }
      , Solidity.SourceItem.contract
          { name := "CodeReader"
            items :=
              [ Solidity.ContractItem.function
                  (contractCodeReturnFunction "CodeTarget"
                    "creationCode") ] } ] }

def typeCreationCodeOtherAccepted : Bool :=
  sourceUnitAccepted? typeCreationCodeOtherSource

def typeCodeMemberSource (target : Solidity.ContractDecl)
    (readerName member : Name) : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract target
      , Solidity.SourceItem.contract
          { name := readerName
            items :=
              [ Solidity.ContractItem.function
                  (contractCodeReturnFunction target.name member) ] } ] }

def typeLibraryCreationCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { kind := Solidity.ContractKind.library
      name := "CodeLibrary" }
    "LibraryCreationCodeReader" "creationCode"

def typeLibraryRuntimeCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { kind := Solidity.ContractKind.library
      name := "RuntimeLibrary" }
    "LibraryRuntimeCodeReader" "runtimeCode"

def typeInterfaceCreationCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { kind := Solidity.ContractKind.interface
      name := "CodeInterface" }
    "InterfaceCreationCodeReader" "creationCode"

def typeInterfaceRuntimeCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { kind := Solidity.ContractKind.interface
      name := "RuntimeInterface" }
    "InterfaceRuntimeCodeReader" "runtimeCode"

def typeAbstractCreationCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { name := "CodeAbstract", abstract := true }
    "AbstractCreationCodeReader" "creationCode"

def typeAbstractRuntimeCodeSource : Solidity.SourceUnit :=
  typeCodeMemberSource
    { name := "RuntimeAbstract", abstract := true }
    "AbstractRuntimeCodeReader" "runtimeCode"

def typeCodeMemberKindDisciplineMatches : Bool :=
  sourceUnitAccepted? typeCreationCodeOtherSource &&
    sourceUnitAccepted? typeLibraryCreationCodeSource &&
    sourceUnitAccepted? typeLibraryRuntimeCodeSource &&
    Result.isError (SourceUnit.check typeInterfaceCreationCodeSource) &&
    Result.isError (SourceUnit.check typeInterfaceRuntimeCodeSource) &&
    Result.isError (SourceUnit.check typeAbstractCreationCodeSource) &&
    Result.isError (SourceUnit.check typeAbstractRuntimeCodeSource)

def typeCreationCodeSelfSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SelfCode"
            items :=
              [ Solidity.ContractItem.function
                  (contractCodeReturnFunction "SelfCode"
                    "creationCode") ] } ] }

def typeCreationCodeSelfRejected : Bool :=
  Result.isError (SourceUnit.check typeCreationCodeSelfSource)

def typeRuntimeCodeBaseContract : Solidity.ContractDecl :=
  { name := "RuntimeBase" }

def typeRuntimeCodeDerivedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          typeRuntimeCodeBaseContract
      , Solidity.SourceItem.contract
          { name := "RuntimeDerived"
            bases := [{ base := userPath "RuntimeBase" }]
            items :=
              [ Solidity.ContractItem.function
                  (contractCodeReturnFunction "RuntimeBase"
                    "runtimeCode") ] } ] }

def typeRuntimeCodeDerivedRejected : Bool :=
  Result.isError (SourceUnit.check typeRuntimeCodeDerivedSource)

def memoryMappingLocalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "m"
                  ty := some
                    (Solidity.Ty.mapping uint256 uint256)
                  location := some Solidity.DataLocation.memory } ]
              none
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "1"))) ]) }

def memoryMappingLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadMappingLocation"
            items := [Solidity.ContractItem.function
              memoryMappingLocalFunction] } ] }

def memoryMappingLocalRejected : Bool :=
  Result.isError (SourceUnit.check memoryMappingLocalSource)

def publicMappingParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesMap"
    params :=
      [ { name := some "m"
          ty := Solidity.Ty.mapping uint256 uint256
          location := some Solidity.DataLocation.storage } ] }

def publicMappingParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiMapping"
            items := [Solidity.ContractItem.function
              publicMappingParamFunction] } ] }

def publicMappingParamRejected : Bool :=
  Result.isError (SourceUnit.check publicMappingParamSource)

def mappingReadFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readMap"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "m")
              (numberExpr "1")))) }

def mappingReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MappingRead"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "m"
                    ty := Solidity.Ty.mapping
                      uint256 uint256 }
              , Solidity.ContractItem.function
                  mappingReadFunction ] } ] }

def mappingReadAccepted : Bool :=
  sourceUnitAccepted? mappingReadSource

def deleteMappingValueFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "deleteMapValue"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.unary
                Solidity.UnaryOp.delete
                (Solidity.Expr.index
                  (Solidity.Expr.ident "m")
                  (numberExpr "1")))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def deleteMappingValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DeleteMappingValue"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "m"
                    ty := Solidity.Ty.mapping
                      uint256 uint256 }
              , Solidity.ContractItem.function
                  deleteMappingValueFunction ] } ] }

def deleteMappingValueAccepted : Bool :=
  sourceUnitAccepted? deleteMappingValueSource

def deleteMappingVariableFunction : Solidity.FunctionDecl :=
  { deleteMappingValueFunction with
    name := some "deleteMap"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.unary
                Solidity.UnaryOp.delete
                (Solidity.Expr.ident "m"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def deleteMappingVariableSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DeleteMappingVariable"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "m"
                    ty := Solidity.Ty.mapping
                      uint256 uint256 }
              , Solidity.ContractItem.function
                  deleteMappingVariableFunction ] } ] }

def deleteMappingVariableRejected : Bool :=
  Result.isError (SourceUnit.check deleteMappingVariableSource)

def mappingStructWithMappingDecl : Solidity.StructDecl :=
  { name := "Ledger"
    fields :=
      [ { name := "total", ty := uint256 }
      , { name := "credits"
          ty := Solidity.Ty.mapping uint256 uint256 } ] }

def mappingStructWithMappingTy : Ty :=
  Solidity.Ty.user (userPath "Ledger")

def mappingStructFirstStateVar : Solidity.StateVarDecl :=
  { name := "first", ty := mappingStructWithMappingTy }

def mappingStructSecondStateVar : Solidity.StateVarDecl :=
  { name := "second", ty := mappingStructWithMappingTy }

def mappingStructStorageCopySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          mappingStructWithMappingDecl
      , Solidity.SourceItem.contract
          { name := "MappingStructStorageCopy"
            items :=
              [ Solidity.ContractItem.stateVar
                  mappingStructFirstStateVar
              , Solidity.ContractItem.stateVar
                  mappingStructSecondStateVar
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "first")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident
                                  "second"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def mappingStructStorageCopyRejected : Bool :=
  Result.isError (SourceUnit.check mappingStructStorageCopySource)

def mappingStructStorageRebindSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          mappingStructWithMappingDecl
      , Solidity.SourceItem.contract
          { name := "MappingStructStorageRebind"
            items :=
              [ Solidity.ContractItem.stateVar
                  mappingStructFirstStateVar
              , Solidity.ContractItem.stateVar
                  mappingStructSecondStateVar
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some mappingStructWithMappingTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some (Solidity.Expr.ident
                                "first"))
                          , Solidity.Stmt.varDecl
                              [ { name := some "other"
                                  ty := some mappingStructWithMappingTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some (Solidity.Expr.ident
                                "second"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "local")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident "other"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def mappingStructStorageRebindAccepted : Bool :=
  sourceUnitAccepted? mappingStructStorageRebindSource

def mappingStructMemoryLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          mappingStructWithMappingDecl
      , Solidity.SourceItem.contract
          { name := "MappingStructMemoryLocal"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "local"
                                  ty := some mappingStructWithMappingTy
                                  location :=
                                    some
                                      Solidity.DataLocation.memory } ]
                              none
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def mappingStructMemoryLocalRejected : Bool :=
  Result.isError (SourceUnit.check mappingStructMemoryLocalSource)

def mappingStructCalldataParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          mappingStructWithMappingDecl
      , Solidity.SourceItem.contract
          { name := "MappingStructCalldataParam"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    params :=
                      [ { name := some "input"
                          ty := mappingStructWithMappingTy
                          location :=
                            some
                              Solidity.DataLocation.calldata } ] } ] } ] }

def mappingStructCalldataParamRejected : Bool :=
  Result.isError (SourceUnit.check mappingStructCalldataParamSource)

def mappingStructInternalStorageParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          mappingStructWithMappingDecl
      , Solidity.SourceItem.contract
          { name := "MappingStructInternalStorageParam"
            items :=
              [ Solidity.ContractItem.stateVar
                  mappingStructFirstStateVar
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "readTotal"
                    params :=
                      [ { name := some "input"
                          ty := mappingStructWithMappingTy
                          location :=
                            some
                              Solidity.DataLocation.storage } ]
                    visibility :=
                      some Solidity.Visibility.internal_
                    mutability :=
                      Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "input")
                              "total"))) }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    mutability :=
                      Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.ident
                                "readTotal")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident
                                    "first") ]))) } ] } ] }

def mappingStructInternalStorageParamAccepted : Bool :=
  sourceUnitAccepted? mappingStructInternalStorageParamSource

def mappingStructContainingMappingDisciplineMatches : Bool :=
  mappingStructStorageCopyRejected &&
    mappingStructStorageRebindAccepted &&
    mappingStructMemoryLocalRejected &&
    mappingStructCalldataParamRejected &&
    mappingStructInternalStorageParamAccepted

def badMappingIndexFunction : Solidity.FunctionDecl :=
  { mappingReadFunction with
    name := some "badMapIndex"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "m")
              (boolExpr true)))) }

def badMappingIndexSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadMappingIndex"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "m"
                    ty := Solidity.Ty.mapping
                      uint256 uint256 }
              , Solidity.ContractItem.function
                  badMappingIndexFunction ] } ] }

def badMappingIndexRejected : Bool :=
  Result.isError (SourceUnit.check badMappingIndexSource)

def keyTy : Ty :=
  Solidity.Ty.user (userPath "Key")

def keyDecl : Solidity.UserValueTypeDecl :=
  { name := "Key", underlying := uint256 }

def userValueMappingKeyFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readByKey"
    params := [{ name := some "k", ty := keyTy, location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "m")
              (Solidity.Expr.ident "k")))) }

def userValueMappingKeySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType keyDecl
      , Solidity.SourceItem.contract
          { name := "UserValueMappingKey"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "m"
                    ty := Solidity.Ty.mapping
                      keyTy uint256 }
              , Solidity.ContractItem.function
                  userValueMappingKeyFunction ] } ] }

def userValueMappingKeyAccepted : Bool :=
  sourceUnitAccepted? userValueMappingKeySource

def signedMappingKeySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SignedMappingKey"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "values"
                    ty := Solidity.Ty.mapping
                      int256 uint256 }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := int256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident
                                "values")
                              (Solidity.Expr.ident
                                "key"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := int256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.ident
                                "values")
                              (Solidity.Expr.ident
                                "key")))) } ] } ] }

def signedMappingKeyAccepted : Bool :=
  sourceUnitAccepted? signedMappingKeySource

def stringLengthSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStringLength"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "stringLength"
                    params :=
                      [ { name := some "s"
                          ty := Solidity.Ty.string
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "s")
                              "length"))) } ] } ] }

def stringLengthRejected : Bool :=
  Result.isError (SourceUnit.check stringLengthSource)

def duplicateSignatureSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateFns"
            items :=
              [ Solidity.ContractItem.function
                  simpleReturnFunction
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.literal
                              (Solidity.Literal.number "9")))) } ] } ] }

def duplicateSignatureRejected : Bool :=
  Result.isError (SourceUnit.check duplicateSignatureSource)

def stateFunctionNameClashSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StateFunctionNameClash"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "clash", ty := uint256 }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with name := some "clash" } ] } ] }

def stateFunctionNameClashRejected : Bool :=
  Result.isError (SourceUnit.check stateFunctionNameClashSource)

def functionEventNameClashSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FunctionEventNameClash"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with name := some "Ping" }
              , Solidity.ContractItem.eventDecl
                  { name := "Ping"
                    params := [{ name := none, ty := uint256 }] } ] } ] }

def functionEventNameClashRejected : Bool :=
  Result.isError (SourceUnit.check functionEventNameClashSource)

def topLevelFunctionContractNameClashSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TopLevelClash" }
      , Solidity.SourceItem.freeFunction
          { simpleReturnFunction with
            name := some "TopLevelClash"
            visibility := none } ] }

def topLevelFunctionContractNameClashRejected : Bool :=
  Result.isError
    (SourceUnit.check topLevelFunctionContractNameClashSource)

def freeErrorOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError
          { name := "FreeErrorClash"
            params := [{ name := none, ty := uint256, location := none }] }
      , Solidity.SourceItem.freeError
          { name := "FreeErrorClash"
            params :=
              [ { name := none
                  ty := Solidity.Ty.address false
                  location := none } ] } ] }

def freeErrorOverloadRejected : Bool :=
  Result.isError (SourceUnit.check freeErrorOverloadSource)

def contractErrorOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContractErrorOverload"
            items :=
              [ Solidity.ContractItem.errorDecl
                  { name := "LocalBad"
                    params :=
                      [{ name := none
                         ty := uint256
                         location := none }] }
              , Solidity.ContractItem.errorDecl
                  { name := "LocalBad"
                    params :=
                      [ { name := none
                          ty := Solidity.Ty.address false
                          location := none } ] } ] } ] }

def contractErrorOverloadRejected : Bool :=
  Result.isError (SourceUnit.check contractErrorOverloadSource)

def abiClashContractTy : Ty :=
  Solidity.Ty.user (userPath "B")

def abiClashContractParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "clash"
    params :=
      [{ name := some "target", ty := abiClashContractTy, location := none }] }

def abiClashAddressParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "clash"
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address false
          location := none } ] }

def abiExternalSignatureClashSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "B" }
      , Solidity.SourceItem.contract
          { name := "AbiClash"
            items :=
              [ Solidity.ContractItem.function
                  abiClashContractParamFunction
              , Solidity.ContractItem.function
                  abiClashAddressParamFunction ] } ] }

def abiExternalSignatureClashRejected : Bool :=
  Result.isError (SourceUnit.check abiExternalSignatureClashSource)

def internalAbiTwinSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "B" }
      , Solidity.SourceItem.contract
          { name := "InternalAbiTwin"
            items :=
              [ Solidity.ContractItem.function
                  { abiClashContractParamFunction with
                    visibility := some Solidity.Visibility.internal_ }
              , Solidity.ContractItem.function
                  { abiClashAddressParamFunction with
                    visibility := some Solidity.Visibility.internal_ } ] } ] }

def internalAbiTwinAccepted : Bool :=
  sourceUnitAccepted? internalAbiTwinSource

def passThroughModifier : Solidity.ModifierDecl :=
  { name := "onlyReady"
    body := some Solidity.Stmt.modifierPlaceholder }

def modifierInvocationFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "withModifier"
    modifiers :=
      [ { target := userPath "onlyReady", args := [] } ] }

def modifierInvocationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierUser"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  passThroughModifier
              , Solidity.ContractItem.function
                  modifierInvocationFunction ] } ] }

def modifierInvocationAccepted : Bool :=
  sourceUnitAccepted? modifierInvocationSource

def returnThroughModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ReturnThroughModifier"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.modifierDecl
                  { name := "afterReturn"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.modifierPlaceholder
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "0")) ]) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility := some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    modifiers :=
                      [{ target := userPath "afterReturn"
                         args := [] }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "11")) ]) } ] } ] }

def returnThroughModifierAccepted : Bool :=
  sourceUnitAccepted? returnThroughModifierSource

def uncheckedArithmeticFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "uncheckedArithmetic"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "x", ty := some uint256, location := none }]
              (some (numberExpr "1"))
          , Solidity.Stmt.unchecked
              (Solidity.Stmt.block
                [Solidity.Stmt.expr
                  (Solidity.Expr.assign
                    (Solidity.Expr.ident "x")
                    Solidity.AssignOp.addAssign
                    (numberExpr "1"))])
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "x")) ]) }

def uncheckedArithmeticSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UncheckedArithmetic"
            items := [Solidity.ContractItem.function
              uncheckedArithmeticFunction] } ] }

def uncheckedArithmeticAccepted : Bool :=
  sourceUnitAccepted? uncheckedArithmeticSource

def uncheckedInternalMaxPlusOneExpr : Solidity.Expr :=
  Solidity.Expr.binary
    Solidity.BinaryOp.add
    (Solidity.Expr.member
      (Solidity.Expr.typeName uint256) "max")
    (numberExpr "1")

def uncheckedInternalCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UncheckedInternalCall"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "overflow"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some uncheckedInternalMaxPlusOneExpr)) }
              , Solidity.ContractItem.function
                  { name := some "id"
                    visibility :=
                      some Solidity.Visibility.internal_
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
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "value"))) }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "callOverflow"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.unchecked
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.call
                                (Solidity.Expr.ident
                                  "overflow") [])))) }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "callWithWrappedArg"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.unchecked
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "id")
                                [Solidity.Arg.positional
                                  uncheckedInternalMaxPlusOneExpr])))) } ] } ] }

def uncheckedInternalCallAccepted : Bool :=
  sourceUnitAccepted? uncheckedInternalCallSource

def internalReturnSubexpressionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalReturnSubexpression"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "base"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (numberExpr "41"))) }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "run"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.add
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "base")
                                [])
                              (numberExpr "1")))) } ] } ] }

def internalReturnSubexpressionAccepted : Bool :=
  sourceUnitAccepted? internalReturnSubexpressionSource

def internalReturnRightSubexpressionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalReturnRightSubexpression"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "run"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.add
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "5"))
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "read")
                                [])))) } ] } ] }

def internalReturnRightSubexpressionAccepted : Bool :=
  sourceUnitAccepted? internalReturnRightSubexpressionSource

def internalReturnShortCircuitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalReturnShortCircuit"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "mark"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "andSkip"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.boolAnd
                              (boolExpr false)
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "mark")
                                [])))) }
              , Solidity.ContractItem.function
                  { name := some "orSkip"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.boolOr
                              (boolExpr true)
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "mark")
                                [])))) }
              , Solidity.ContractItem.function
                  { name := some "andCall"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.boolAnd
                              (boolExpr true)
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "mark")
                                [])))) }
              , Solidity.ContractItem.function
                  { name := some "orCall"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.boolOr
                              (boolExpr false)
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "mark")
                                [])))) } ] } ] }

def internalReturnShortCircuitAccepted : Bool :=
  sourceUnitAccepted? internalReturnShortCircuitSource

def internalBinaryLocalCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalBinaryLocalCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "base"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (numberExpr "41"))) }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { name := some "setFive"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "5"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "mark"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "2"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "2"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , Solidity.ContractItem.function
                  { name := some "runVar"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.add
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "base")
                                    [])
                                  (numberExpr "1")))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runVarBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.add
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "setFive")
                                    [])
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "read")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssign"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "y")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.add
                                  (Solidity.Expr.assign
                                    (Solidity.Expr.ident "x")
                                    Solidity.AssignOp.assign
                                    (numberExpr "5"))
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "read")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "y")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.add
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "setFive")
                                    [])
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "read")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runVarShort"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.boolAnd
                                  (boolExpr false)
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "mark")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignShort"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "ok")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.boolOr
                                  (boolExpr true)
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "mark")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runVarShortBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.boolAnd
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident
                                      "flagFalse")
                                    [])
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "mark")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignShortBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "ok")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.boolOr
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "flagTrue")
                                    [])
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "mark")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignShortBothCall"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "ok")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.boolAnd
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "flagTrue")
                                    [])
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "mark")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalBinaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalBinaryLocalCallSource

def internalUnaryLocalCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalUnaryLocalCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , Solidity.ContractItem.function
                  { name := some "zero"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "11"))
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "0")) ]) }
              , Solidity.ContractItem.function
                  { name := some "minusFive"
                    visibility :=
                      some Solidity.Visibility.internal_
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
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "13"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.unary
                                  Solidity.UnaryOp.neg
                                  (Solidity.Expr.ident
                                    "seed"))) ]) }
              , Solidity.ContractItem.function
                  { name := some "runReturnNot"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.logicalNot
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "flagFalse")
                                [])))) }
              , Solidity.ContractItem.function
                  { name := some "runVarNot"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              (some
                                (Solidity.Expr.unary
                                  Solidity.UnaryOp.logicalNot
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident
                                      "flagFalse")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "ok")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignNot"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "ok"
                                 ty := some Solidity.Ty.bool
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "ok")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.unary
                                  Solidity.UnaryOp.logicalNot
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident
                                      "flagFalse")
                                    [])))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "ok")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runBitNot"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.bitNot
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "zero")
                                [])))) }
              , Solidity.ContractItem.function
                  { name := some "runNeg"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := int256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.neg
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "minusFive")
                                [Solidity.Arg.positional
                                  (numberExpr "5")])))) } ] } ] }

def internalUnaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalUnaryLocalCallSource

def internalTernaryCallExpr (name : Name) : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.ident name) []

def internalTernaryAssignXExpr (value : String) :
    Solidity.Expr :=
  Solidity.Expr.assign
    (Solidity.Expr.ident "x")
    Solidity.AssignOp.assign
    (numberExpr value)

def internalTernaryLocalCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalTernaryLocalCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (internalTernaryAssignXExpr "1")
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (internalTernaryAssignXExpr "2")
                          , Solidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , Solidity.ContractItem.function
                  { name := some "runReturnTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ternary
                              (internalTernaryCallExpr "flagTrue")
                              (internalTernaryAssignXExpr "21")
                              (internalTernaryAssignXExpr "22")))) }
              , Solidity.ContractItem.function
                  { name := some "runReturnFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ternary
                              (internalTernaryCallExpr "flagFalse")
                              (internalTernaryAssignXExpr "21")
                              (internalTernaryAssignXExpr "22")))) }
              , Solidity.ContractItem.function
                  { name := some "runVarTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (Solidity.Expr.ternary
                                  (internalTernaryCallExpr "flagTrue")
                                  (internalTernaryAssignXExpr "31")
                                  (internalTernaryAssignXExpr "32")))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "y")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ternary
                                  (internalTernaryCallExpr "flagFalse")
                                  (internalTernaryAssignXExpr "41")
                                  (internalTernaryAssignXExpr "42")))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) } ] } ] }

def internalTernaryLocalCallAccepted : Bool :=
  sourceUnitAccepted? internalTernaryLocalCallSource

def internalTernaryBranchCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalTernaryBranchCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "markThen"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (internalTernaryAssignXExpr "21")
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "markElse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (internalTernaryAssignXExpr "22")
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runReturnThen"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ternary
                              (boolExpr true)
                              (internalTernaryCallExpr "markThen")
                              (internalTernaryAssignXExpr "99")))) }
              , Solidity.ContractItem.function
                  { name := some "runReturnElse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ternary
                              (boolExpr false)
                              (internalTernaryAssignXExpr "99")
                              (internalTernaryCallExpr "markElse")))) }
              , Solidity.ContractItem.function
                  { name := some "runVarBothFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some
                                (Solidity.Expr.ternary
                                  (boolExpr false)
                                  (internalTernaryCallExpr "markThen")
                                  (internalTernaryCallExpr "markElse")))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssignBothTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "y")
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ternary
                                  (boolExpr true)
                                  (internalTernaryCallExpr "markThen")
                                  (internalTernaryCallExpr "markElse")))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) } ] } ] }

def internalTernaryBranchCallAccepted : Bool :=
  sourceUnitAccepted? internalTernaryBranchCallSource

def internalIfConditionCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalIfConditionCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "flagTrue"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "flagFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , Solidity.ContractItem.function
                  { name := some "runTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.ifElse
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "flagTrue")
                            [])
                          (Solidity.Stmt.returnValues
                            (some
                              (Solidity.Expr.binary
                                Solidity.BinaryOp.add
                                (Solidity.Expr.ident "x")
                                (numberExpr "1"))))
                          (some
                            (Solidity.Stmt.returnValues
                              (some (numberExpr "9"))))) }
              , Solidity.ContractItem.function
                  { name := some "runFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.ifElse
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "flagFalse")
                            [])
                          (Solidity.Stmt.returnValues
                            (some (numberExpr "9")))
                          (some
                            (Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.add
                                  (Solidity.Expr.ident "x")
                                  (numberExpr "2")))))) } ] } ] }

def internalIfConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalIfConditionCallSource

def internalWhileConditionCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalWhileConditionCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "keepGoing"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.ifElse
                          (Solidity.Expr.binary
                            Solidity.BinaryOp.lt
                            (Solidity.Expr.ident "x")
                            (numberExpr "3"))
                          (Solidity.Stmt.block
                            [ Solidity.Stmt.expr
                                (Solidity.Expr.assign
                                  (Solidity.Expr.ident "x")
                                  Solidity.AssignOp.addAssign
                                  (numberExpr "1"))
                            , Solidity.Stmt.returnValues
                                (some (boolExpr true)) ])
                          (some
                            (Solidity.Stmt.returnValues
                              (some (boolExpr false))))) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.whileLoop
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "keepGoing")
                                [])
                              Solidity.Stmt.empty
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalWhileConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalWhileConditionCallSource

def internalForPostCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalForPostCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "bump"
                    visibility :=
                      some Solidity.Visibility.internal_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "x")
                            Solidity.AssignOp.addAssign
                            (numberExpr "1"))) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "0"))
                          , Solidity.Stmt.forLoop
                              none
                              (some
                                (Solidity.Expr.binary
                                  Solidity.BinaryOp.lt
                                  (Solidity.Expr.ident "x")
                                  (numberExpr "3")))
                              (some
                                (Solidity.Expr.call
                                  (Solidity.Expr.ident "bump")
                                  []))
                              Solidity.Stmt.continue
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalForPostCallAccepted : Bool :=
  sourceUnitAccepted? internalForPostCallSource

def loopBreakContinueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LoopBreakContinue"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "runBreak"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "0"))
                          , Solidity.Stmt.whileLoop
                              (boolExpr true)
                              (Solidity.Stmt.block
                                [ Solidity.Stmt.expr
                                    (Solidity.Expr.assign
                                      (Solidity.Expr.ident "x")
                                      Solidity.AssignOp.addAssign
                                      (numberExpr "1"))
                                , Solidity.Stmt.ifElse
                                    (Solidity.Expr.binary
                                      Solidity.BinaryOp.eq
                                      (Solidity.Expr.ident "x")
                                      (numberExpr "3"))
                                    Solidity.Stmt.break
                                    none ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runContinue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "0"))
                          , Solidity.Stmt.varDecl
                              [{ name := some "y"
                                 ty := some uint256
                                 location := none }]
                              (some (numberExpr "0"))
                          , Solidity.Stmt.whileLoop
                              (Solidity.Expr.binary
                                Solidity.BinaryOp.lt
                                (Solidity.Expr.ident "x")
                                (numberExpr "5"))
                              (Solidity.Stmt.block
                                [ Solidity.Stmt.expr
                                    (Solidity.Expr.assign
                                      (Solidity.Expr.ident "x")
                                      Solidity.AssignOp.addAssign
                                      (numberExpr "1"))
                                , Solidity.Stmt.ifElse
                                    (Solidity.Expr.binary
                                      Solidity.BinaryOp.eq
                                      (Solidity.Expr.binary
                                        Solidity.BinaryOp.mod
                                        (Solidity.Expr.ident "x")
                                        (numberExpr "2"))
                                      (numberExpr "0"))
                                    Solidity.Stmt.continue
                                    none
                                , Solidity.Stmt.expr
                                    (Solidity.Expr.assign
                                      (Solidity.Expr.ident "y")
                                      Solidity.AssignOp.addAssign
                                      (Solidity.Expr.ident "x")) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "y")) ]) } ] } ] }

def loopBreakContinueAccepted : Bool :=
  sourceUnitAccepted? loopBreakContinueSource

def breakOutsideLoopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BreakOutsideLoop"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some Solidity.Visibility.public_
                    body := some Solidity.Stmt.break } ] } ] }

def breakOutsideLoopRejected : Bool :=
  Result.isError (SourceUnit.check breakOutsideLoopSource)

def continueOutsideLoopSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContinueOutsideLoop"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some Solidity.Visibility.public_
                    body := some Solidity.Stmt.continue } ] } ] }

def continueOutsideLoopRejected : Bool :=
  Result.isError (SourceUnit.check continueOutsideLoopSource)

def loopControlPlacementDisciplineMatches : Bool :=
  loopBreakContinueAccepted &&
    breakOutsideLoopRejected &&
    continueOutsideLoopRejected

def namedReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NamedReturn"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "stop"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "99")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runFallthrough"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "out")
                            Solidity.AssignOp.assign
                            (numberExpr "9"))) }
              , Solidity.ContractItem.function
                  { name := some "runBare"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "out")
                                Solidity.AssignOp.assign
                                (numberExpr "11"))
                          , Solidity.Stmt.returnValues none
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "out")
                                Solidity.AssignOp.assign
                                (numberExpr "99")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runDefault"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body := some Solidity.Stmt.empty } ] } ] }

def namedReturnAccepted : Bool :=
  sourceUnitAccepted? namedReturnSource

def namedBareReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NamedBareReturn"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "out")
                                Solidity.AssignOp.assign
                                (numberExpr "12"))
                          , Solidity.Stmt.returnValues none ]) } ] } ] }

def namedBareReturnAccepted : Bool :=
  sourceUnitAccepted? namedBareReturnSource

def unnamedBareReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnnamedBareReturn"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := none
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues none) } ] } ] }

def unnamedBareReturnRejected : Bool :=
  Result.isError (SourceUnit.check unnamedBareReturnSource)

def internalRequireConditionCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalRequireConditionCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , Solidity.ContractItem.function
                  { name := some "okTrue"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr true)) ]) }
              , Solidity.ContractItem.function
                  { name := some "okFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some (boolExpr false)) ]) }
              , Solidity.ContractItem.function
                  { name := some "runAssert"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "assert")
                                [Solidity.Arg.positional
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "okTrue")
                                    [])])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runRequire"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "okTrue")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.string
                                        "bad")) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runRequireFail"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident
                                        "okFalse")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.string
                                        "bad")) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runRequireCustomFail"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident
                                        "okFalse")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "Bad")
                                      [Solidity.Arg.positional
                                        (numberExpr "7")]) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalRequireConditionCallAccepted : Bool :=
  sourceUnitAccepted? internalRequireConditionCallSource

def internalRequireReasonCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalRequireReasonCall"
            items :=
              [ Solidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "note"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.string
                         location :=
                           some Solidity.DataLocation.memory }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "9"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.literal
                                  (Solidity.Literal.string
                                    "ok"))) ]) }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "okTrue"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.literal
                                  (Solidity.Literal.bool
                                    true))) ]) }
              , Solidity.ContractItem.function
                  { name := some "okFalse"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := Solidity.Ty.bool
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "1"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.literal
                                  (Solidity.Literal.bool
                                    false))) ]) }
              , Solidity.ContractItem.function
                  { name := some "runReasonTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.bool true))
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "note")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runCustomFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.literal
                                      (Solidity.Literal.bool false))
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "Bad")
                                      [Solidity.Arg.positional
                                        (Solidity.Expr.call
                                          (Solidity.Expr.ident
                                            "value")
                                          [])]) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runBothReasonTrue"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident
                                        "okTrue")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "note")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runBothCustomFalse"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "require")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident
                                        "okFalse")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "Bad")
                                      [Solidity.Arg.positional
                                        (Solidity.Expr.call
                                          (Solidity.Expr.ident
                                            "value")
                                          [])]) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalRequireReasonCallAccepted : Bool :=
  sourceUnitAccepted? internalRequireReasonCallSource

def requireUintReasonSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadRequireUintReason"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badRequireUintReason"
                    returns := []
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "require")
                            [ Solidity.Arg.positional
                                (boolExpr true)
                            , Solidity.Arg.positional
                                (numberExpr "7") ])) } ] } ] }

def requireUintReasonRejected : Bool :=
  Result.isError (SourceUnit.check requireUintReasonSource)

def revertUintReasonSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadRevertUintReason"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badRevertUintReason"
                    returns := []
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "revert")
                            [Solidity.Arg.positional
                              (numberExpr "7")])) } ] } ] }

def revertUintReasonRejected : Bool :=
  Result.isError (SourceUnit.check revertUintReasonSource)

def internalEmitArgumentCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalEmitArgumentCall"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Seen"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         indexed := false }] }
              , Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.emitEvent
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Seen")
                                [Solidity.Arg.positional
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "value")
                                    [])])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalEmitArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalEmitArgumentCallSource

def internalEmitTwoArgumentCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalEmitTwoArgumentCall"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Seen"
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          indexed := false }
                      , { name := some "right"
                          ty := uint256
                          indexed := false } ] }
              , Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { name := some "runLeft"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.emitEvent
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Seen")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "value")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.binary
                                      Solidity.BinaryOp.add
                                      (Solidity.Expr.ident "x")
                                      (numberExpr "1")) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runRight"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.emitEvent
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Seen")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.assign
                                      (Solidity.Expr.ident "x")
                                      Solidity.AssignOp.assign
                                      (numberExpr "5"))
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "read")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.emitEvent
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Seen")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "value")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "read")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              ] } ] }

def internalEmitTwoArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalEmitTwoArgumentCallSource

def internalRevertArgumentCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalRevertArgumentCall"
            items :=
              [ Solidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }] }
              , Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.revertCall
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Bad")
                                [Solidity.Arg.positional
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "value")
                                    [])])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalRevertArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalRevertArgumentCallSource

def internalRevertTwoArgumentCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalRevertTwoArgumentCall"
            items :=
              [ Solidity.ContractItem.errorDecl
                  { name := "Bad"
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ] }
              , Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "7"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { name := some "runLeft"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.revertCall
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Bad")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "value")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.binary
                                      Solidity.BinaryOp.add
                                      (Solidity.Expr.ident "x")
                                      (numberExpr "1")) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runRight"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.revertCall
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Bad")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.assign
                                      (Solidity.Expr.ident "x")
                                      Solidity.AssignOp.assign
                                      (numberExpr "5"))
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "read")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "runBoth"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.revertCall
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "Bad")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "value")
                                      [])
                                , Solidity.Arg.positional
                                    (Solidity.Expr.call
                                      (Solidity.Expr.ident "read")
                                      []) ])
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) } ] } ] }

def internalRevertTwoArgumentCallAccepted : Bool :=
  sourceUnitAccepted? internalRevertTwoArgumentCallSource

def assertBoolConditionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AssertBoolCondition"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "ok"
                    visibility :=
                      some Solidity.Visibility.external_
                    returns := []
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "assert")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.literal
                                  (Solidity.Literal.bool true)) ])) } ] } ] }

def assertBoolConditionAccepted : Bool :=
  sourceUnitAccepted? assertBoolConditionSource

def assertUintConditionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAssertUintCondition"
            items :=
              [ Solidity.ContractItem.function
                  { name := some "bad"
                    visibility :=
                      some Solidity.Visibility.external_
                    returns := []
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "assert")
                            [ Solidity.Arg.positional
                                (numberExpr "1") ])) } ] } ] }

def assertUintConditionRejected : Bool :=
  Result.isError (SourceUnit.check assertUintConditionSource)

def assertBuiltinDisciplineMatches : Bool :=
  assertBoolConditionAccepted &&
    assertUintConditionRejected

def requireRevertBuiltinDisciplineMatches : Bool :=
  internalRequireConditionCallAccepted &&
    internalRequireReasonCallAccepted &&
    requireUintReasonRejected &&
    revertUintReasonRejected &&
    internalRevertArgumentCallAccepted &&
    internalRevertTwoArgumentCallAccepted

def internalTupleReturnCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalTupleReturnCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "value"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "5"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "value")
                                    [])
                              , Solidity.TupleItem.value
                                  (Solidity.Expr.binary
                                    Solidity.BinaryOp.add
                                    (Solidity.Expr.ident "x")
                                    (numberExpr "1")) ]))) } ] } ] }

def internalTupleReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleReturnCallSource

def internalTupleRightReturnCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalTupleRightReturnCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (Solidity.Expr.assign
                                    (Solidity.Expr.ident "x")
                                    Solidity.AssignOp.assign
                                    (numberExpr "5"))
                              , Solidity.TupleItem.value
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "read")
                                    []) ]))) } ] } ] }

def internalTupleRightReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleRightReturnCallSource

def internalTupleBothReturnCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalTupleBothReturnCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256 }
              , Solidity.ContractItem.function
                  { name := some "setFive"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.ident "x")
                                Solidity.AssignOp.assign
                                (numberExpr "5"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.ident "x")) ]) }
              , Solidity.ContractItem.function
                  { name := some "read"
                    visibility :=
                      some Solidity.Visibility.internal_
                    returns :=
                      [{ name := some "out"
                         ty := uint256
                         location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "x"))) }
              , Solidity.ContractItem.function
                  { name := some "run"
                    visibility :=
                      some Solidity.Visibility.public_
                    returns :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "setFive")
                                    [])
                              , Solidity.TupleItem.value
                                  (Solidity.Expr.call
                                    (Solidity.Expr.ident "read")
                                    []) ]))) } ] } ] }

def internalTupleBothReturnCallAccepted : Bool :=
  sourceUnitAccepted? internalTupleBothReturnCallSource

def nestedUncheckedFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "nestedUnchecked"
    body :=
      some
        (Solidity.Stmt.unchecked
          (Solidity.Stmt.block
            [Solidity.Stmt.unchecked
              (Solidity.Stmt.block
                [Solidity.Stmt.empty])])) }

def nestedUncheckedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedUnchecked"
            items := [Solidity.ContractItem.function
              nestedUncheckedFunction] } ] }

def nestedUncheckedRejected : Bool :=
  Result.isError (SourceUnit.check nestedUncheckedSource)

def uncheckedPlaceholderModifier : Solidity.ModifierDecl :=
  { name := "uncheckedPlaceholder"
    body :=
      some
        (Solidity.Stmt.unchecked
          (Solidity.Stmt.block
            [Solidity.Stmt.modifierPlaceholder])) }

def uncheckedPlaceholderFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usesUncheckedPlaceholder"
    modifiers :=
      [{ target := userPath "uncheckedPlaceholder", args := [] }] }

def uncheckedPlaceholderSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UncheckedPlaceholder"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  uncheckedPlaceholderModifier
              , Solidity.ContractItem.function
                  uncheckedPlaceholderFunction ] } ] }

def uncheckedPlaceholderRejected : Bool :=
  Result.isError (SourceUnit.check uncheckedPlaceholderSource)

def uncheckedPlacementDisciplineMatches : Bool :=
  uncheckedArithmeticAccepted &&
    nestedUncheckedRejected &&
    uncheckedPlaceholderRejected

def emptyInlineAssemblyFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emptyAssembly"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.inlineAssembly ""
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def emptyInlineAssemblySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EmptyInlineAssembly"
            items := [Solidity.ContractItem.function
              emptyInlineAssemblyFunction] } ] }

def emptyInlineAssemblyRejected : Bool :=
  Result.isError (SourceUnit.check emptyInlineAssemblySource)

def nonemptyInlineAssemblySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonemptyInlineAssembly"
            items :=
              [ Solidity.ContractItem.function
                  { emptyInlineAssemblyFunction with
                    name := some "nonemptyAssembly"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.inlineAssembly "x := 1"
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def nonemptyInlineAssemblyRejected : Bool :=
  Result.isError (SourceUnit.check nonemptyInlineAssemblySource)

def unknownModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnknownModifier"
            items := [Solidity.ContractItem.function
              modifierInvocationFunction] } ] }

def unknownModifierRejected : Bool :=
  Result.isError (SourceUnit.check unknownModifierSource)

def duplicateModifierParamNameSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateModifierParamName"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { name := "only"
                    params :=
                      [ { name := some "value"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body := some Solidity.Stmt.modifierPlaceholder } ] } ] }

def duplicateModifierParamNameRejected : Bool :=
  Result.isError (SourceUnit.check duplicateModifierParamNameSource)

def modifierOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierOverload"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { name := "guarded"
                    params :=
                      [{ name := some "value"
                         ty := uint256
                         location := none }]
                    body :=
                      some Solidity.Stmt.modifierPlaceholder }
              , Solidity.ContractItem.modifierDecl
                  { name := "guarded"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    body :=
                      some Solidity.Stmt.modifierPlaceholder } ] } ] }

def modifierOverloadRejected : Bool :=
  Result.isError (SourceUnit.check modifierOverloadSource)

def valueOption (amount : String) : Solidity.CallOption :=
  Solidity.CallOption.named "value"
    (Solidity.Expr.literal
      (Solidity.Literal.number amount))

def gasOption (amount : String) : Solidity.CallOption :=
  Solidity.CallOption.named "gas"
    (Solidity.Expr.literal
      (Solidity.Literal.number amount))

def saltOption (expr : Solidity.Expr) :
    Solidity.CallOption :=
  Solidity.CallOption.named "salt" expr

def bytes32ZeroExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 32))
    [Solidity.Arg.positional (numberExpr "0")]

def seedConstructor
    (mutability : Solidity.StateMutability) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.constructor
    name := none
    params :=
      [ { name := some "seed"
          ty := uint256
          location := none } ]
    returns := []
    visibility := none
    mutability := mutability
    body := some Solidity.Stmt.empty }

def assigningSeedConstructorWithVisibility
    (visibility? : Option Solidity.Visibility) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.constructor
    name := none
    params :=
      [ { name := some "seed"
          ty := uint256
          location := none } ]
    returns := []
    visibility := visibility?
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.expr
          (Solidity.Expr.assign
            (Solidity.Expr.ident "x")
            Solidity.AssignOp.assign
            (Solidity.Expr.ident "seed"))) }

def constructorVisibilitySource
    (contractName : Name) (abstract : Bool)
    (visibility? : Option Solidity.Visibility) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            abstract := abstract
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x", ty := uint256 }
              , Solidity.ContractItem.function
                  (assigningSeedConstructorWithVisibility visibility?) ] } ] }

def publicConstructorVisibilitySource : Solidity.SourceUnit :=
  constructorVisibilitySource "PublicConstructorVisibility" false
    (some Solidity.Visibility.public_)

def publicConstructorVisibilityAccepted : Bool :=
  sourceUnitAccepted? publicConstructorVisibilitySource

def abstractInternalConstructorVisibilitySource :
    Solidity.SourceUnit :=
  constructorVisibilitySource "AbstractInternalConstructorVisibility" true
    (some Solidity.Visibility.internal_)

def abstractInternalConstructorVisibilityAccepted : Bool :=
  sourceUnitAccepted? abstractInternalConstructorVisibilitySource

def concreteInternalConstructorVisibilitySource :
    Solidity.SourceUnit :=
  constructorVisibilitySource "ConcreteInternalConstructorVisibility" false
    (some Solidity.Visibility.internal_)

def concreteInternalConstructorVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check concreteInternalConstructorVisibilitySource)

def abstractPublicConstructorVisibilitySource :
    Solidity.SourceUnit :=
  constructorVisibilitySource "AbstractPublicConstructorVisibility" true
    (some Solidity.Visibility.public_)

def abstractPublicConstructorVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check abstractPublicConstructorVisibilitySource)

def privateConstructorVisibilitySource : Solidity.SourceUnit :=
  constructorVisibilitySource "PrivateConstructorVisibility" false
    (some Solidity.Visibility.private_)

def privateConstructorVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check privateConstructorVisibilitySource)

def externalConstructorVisibilitySource : Solidity.SourceUnit :=
  constructorVisibilitySource "ExternalConstructorVisibility" false
    (some Solidity.Visibility.external_)

def externalConstructorVisibilityRejected : Bool :=
  Result.isError (SourceUnit.check externalConstructorVisibilitySource)

def constructorVisibilityDisciplineAccepted : Bool :=
  publicConstructorVisibilityAccepted &&
    abstractInternalConstructorVisibilityAccepted

def constructorVisibilityDisciplineRejected : Bool :=
  concreteInternalConstructorVisibilityRejected &&
    abstractPublicConstructorVisibilityRejected &&
    privateConstructorVisibilityRejected &&
    externalConstructorVisibilityRejected

def constructorVisibilityDisciplineMatches : Bool :=
  constructorVisibilityDisciplineAccepted &&
    constructorVisibilityDisciplineRejected

def pointStorageConstructor
    (location : Option Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.constructor
    name := none
    params :=
      [ { name := some "point"
          ty := pointTy
          location := location } ]
    returns := []
    visibility := none
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.expr
          (Solidity.Expr.assign
            (Solidity.Expr.ident "x")
            Solidity.AssignOp.assign
            (Solidity.Expr.member
              (Solidity.Expr.ident "point") "x"))) }

def constructorDataLocationSource
    (contractName : Name) (abstract : Bool)
    (constructor : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := contractName
            abstract := abstract
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x", ty := uint256 }
              , Solidity.ContractItem.function
                  constructor ] } ] }

def abstractStorageConstructorParamSource : Solidity.SourceUnit :=
  constructorDataLocationSource "AbstractStorageConstructorParam" true
    (pointStorageConstructor
      (some Solidity.DataLocation.storage))

def abstractStorageConstructorParamAccepted : Bool :=
  sourceUnitAccepted? abstractStorageConstructorParamSource

def concreteStorageConstructorParamSource : Solidity.SourceUnit :=
  constructorDataLocationSource "ConcreteStorageConstructorParam" false
    (pointStorageConstructor
      (some Solidity.DataLocation.storage))

def concreteStorageConstructorParamRejected : Bool :=
  Result.isError (SourceUnit.check concreteStorageConstructorParamSource)

def calldataConstructorParamSource : Solidity.SourceUnit :=
  constructorDataLocationSource "CalldataConstructorParam" true
    (pointStorageConstructor
      (some Solidity.DataLocation.calldata))

def calldataConstructorParamRejected : Bool :=
  Result.isError (SourceUnit.check calldataConstructorParamSource)

def missingConstructorLocationSource : Solidity.SourceUnit :=
  constructorDataLocationSource "MissingConstructorLocation" false
    (pointStorageConstructor none)

def missingConstructorLocationRejected : Bool :=
  Result.isError (SourceUnit.check missingConstructorLocationSource)

def valueTypeMemoryConstructorSource : Solidity.SourceUnit :=
  constructorDataLocationSource "ValueTypeMemoryConstructor" false
    { seedConstructor Solidity.StateMutability.nonpayable with
      params :=
        [ { name := some "seed"
            ty := uint256
            location := some Solidity.DataLocation.memory } ] }

def valueTypeMemoryConstructorRejected : Bool :=
  Result.isError (SourceUnit.check valueTypeMemoryConstructorSource)

def constructorDataLocationDisciplineMatches : Bool :=
  abstractStorageConstructorParamAccepted &&
    concreteStorageConstructorParamRejected &&
    calldataConstructorParamRejected &&
    missingConstructorLocationRejected &&
    valueTypeMemoryConstructorRejected

def constructorTargetTy : Ty :=
  Solidity.Ty.user (userPath "CtorTarget")

def constructorTargetContract : Solidity.ContractDecl :=
  { name := "CtorTarget"
    items :=
      [Solidity.ContractItem.function
        (seedConstructor Solidity.StateMutability.nonpayable)] }

def constructorCreateFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "make"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.newExpr constructorTargetTy
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def constructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "CtorMaker"
            items :=
              [Solidity.ContractItem.function
                constructorCreateFunction] } ] }

def constructorCreateAccepted : Bool :=
  sourceUnitAccepted? constructorCreateSource

def badConstructorTypeFunction : Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeBadType"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.newExpr constructorTargetTy
                [Solidity.Arg.named "seed" (boolExpr true)])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def badConstructorTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadCtorMaker"
            items :=
              [Solidity.ContractItem.function
                badConstructorTypeFunction] } ] }

def badConstructorTypeRejected : Bool :=
  Result.isError (SourceUnit.check badConstructorTypeSource)

def missingConstructorArgFunction : Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeMissing"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.newExpr constructorTargetTy [])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def missingConstructorArgSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "MissingCtorArgMaker"
            items :=
              [Solidity.ContractItem.function
                missingConstructorArgFunction] } ] }

def missingConstructorArgRejected : Bool :=
  Result.isError (SourceUnit.check missingConstructorArgSource)

def payableConstructorTargetTy : Ty :=
  Solidity.Ty.user (userPath "PayableCtorTarget")

def payableConstructorTargetContract : Solidity.ContractDecl :=
  { name := "PayableCtorTarget"
    items :=
      [Solidity.ContractItem.function
        (seedConstructor Solidity.StateMutability.payable)] }

def payableConstructorCreateFunction : Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makePayable"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr
                  payableConstructorTargetTy [])
                [valueOption "1"]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def payableConstructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          payableConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "PayableCtorMaker"
            items :=
              [Solidity.ContractItem.function
                payableConstructorCreateFunction] } ] }

def payableConstructorCreateAccepted : Bool :=
  sourceUnitAccepted? payableConstructorCreateSource

def viewConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewConstructor"
            items :=
              [ Solidity.ContractItem.function
                  (seedConstructor
                    Solidity.StateMutability.view) ] } ] }

def viewConstructorRejected : Bool :=
  Result.isError (SourceUnit.check viewConstructorSource)

def pureConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureConstructor"
            items :=
              [ Solidity.ContractItem.function
                  (seedConstructor
                    Solidity.StateMutability.pure) ] } ] }

def pureConstructorRejected : Bool :=
  Result.isError (SourceUnit.check pureConstructorSource)

def saltedConstructorCreateFunction : Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeSalted"
    params :=
      [{ name := some "salt"
         ty := Solidity.Ty.bytesN 32
         location := none }]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr constructorTargetTy [])
                [saltOption (Solidity.Expr.ident "salt")]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def saltedConstructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "SaltedCtorMaker"
            items :=
              [Solidity.ContractItem.function
                saltedConstructorCreateFunction] } ] }

def saltedConstructorCreateAccepted : Bool :=
  sourceUnitAccepted? saltedConstructorCreateSource

def uintSaltConstructorCreateFunction :
    Solidity.FunctionDecl :=
  { saltedConstructorCreateFunction with
    name := some "makeUintSalted"
    params :=
      [{ name := some "salt"
         ty := uint256
         location := none }] }

def uintSaltConstructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadUintSaltCtorMaker"
            items :=
              [Solidity.ContractItem.function
                uintSaltConstructorCreateFunction] } ] }

def uintSaltConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.check uintSaltConstructorCreateSource)

def literalSaltConstructorCreateFunction :
    Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeLiteralSalted"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr constructorTargetTy [])
                [saltOption (numberExpr "1")]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def literalSaltConstructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadLiteralSaltCtorMaker"
            items :=
              [Solidity.ContractItem.function
                literalSaltConstructorCreateFunction] } ] }

def literalSaltConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.check literalSaltConstructorCreateSource)

def gasConstructorCreateFunction : Solidity.FunctionDecl :=
  { constructorCreateFunction with
    name := some "makeGasCreate"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr constructorTargetTy [])
                [gasOption "1"]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def gasConstructorCreateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadGasCtorMaker"
            items :=
              [Solidity.ContractItem.function
                gasConstructorCreateFunction] } ] }

def gasConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.check gasConstructorCreateSource)

def duplicateSaltConstructorCreateFunction :
    Solidity.FunctionDecl :=
  { saltedConstructorCreateFunction with
    name := some "makeDuplicateSalted"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr constructorTargetTy [])
                [ saltOption (Solidity.Expr.ident "salt")
                , saltOption (Solidity.Expr.ident "salt") ]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def duplicateSaltConstructorCreateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadDuplicateSaltCtorMaker"
            items :=
              [Solidity.ContractItem.function
                duplicateSaltConstructorCreateFunction] } ] }

def duplicateSaltConstructorCreateRejected : Bool :=
  Result.isError (SourceUnit.check duplicateSaltConstructorCreateSource)

def contractCreationCallOptionDisciplineMatches : Bool :=
  saltedConstructorCreateAccepted &&
    uintSaltConstructorCreateRejected &&
    literalSaltConstructorCreateRejected &&
    gasConstructorCreateRejected &&
    duplicateSaltConstructorCreateRejected

def nonpayableConstructorValueFunction :
    Solidity.FunctionDecl :=
  { payableConstructorCreateFunction with
    name := some "makeNonpayableValue"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr constructorTargetTy [])
                [valueOption "1"]
                [Solidity.Arg.named "seed" (numberExpr "7")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def nonpayableConstructorValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract constructorTargetContract
      , Solidity.SourceItem.contract
          { name := "BadValueCtorMaker"
            items :=
              [Solidity.ContractItem.function
                nonpayableConstructorValueFunction] } ] }

def nonpayableConstructorValueRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableConstructorValueSource)

def baseConstructorContract : Solidity.ContractDecl :=
  { name := "CtorBase"
    items :=
      [Solidity.ContractItem.function
        (seedConstructor Solidity.StateMutability.nonpayable)] }

def derivedBaseConstructorGood : Solidity.ContractDecl :=
  { name := "CtorDerived"
    bases :=
      [{ base := userPath "CtorBase"
         args := [Solidity.Arg.positional (numberExpr "4")] }]
    items :=
      [Solidity.ContractItem.function simpleReturnFunction] }

def baseConstructorArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          derivedBaseConstructorGood ] }

def baseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? baseConstructorArgsSource

def namedBaseConstructorContract : Solidity.ContractDecl :=
  { name := "NamedCtorBase"
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            params :=
              [ { name := some "left"
                  ty := uint256
                  location := none }
              , { name := some "right"
                  ty := uint256
                  location := none } ]
            body := some Solidity.Stmt.empty } ] }

def namedBaseConstructorArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract namedBaseConstructorContract
      , Solidity.SourceItem.contract
          { name := "NamedCtorDerived"
            bases :=
              [{ base := userPath "NamedCtorBase"
                 args :=
                  [ Solidity.Arg.named "right" (numberExpr "2")
                  , Solidity.Arg.named "left" (numberExpr "1") ] }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def namedBaseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? namedBaseConstructorArgsSource

def duplicateNamedBaseConstructorArgsSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract namedBaseConstructorContract
      , Solidity.SourceItem.contract
          { name := "DuplicateNamedCtorDerived"
            bases :=
              [{ base := userPath "NamedCtorBase"
                 args :=
                  [ Solidity.Arg.named "left" (numberExpr "1")
                  , Solidity.Arg.named "left" (numberExpr "2") ] }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def duplicateNamedBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check duplicateNamedBaseConstructorArgsSource)

def baseConstructorFileConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "BASE_SEED"
            ty := uint256
            mutability := Solidity.VarMutability.constant
            init := some (numberExpr "7") }
      , Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          { name := "FileConstantCtorArg"
            bases :=
              [{ base := userPath "CtorBase"
                 args :=
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "BASE_SEED")] }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def baseConstructorFileConstantAccepted : Bool :=
  sourceUnitAccepted? baseConstructorFileConstantSource

def baseConstructorStateArgSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          { name := "BadStateCtorArg"
            bases :=
              [{ base := userPath "CtorBase"
                 args :=
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "seed")] }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "seed"
                    ty := uint256
                    init := some (numberExpr "7") }
              , Solidity.ContractItem.function
                  simpleReturnFunction ] } ] }

def baseConstructorStateArgRejected : Bool :=
  Result.isError (SourceUnit.check baseConstructorStateArgSource)

def derivedBaseConstructorBad : Solidity.ContractDecl :=
  { derivedBaseConstructorGood with
    name := "BadCtorDerived"
    bases :=
      [{ base := userPath "CtorBase"
         args := [Solidity.Arg.positional (boolExpr true)] }] }

def badBaseConstructorArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          derivedBaseConstructorBad ] }

def badBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check badBaseConstructorArgsSource)

def derivedBaseConstructorModifierGood :
    Solidity.ContractDecl :=
  { name := "CtorModifierDerived"
    bases := [{ base := userPath "CtorBase" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            params :=
              [ { name := some "seed"
                  ty := uint256
                  location := none } ]
            modifiers :=
              [ { target := userPath "CtorBase"
                  args :=
                    [ Solidity.Arg.positional
                        (Solidity.Expr.binary
                          Solidity.BinaryOp.mul
                          (Solidity.Expr.ident "seed")
                          (Solidity.Expr.ident "seed")) ] } ]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def baseConstructorModifierArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          derivedBaseConstructorModifierGood ] }

def baseConstructorModifierArgsAccepted : Bool :=
  sourceUnitAccepted? baseConstructorModifierArgsSource

-- CL1: a bare modifier-style base-constructor call (`constructor() Base {}`,
-- no argument list) is a declaration error in solc (1563), while the
-- parenthesised form (`constructor() Base() {}`) is accepted. The two witnesses
-- differ ONLY in `hasArgList`, isolating the boundary.
def zeroParamBaseContract : Solidity.ContractDecl :=
  { name := "ZeroParamBase"
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            body := some Solidity.Stmt.empty } ] }

def bareModifierBaseCtorDerived : Solidity.ContractDecl :=
  { name := "BareModifierDerived"
    bases := [{ base := userPath "ZeroParamBase" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            modifiers :=
              [ { target := userPath "ZeroParamBase"
                  args := []
                  hasArgList := false } ]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def parenModifierBaseCtorDerived : Solidity.ContractDecl :=
  { name := "ParenModifierDerived"
    bases := [{ base := userPath "ZeroParamBase" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            modifiers :=
              [ { target := userPath "ZeroParamBase"
                  args := []
                  hasArgList := true } ]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def bareModifierBaseConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract zeroParamBaseContract
      , Solidity.SourceItem.contract bareModifierBaseCtorDerived ] }

def bareModifierBaseConstructorRejected : Bool :=
  Result.isError (SourceUnit.check bareModifierBaseConstructorSource)

def parenModifierBaseConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract zeroParamBaseContract
      , Solidity.SourceItem.contract parenModifierBaseCtorDerived ] }

def parenModifierBaseConstructorAccepted : Bool :=
  sourceUnitAccepted? parenModifierBaseConstructorSource

def derivedBaseConstructorDuplicate :
    Solidity.ContractDecl :=
  { derivedBaseConstructorModifierGood with
    name := "DuplicateCtorArgs"
    bases :=
      [{ base := userPath "CtorBase"
         args := [Solidity.Arg.positional (numberExpr "1")] }] }

def duplicateBaseConstructorArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          derivedBaseConstructorDuplicate ] }

def duplicateBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check duplicateBaseConstructorArgsSource)

-- ACCEPT-BOUNDARY (gap/accept-boundary): base-constructor arguments supplied
-- twice and eager brace-form using-for validation.  These pin the two
-- reject-fidelity fixes against solc 0.8.35.

-- DIV-DUP-INH-MOD #81, indirect variant: `A` has `constructor(uint)`, `B is
-- A(1)` supplies A's args in ITS inheritance list, and `C is B` then re-supplies
-- via a constructor modifier `A(2)`.  solc rejects ("Base constructor arguments
-- given twice."); the inheritance-supplied set must be gathered across the whole
-- linearization, not just the direct contract.
def accBndCtorBaseA : Solidity.ContractDecl :=
  { name := "AccBndCtorA"
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            params := [{ name := some "x", ty := uint256, location := none }]
            body := some Solidity.Stmt.empty } ] }

def accBndCtorBaseB : Solidity.ContractDecl :=
  { name := "AccBndCtorB"
    bases :=
      [{ base := userPath "AccBndCtorA"
         args := [Solidity.Arg.positional (numberExpr "1")] }]
    items := [] }

def accBndCtorDerivedIndirect : Solidity.ContractDecl :=
  { name := "AccBndCtorC"
    bases := [{ base := userPath "AccBndCtorB" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            modifiers :=
              [ { target := userPath "AccBndCtorA"
                  args := [Solidity.Arg.positional (numberExpr "2")] } ]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def accBndIndirectDoubleBaseCtorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract accBndCtorBaseA
      , Solidity.SourceItem.contract accBndCtorBaseB
      , Solidity.SourceItem.contract accBndCtorDerivedIndirect ] }

def accBndIndirectDoubleBaseCtorRejected : Bool :=
  Result.isError (SourceUnit.check accBndIndirectDoubleBaseCtorSource)

-- Single-supply control: args given ONLY in the inheritance list (`C is B(1)`
-- with a no-arg constructor) — solc and Lean both ACCEPT.
def accBndSingleSupplyDerived : Solidity.ContractDecl :=
  { name := "AccBndSingleC"
    bases :=
      [{ base := userPath "AccBndCtorA"
         args := [Solidity.Arg.positional (numberExpr "1")] }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def accBndSingleSupplySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract accBndCtorBaseA
      , Solidity.SourceItem.contract accBndSingleSupplyDerived ] }

def accBndSingleSupplyAccepted : Bool :=
  sourceUnitAccepted? accBndSingleSupplySource

-- USINGFOR-BRACE #82: a UDVT target for the brace-form using-for cases.
def accBndUdvt : Ty := Solidity.Ty.user (userPath "AccBndT")

def accBndUdvtItem : Solidity.SourceItem :=
  Solidity.SourceItem.freeUserValueType
    { name := "AccBndT", underlying := uint256 }

def accBndSurfaceContract : Solidity.ContractDecl :=
  { name := "AccBndSurface"
    items := [Solidity.ContractItem.function simpleReturnFunction] }

-- Non-attachable brace binding: `f(bool)` cannot be attached to a UDVT target.
-- solc rejects eagerly ("the function cannot be attached ... cannot be
-- implicitly converted to the first argument").
def accBndBoolFreeFunction : Solidity.FunctionDecl :=
  { name := some "accBndBoolF"
    params := [{ name := some "x", ty := Solidity.Ty.bool, location := none }]
    returns := [{ name := none, ty := Solidity.Ty.bool, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some (Solidity.Stmt.returnValues (some (Solidity.Expr.ident "x"))) }

def accBndBraceNonAttachableSource : Solidity.SourceUnit :=
  { items :=
      [ accBndUdvtItem
      , Solidity.SourceItem.freeFunction accBndBoolFreeFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions := [{ function := { segments := ["accBndBoolF"] } }]
            target := some accBndUdvt }
      , Solidity.SourceItem.contract accBndSurfaceContract ] }

def accBndBraceNonAttachableRejected : Bool :=
  Result.isError (SourceUnit.check accBndBraceNonAttachableSource)

-- Non-unique brace binding: two free `f` overloads make `{f}` ambiguous.
-- solc rejects ("Identifier is not a function name or not unique.").
def accBndUdvtFreeFunction : Solidity.FunctionDecl :=
  { name := some "accBndF"
    params := [{ name := some "a", ty := accBndUdvt, location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    mutability := Solidity.StateMutability.pure
    body := some (Solidity.Stmt.returnValues (some (numberExpr "1"))) }

def accBndBoolOverloadFreeFunction : Solidity.FunctionDecl :=
  { accBndBoolFreeFunction with name := some "accBndF" }

def accBndBraceNonUniqueSource : Solidity.SourceUnit :=
  { items :=
      [ accBndUdvtItem
      , Solidity.SourceItem.freeFunction accBndUdvtFreeFunction
      , Solidity.SourceItem.freeFunction accBndBoolOverloadFreeFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions := [{ function := { segments := ["accBndF"] } }]
            target := some accBndUdvt }
      , Solidity.SourceItem.contract accBndSurfaceContract ] }

def accBndBraceNonUniqueRejected : Bool :=
  Result.isError (SourceUnit.check accBndBraceNonUniqueSource)

-- Attachable + unique brace binding: `f(AccBndT)` — solc and Lean ACCEPT.
def accBndBraceAttachableSource : Solidity.SourceUnit :=
  { items :=
      [ accBndUdvtItem
      , Solidity.SourceItem.freeFunction accBndUdvtFreeFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions := [{ function := { segments := ["accBndF"] } }]
            target := some accBndUdvt }
      , Solidity.SourceItem.contract accBndSurfaceContract ] }

def accBndBraceAttachableAccepted : Bool :=
  sourceUnitAccepted? accBndBraceAttachableSource

-- Library-form using-for is validated LAZILY: an unused library function whose
-- self type does not match the target is accepted by BOTH solc and Lean.  This
-- guards that the eager fix touches ONLY the brace form.
def accBndUnusedLibrary : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "AccBndLib"
    items :=
      [ Solidity.ContractItem.function
          { accBndBoolFreeFunction with
            name := some "libBool"
            visibility := some Solidity.Visibility.internal_ } ] }

def accBndUnusedLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ accBndUdvtItem
      , Solidity.SourceItem.contract accBndUnusedLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "AccBndLib"
            target := some accBndUdvt }
      , Solidity.SourceItem.contract accBndSurfaceContract ] }

def accBndUnusedLibraryAccepted : Bool :=
  sourceUnitAccepted? accBndUnusedLibrarySource

-- Combined discipline: both reject-fidelity fixes and their accept controls.
def acceptBoundaryDisciplineMatches : Bool :=
  -- DIV-DUP-INH-MOD #81
  duplicateBaseConstructorArgsRejected &&
    accBndIndirectDoubleBaseCtorRejected &&
    accBndSingleSupplyAccepted &&
    -- USINGFOR-BRACE #82
    accBndBraceNonAttachableRejected &&
    accBndBraceNonUniqueRejected &&
    accBndBraceAttachableAccepted &&
    accBndUnusedLibraryAccepted

def abstractMissingBaseConstructorArgs :
    Solidity.ContractDecl :=
  { name := "AbstractMissingCtorArgs"
    abstract := true
    bases := [{ base := userPath "CtorBase" }]
    items := [] }

def abstractMissingBaseConstructorArgsSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          abstractMissingBaseConstructorArgs ] }

def abstractMissingBaseConstructorArgsAccepted : Bool :=
  sourceUnitAccepted? abstractMissingBaseConstructorArgsSource

def concreteMissingBaseConstructorArgs :
    Solidity.ContractDecl :=
  { abstractMissingBaseConstructorArgs with
    name := "ConcreteMissingCtorArgs"
    abstract := false }

def concreteMissingBaseConstructorArgsSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          concreteMissingBaseConstructorArgs ] }

def concreteMissingBaseConstructorArgsRejected : Bool :=
  Result.isError (SourceUnit.check concreteMissingBaseConstructorArgsSource)

def concreteSuppliesIndirectBaseConstructorArgs :
    Solidity.ContractDecl :=
  { name := "ConcreteSuppliesIndirectCtorArgs"
    bases := [{ base := userPath "AbstractMissingCtorArgs" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            params := []
            modifiers :=
              [ { target := userPath "CtorBase"
                  args :=
                    [ Solidity.Arg.positional
                        (numberExpr "10") ] } ]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def indirectBaseConstructorModifierArgsSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          abstractMissingBaseConstructorArgs
      , Solidity.SourceItem.contract
          concreteSuppliesIndirectBaseConstructorArgs ] }

def indirectBaseConstructorModifierArgsAccepted : Bool :=
  sourceUnitAccepted? indirectBaseConstructorModifierArgsSource

def nonconstructorBaseConstructorInvocation :
    Solidity.ContractDecl :=
  { name := "NonconstructorBaseInvocation"
    bases :=
      [{ base := userPath "CtorBase"
         args := [Solidity.Arg.positional (numberExpr "1")] }]
    items :=
      [ Solidity.ContractItem.function
          { simpleReturnFunction with
            modifiers :=
              [ { target := userPath "CtorBase"
                  args := [Solidity.Arg.positional
                    (numberExpr "2")] } ] } ] }

def nonconstructorBaseConstructorInvocationSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseConstructorContract
      , Solidity.SourceItem.contract
          nonconstructorBaseConstructorInvocation ] }

def nonconstructorBaseConstructorInvocationRejected : Bool :=
  Result.isError
    (SourceUnit.check nonconstructorBaseConstructorInvocationSource)

def newStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pairStruct
      , Solidity.SourceItem.contract
          { name := "NewStruct"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badNewStruct"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.newExpr pairTy
                                [ Solidity.Arg.positional
                                    (numberExpr "1")
                                , Solidity.Arg.positional
                                    (numberExpr "2") ])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def newStructRejected : Bool :=
  Result.isError (SourceUnit.check newStructSource)

def payableReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "payMe"
    mutability := Solidity.StateMutability.payable }

def payableValueCaller : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callPayable"
    mutability := Solidity.StateMutability.payable
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.callWithOptions
              (Solidity.Expr.ident "payMe")
              [valueOption "1"] []))) }

def payableValueCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableValueCall"
            items :=
              [ Solidity.ContractItem.function payableReturnFunction
              , Solidity.ContractItem.function payableValueCaller ] } ] }

def payableInternalValueCallRejected : Bool :=
  Result.isError (SourceUnit.check payableValueCallSource)

def nonpayableValueCaller : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callNonpayable"
    mutability := Solidity.StateMutability.payable
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.callWithOptions
              (Solidity.Expr.ident "f")
              [valueOption "1"] []))) }

def nonpayableValueCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonpayableValueCall"
            items :=
              [ Solidity.ContractItem.function simpleReturnFunction
              , Solidity.ContractItem.function
                  nonpayableValueCaller ] } ] }

def nonpayableValueCallRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableValueCallSource)

def pingEvent : Solidity.EventDecl :=
  { name := "Ping"
    params := [{ name := some "value", ty := uint256, indexed := false }] }

def boomError : Solidity.ErrorDecl :=
  { name := "Boom"
    params :=
      [{ name := some "value", ty := uint256, location := none }] }

def reservedErrorDecl : Solidity.ErrorDecl :=
  { name := "Error"
    params :=
      [ { name := some "reason"
          ty := Solidity.Ty.string
          location := none } ] }

def reservedErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ReservedError"
            items :=
              [Solidity.ContractItem.errorDecl
                reservedErrorDecl] } ] }

def reservedErrorRejected : Bool :=
  Result.isError (SourceUnit.check reservedErrorSource)

def reservedPanicSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ReservedPanic"
            items :=
              [ Solidity.ContractItem.errorDecl
                  { name := "Panic"
                    params :=
                      [ { name := some "code"
                          ty := uint256
                          location := none } ] } ] } ] }

def reservedPanicRejected : Bool :=
  Result.isError (SourceUnit.check reservedPanicSource)

def duplicateErrorParamNameSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError
          { name := "DuplicateErrorParam"
            params :=
              [ { name := some "value"
                  ty := uint256
                  location := none }
              , { name := some "value"
                  ty := uint256
                  location := none } ] } ] }

def duplicateErrorParamNameRejected : Bool :=
  Result.isError (SourceUnit.check duplicateErrorParamNameSource)

def emitPingFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emitPing"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.emitEvent
              (Solidity.Expr.call
                (Solidity.Expr.ident "Ping")
                [Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "1"))])
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "1"))) ]) }

def emitPingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EmitPing"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.function emitPingFunction ] } ] }

def emitPingAccepted : Bool :=
  sourceUnitAccepted? emitPingSource

def freeEventEmitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.contract
          { name := "EmitFreePing"
            items :=
              [Solidity.ContractItem.function emitPingFunction] } ] }

def freeEventEmitAccepted : Bool :=
  sourceUnitAccepted? freeEventEmitSource

def eventSelectorFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "selector"
    returns :=
      [{ name := some "out"
         ty := Solidity.Ty.bytesN 32
         location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "Ping")
              "selector"))) }

def eventSelectorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EventSelector"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.function
                  eventSelectorFunction ] } ] }

def eventSelectorAccepted : Bool :=
  sourceUnitAccepted? eventSelectorSource

def freeEventSelectorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.contract
          { name := "FreeEventSelector"
            items :=
              [Solidity.ContractItem.function
                eventSelectorFunction] } ] }

def freeEventSelectorAccepted : Bool :=
  sourceUnitAccepted? freeEventSelectorSource

def overloadedAddressPingEvent : Solidity.EventDecl :=
  { name := "Ping"
    params :=
      [ { name := some "value"
          ty := Solidity.Ty.address false
          indexed := false } ] }

def overloadedEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "OverloadedEvents"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.eventDecl
                  overloadedAddressPingEvent ] } ] }

def overloadedEventAccepted : Bool :=
  sourceUnitAccepted? overloadedEventSource

def overloadedEventSelectorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "OverloadedEventSelector"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.eventDecl
                  overloadedAddressPingEvent
              , Solidity.ContractItem.function
                  eventSelectorFunction ] } ] }

def overloadedEventSelectorRejected : Bool :=
  Result.isError (SourceUnit.check overloadedEventSelectorSource)

def duplicateCanonicalPingEvent : Solidity.EventDecl :=
  { name := "Ping"
    params := [{ name := some "other", ty := uint256, indexed := false }] }

def duplicateEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateEvent"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.eventDecl
                  duplicateCanonicalPingEvent ] } ] }

def duplicateEventRejected : Bool :=
  Result.isError (SourceUnit.check duplicateEventSource)

def duplicateFreeEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.freeEvent duplicateCanonicalPingEvent ] }

def duplicateFreeEventRejected : Bool :=
  Result.isError (SourceUnit.check duplicateFreeEventSource)

def freeAndContractSameEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.contract
          { name := "ContractEventShadowsFree"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.function emitPingFunction ] } ] }

def freeAndContractSameEventAccepted : Bool :=
  sourceUnitAccepted? freeAndContractSameEventSource

def addressPingEvent : Solidity.EventDecl :=
  { name := "Ping"
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address false
          indexed := false } ] }

def emitPingAddressFunction : Solidity.FunctionDecl :=
  { emitPingFunction with
    body :=
      some
        (Solidity.Stmt.emitEvent
          (Solidity.Expr.call
            (Solidity.Expr.ident "Ping")
            [ Solidity.Arg.positional
                (Solidity.Expr.call
                  (Solidity.Expr.typeName
                    (Solidity.Ty.address false))
                  [Solidity.Arg.positional (numberExpr "0")]) ])) }

def freeAndContractEventNameShadowAcceptedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.contract
          { name := "ContractEventNameShadowsFree"
            items :=
              [ Solidity.ContractItem.eventDecl addressPingEvent
              , Solidity.ContractItem.function
                  emitPingAddressFunction ] } ] }

def freeAndContractEventNameShadowAccepted : Bool :=
  sourceUnitAccepted? freeAndContractEventNameShadowAcceptedSource

def freeAndContractEventNameShadowRejectsFreeMatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.contract
          { name := "ContractEventNameShadowRejectsFreeMatch"
            items :=
              [ Solidity.ContractItem.eventDecl addressPingEvent
              , Solidity.ContractItem.function emitPingFunction ] } ] }

def freeAndContractEventNameShadowRejectsFreeMatch : Bool :=
  Result.isError
    (SourceUnit.check freeAndContractEventNameShadowRejectsFreeMatchSource)

def freeEventFunctionNameCollisionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent pingEvent
      , Solidity.SourceItem.freeFunction
          { simpleReturnFunction with
            name := some "Ping"
            visibility := none } ] }

def freeEventFunctionNameCollisionRejected : Bool :=
  Result.isError (SourceUnit.check freeEventFunctionNameCollisionSource)

def duplicateEventParamNameSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateEventParamName"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Seen"
                    params :=
                      [ { name := some "value"
                          ty := uint256
                          indexed := false }
                      , { name := some "value"
                          ty := uint256
                          indexed := false } ] } ] } ] }

def duplicateEventParamNameRejected : Bool :=
  Result.isError (SourceUnit.check duplicateEventParamNameSource)

def indexedPingEvent : Solidity.EventDecl :=
  { name := "Ping"
    params :=
      [{ name := some "value"
         ty := uint256
         indexed := true }] }

def eventIndexedOnlyDuplicateSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EventIndexedOnlyDuplicate"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.eventDecl
                  indexedPingEvent ] } ] }

def eventIndexedOnlyDuplicateRejected : Bool :=
  Result.isError (SourceUnit.check eventIndexedOnlyDuplicateSource)

def declarationSignatureIdentityDisciplineMatches : Bool :=
  overloadedEventAccepted &&
    duplicateEventRejected &&
    duplicateFreeEventRejected &&
    duplicateEventParamNameRejected &&
    eventIndexedOnlyDuplicateRejected &&
    freeErrorOverloadRejected &&
    contractErrorOverloadRejected &&
    modifierOverloadRejected

def mappingEventParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadMappingEventParam"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Bad"
                    params :=
                      [ { name := some "values"
                          ty :=
                            Solidity.Ty.mapping
                              uint256 uint256
                          indexed := true } ] } ] } ] }

def mappingEventParamRejected : Bool :=
  Result.isError (SourceUnit.check mappingEventParamSource)

def freeMappingEventParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEvent
          { name := "Bad"
            params :=
              [ { name := some "values"
                  ty := Solidity.Ty.mapping uint256 uint256
                  indexed := true } ] } ] }

def freeMappingEventParamRejected : Bool :=
  Result.isError (SourceUnit.check freeMappingEventParamSource)

def internalFunctionEventParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadInternalFunctionEventParam"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Bad"
                    params :=
                      [ { name := some "fn"
                          ty :=
                            Solidity.Ty.function
                              [uint256] []
                              Solidity.StateMutability.pure
                              Solidity.Visibility.internal_
                          indexed := false } ] } ] } ] }

def internalFunctionEventParamRejected : Bool :=
  Result.isError (SourceUnit.check internalFunctionEventParamSource)

def externalFunctionEventParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalFunctionEventParam"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { name := "Good"
                    params :=
                      [ { name := some "fn"
                          ty :=
                            Solidity.Ty.function
                              [uint256] []
                              Solidity.StateMutability.nonpayable
                              Solidity.Visibility.external_
                          indexed := false } ] } ] } ] }

def externalFunctionEventParamAccepted : Bool :=
  sourceUnitAccepted? externalFunctionEventParamSource

def indexedUintEventParam (name : Name) : Solidity.EventParam :=
  { name := some name, ty := uint256, indexed := true }

def threeIndexedEvent : Solidity.EventDecl :=
  { name := "ThreeIndexed"
    params :=
      [ indexedUintEventParam "a"
      , indexedUintEventParam "b"
      , indexedUintEventParam "c" ] }

def threeIndexedEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ThreeIndexedEvent"
            items := [Solidity.ContractItem.eventDecl
              threeIndexedEvent] } ] }

def threeIndexedEventAccepted : Bool :=
  sourceUnitAccepted? threeIndexedEventSource

def fourIndexedEvent : Solidity.EventDecl :=
  { name := "FourIndexed"
    params :=
      [ indexedUintEventParam "a"
      , indexedUintEventParam "b"
      , indexedUintEventParam "c"
      , indexedUintEventParam "d" ] }

def fourIndexedEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FourIndexedEvent"
            items := [Solidity.ContractItem.eventDecl
              fourIndexedEvent] } ] }

def fourIndexedEventRejected : Bool :=
  Result.isError (SourceUnit.check fourIndexedEventSource)

def anonymousFourIndexedEvent : Solidity.EventDecl :=
  { fourIndexedEvent with name := "AnonymousFourIndexed", anonymous := true }

def anonymousFourIndexedEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AnonymousFourIndexedEvent"
            items := [Solidity.ContractItem.eventDecl
              anonymousFourIndexedEvent] } ] }

def anonymousFourIndexedEventAccepted : Bool :=
  sourceUnitAccepted? anonymousFourIndexedEventSource

def anonymousEventSelectorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AnonymousEventSelector"
            items :=
              [ Solidity.ContractItem.eventDecl
                  { pingEvent with anonymous := true }
              , Solidity.ContractItem.function
                  eventSelectorFunction ] } ] }

def anonymousEventSelectorRejected : Bool :=
  Result.isError (SourceUnit.check anonymousEventSelectorSource)

def unknownEventSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnknownEvent"
            items := [Solidity.ContractItem.function
              emitPingFunction] } ] }

def unknownEventRejected : Bool :=
  Result.isError (SourceUnit.check unknownEventSource)

def eventStaticDisciplineMatches : Bool :=
  mappingEventParamRejected &&
    freeMappingEventParamRejected &&
    internalFunctionEventParamRejected &&
    externalFunctionEventParamAccepted &&
    threeIndexedEventAccepted &&
    fourIndexedEventRejected &&
    anonymousFourIndexedEventAccepted &&
    anonymousEventSelectorRejected &&
    unknownEventRejected

def revertBoomFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertBoom"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "Boom")
                [Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "1"))])
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "1"))) ]) }

def revertBoomSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError boomError
      , Solidity.SourceItem.contract
          { name := "RevertBoom"
            items := [Solidity.ContractItem.function
              revertBoomFunction] } ] }

def revertBoomAccepted : Bool :=
  sourceUnitAccepted? revertBoomSource

def addressBoomError : Solidity.ErrorDecl :=
  { name := "Boom"
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address false
          location := none } ] }

def revertAddressBoomFunction : Solidity.FunctionDecl :=
  { revertBoomFunction with
    body :=
      some
        (Solidity.Stmt.revertCall
          (Solidity.Expr.call
            (Solidity.Expr.ident "Boom")
            [ Solidity.Arg.positional
                (Solidity.Expr.call
                  (Solidity.Expr.typeName
                    (Solidity.Ty.address false))
                  [Solidity.Arg.positional (numberExpr "0")]) ])) }

def freeAndContractSameErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError boomError
      , Solidity.SourceItem.contract
          { name := "ContractErrorShadowsFree"
            items :=
              [ Solidity.ContractItem.errorDecl boomError
              , Solidity.ContractItem.function
                  revertBoomFunction ] } ] }

def freeAndContractSameErrorAccepted : Bool :=
  sourceUnitAccepted? freeAndContractSameErrorSource

def freeAndContractErrorNameShadowAcceptedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError boomError
      , Solidity.SourceItem.contract
          { name := "ContractErrorNameShadowsFree"
            items :=
              [ Solidity.ContractItem.errorDecl addressBoomError
              , Solidity.ContractItem.function
                  revertAddressBoomFunction ] } ] }

def freeAndContractErrorNameShadowAccepted : Bool :=
  sourceUnitAccepted? freeAndContractErrorNameShadowAcceptedSource

def freeAndContractErrorNameShadowRejectsFreeMatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError boomError
      , Solidity.SourceItem.contract
          { name := "ContractErrorNameShadowRejectsFreeMatch"
            items :=
              [ Solidity.ContractItem.errorDecl addressBoomError
              , Solidity.ContractItem.function
                  revertBoomFunction ] } ] }

def freeAndContractErrorNameShadowRejectsFreeMatch : Bool :=
  Result.isError
    (SourceUnit.check freeAndContractErrorNameShadowRejectsFreeMatchSource)

def unknownErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnknownError"
            items := [Solidity.ContractItem.function
              revertBoomFunction] } ] }

def unknownErrorRejected : Bool :=
  Result.isError (SourceUnit.check unknownErrorSource)

def stringError : Solidity.ErrorDecl :=
  { name := "StringBoom"
    params :=
      [{ name := some "reason"
         ty := Solidity.Ty.string
         location := none }] }

def revertStringErrorFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertStringBoom"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "StringBoom")
                [Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.string "bad"))])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def revertStringErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError stringError
      , Solidity.SourceItem.contract
          { name := "RevertStringBoom"
            items := [Solidity.ContractItem.function
              revertStringErrorFunction] } ] }

def revertStringErrorAccepted : Bool :=
  sourceUnitAccepted? revertStringErrorSource

def pairNamedEvent : Solidity.EventDecl :=
  { name := "PairSeen"
    params :=
      [ { name := some "left", ty := uint256, indexed := false }
      , { name := some "right", ty := uint256, indexed := false } ] }

def emitPairNamedFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emitPairNamed"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.emitEvent
              (Solidity.Expr.call
                (Solidity.Expr.ident "PairSeen")
                [ Solidity.Arg.named "right" (numberExpr "2")
                , Solidity.Arg.named "left" (numberExpr "40") ])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def emitPairNamedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EmitPairNamed"
            items :=
              [ Solidity.ContractItem.eventDecl pairNamedEvent
              , Solidity.ContractItem.function
                  emitPairNamedFunction ] } ] }

def emitPairNamedAccepted : Bool :=
  sourceUnitAccepted? emitPairNamedSource

def pairNamedError : Solidity.ErrorDecl :=
  { name := "PairBad"
    params :=
      [ { name := some "left", ty := uint256, location := none }
      , { name := some "right", ty := uint256, location := none } ] }

def revertPairNamedFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertPairNamed"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "PairBad")
                [ Solidity.Arg.named "right" (numberExpr "2")
                , Solidity.Arg.named "left" (numberExpr "40") ])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def revertPairNamedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError pairNamedError
      , Solidity.SourceItem.contract
          { name := "RevertPairNamed"
            items := [Solidity.ContractItem.function
              revertPairNamedFunction] } ] }

def revertPairNamedAccepted : Bool :=
  sourceUnitAccepted? revertPairNamedSource

def requirePairNamedFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "requirePairNamed"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.call
                (Solidity.Expr.ident "require")
                [ Solidity.Arg.positional (boolExpr false)
                , Solidity.Arg.positional
                    (Solidity.Expr.call
                      (Solidity.Expr.ident "PairBad")
                      [ Solidity.Arg.named "right" (numberExpr "2")
                      , Solidity.Arg.named "left"
                          (numberExpr "40") ]) ])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def requirePairNamedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError pairNamedError
      , Solidity.SourceItem.contract
          { name := "RequirePairNamed"
            items := [Solidity.ContractItem.function
              requirePairNamedFunction] } ] }

def requirePairNamedAccepted : Bool :=
  sourceUnitAccepted? requirePairNamedSource

def stringErrorWithLocationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeError
          { stringError with
            params :=
              [ { name := some "reason"
                  ty := Solidity.Ty.string
                  location :=
                    some Solidity.DataLocation.memory } ] } ] }

def stringErrorWithLocationRejected : Bool :=
  Result.isError (SourceUnit.check stringErrorWithLocationSource)

def customErrorStaticDisciplineMatches : Bool :=
  revertBoomAccepted &&
    freeAndContractSameErrorAccepted &&
    freeAndContractErrorNameShadowAccepted &&
    freeAndContractErrorNameShadowRejectsFreeMatch &&
    unknownErrorRejected &&
    revertStringErrorAccepted &&
    revertPairNamedAccepted &&
    requirePairNamedAccepted &&
    stringErrorWithLocationRejected &&
    reservedErrorRejected &&
    reservedPanicRejected &&
    duplicateErrorParamNameRejected &&
    freeErrorOverloadRejected &&
    contractErrorOverloadRejected

def pointModifier
    (location : Option Solidity.DataLocation) :
    Solidity.ModifierDecl :=
  { name := "withPoint"
    params :=
      [ { name := some "point"
          ty := pointTy
          location := location } ]
    body := some Solidity.Stmt.modifierPlaceholder }

def modifierLocationSource
    (contractName : Name)
    (modifier : Solidity.ModifierDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct pointStruct
      , Solidity.SourceItem.contract
          { name := contractName
            items := [Solidity.ContractItem.modifierDecl
              modifier] } ] }

def modifierStorageParamSource : Solidity.SourceUnit :=
  modifierLocationSource "ModifierStorageParam"
    (pointModifier (some Solidity.DataLocation.storage))

def modifierStorageParamAccepted : Bool :=
  sourceUnitAccepted? modifierStorageParamSource

def modifierMemoryParamSource : Solidity.SourceUnit :=
  modifierLocationSource "ModifierMemoryParam"
    (pointModifier (some Solidity.DataLocation.memory))

def modifierMemoryParamAccepted : Bool :=
  sourceUnitAccepted? modifierMemoryParamSource

def modifierCalldataParamSource : Solidity.SourceUnit :=
  modifierLocationSource "ModifierCalldataParam"
    (pointModifier (some Solidity.DataLocation.calldata))

def modifierCalldataParamAccepted : Bool :=
  sourceUnitAccepted? modifierCalldataParamSource

def modifierMissingLocationSource : Solidity.SourceUnit :=
  modifierLocationSource "ModifierMissingLocation" (pointModifier none)

def modifierMissingLocationRejected : Bool :=
  Result.isError (SourceUnit.check modifierMissingLocationSource)

def modifierValueMemoryParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierValueMemoryParam"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { name := "withValue"
                    params :=
                      [ { name := some "value"
                          ty := uint256
                          location :=
                            some
                              Solidity.DataLocation.memory } ]
                    body :=
                      some
                        Solidity.Stmt.modifierPlaceholder } ] } ] }

def modifierValueMemoryParamRejected : Bool :=
  Result.isError (SourceUnit.check modifierValueMemoryParamSource)

def modifierDataLocationDisciplineMatches : Bool :=
  modifierStorageParamAccepted &&
    modifierMemoryParamAccepted &&
    modifierCalldataParamAccepted &&
    modifierMissingLocationRejected &&
    modifierValueMemoryParamRejected

def externallyVisibleStorageParamSource
    (contractName : Name) (visibility : Solidity.Visibility) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "bad"
                    params :=
                      [ { name := some "values"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.storage } ]
                    visibility := some visibility
                    mutability := Solidity.StateMutability.view } ] } ] }

def externallyVisibleStorageReturnSource
    (contractName : Name) (visibility : Solidity.Visibility) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "values", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "bad"
                    returns :=
                      [ { name := some "result"
                          ty := uintArrayTy
                          location :=
                            some
                              Solidity.DataLocation.storage } ]
                    visibility := some visibility
                    mutability := Solidity.StateMutability.view } ] } ] }

def externalStorageParamRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (externallyVisibleStorageParamSource "ExternalStorageParam"
        Solidity.Visibility.external_))

def externalStorageReturnRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (externallyVisibleStorageReturnSource "ExternalStorageReturn"
        Solidity.Visibility.external_))

def publicStorageReturnRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (externallyVisibleStorageReturnSource "PublicStorageReturn"
        Solidity.Visibility.public_))

def declarationDataLocationDisciplineMatches : Bool :=
  missingStructLocationRejected &&
    missingStructReturnLocationRejected &&
    valueTypeMemoryParamRejected &&
    stringErrorWithLocationRejected &&
    externalStorageParamRejected &&
    publicStorageParamRejected &&
    externalStorageReturnRejected &&
    publicStorageReturnRejected &&
    constructorDataLocationDisciplineMatches &&
    modifierDataLocationDisciplineMatches

def namedTargetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "target"
    params :=
      [ { name := some "a", ty := uint256, location := none }
      , { name := some "flag"
          ty := Solidity.Ty.bool
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "a"))) }

def namedCallerFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callNamed"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "target")
              [ Solidity.Arg.named "flag"
                  (Solidity.Expr.literal
                    (Solidity.Literal.bool true))
              , Solidity.Arg.named "a"
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "3")) ]))) }

def namedArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NamedArgs"
            items :=
              [ Solidity.ContractItem.function namedTargetFunction
              , Solidity.ContractItem.function
                  namedCallerFunction ] } ] }

def namedArgsAccepted : Bool :=
  sourceUnitAccepted? namedArgsSource

def badNamedCallerFunction : Solidity.FunctionDecl :=
  { namedCallerFunction with
    name := some "badNamed"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "target")
              [ Solidity.Arg.named "missing"
                  (Solidity.Expr.literal
                    (Solidity.Literal.bool true))
              , Solidity.Arg.named "a"
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "3")) ]))) }

def badNamedArgsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadNamedArgs"
            items :=
              [ Solidity.ContractItem.function namedTargetFunction
              , Solidity.ContractItem.function
                  badNamedCallerFunction ] } ] }

def badNamedArgsRejected : Bool :=
  Result.isError (SourceUnit.check badNamedArgsSource)

def interfaceFunctionDecl : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "read"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view
    body := none }

def interfaceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IReader"
            items := [Solidity.ContractItem.function
              interfaceFunctionDecl] } ] }

def interfaceAccepted : Bool :=
  sourceUnitAccepted? interfaceSource

def interfaceFallbackDecl : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.fallback
    name := none
    params := []
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body := none }

def interfaceFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IFallback"
            items := [Solidity.ContractItem.function
              interfaceFallbackDecl] } ] }

def interfaceFallbackAccepted : Bool :=
  sourceUnitAccepted? interfaceFallbackSource

def interfaceReceiveDecl : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.receive
    name := none
    params := []
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.payable
    body := none }

def interfaceReceiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IReceive"
            items := [Solidity.ContractItem.function
              interfaceReceiveDecl] } ] }

def interfaceReceiveAccepted : Bool :=
  sourceUnitAccepted? interfaceReceiveSource

def interfaceTypedFallbackDecl : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.fallback
    name := none
    params :=
      [ { name := some "input"
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.calldata } ]
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body := none }

def interfaceTypedFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "ITypedFallback"
            items := [Solidity.ContractItem.function
              interfaceTypedFallbackDecl] } ] }

def interfaceTypedFallbackAccepted : Bool :=
  sourceUnitAccepted? interfaceTypedFallbackSource

def badInterfaceBodySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IBad"
            items :=
              [ Solidity.ContractItem.function
                  { interfaceFunctionDecl with
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.literal
                              (Solidity.Literal.number "1")))) } ] } ] }

def badInterfaceBodyRejected : Bool :=
  Result.isError (SourceUnit.check badInterfaceBodySource)

def badInterfaceFallbackBodySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IBadFallbackBody"
            items :=
              [ Solidity.ContractItem.function
                  { interfaceFallbackDecl with
                    body := some Solidity.Stmt.empty } ] } ] }

def badInterfaceFallbackBodyRejected : Bool :=
  Result.isError (SourceUnit.check badInterfaceFallbackBodySource)

def interfaceConstructorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IConstructor"
            items :=
              [ Solidity.ContractItem.function
                  { kind := Solidity.FunctionKind.constructor
                    name := none
                    params := []
                    returns := []
                    visibility := none
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body := none } ] } ] }

def interfaceConstructorRejected : Bool :=
  Result.isError (SourceUnit.check interfaceConstructorSource)

def abstractInterfaceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IAbstract"
            abstract := true
            items := [Solidity.ContractItem.function
              interfaceFunctionDecl] } ] }

def abstractInterfaceRejected : Bool :=
  Result.isError (SourceUnit.check abstractInterfaceSource)

def unimplementedFunctionDecl : Solidity.FunctionDecl :=
  { simpleReturnFunction with body := none, virtual := true }

def nonAbstractMissingBodySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MissingImpl"
            items := [Solidity.ContractItem.function
              unimplementedFunctionDecl] } ] }

def nonAbstractMissingBodyRejected : Bool :=
  Result.isError (SourceUnit.check nonAbstractMissingBodySource)

def abstractMissingBodySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractMissingImpl"
            abstract := true
            items := [Solidity.ContractItem.function
              unimplementedFunctionDecl] } ] }

def abstractMissingBodyAccepted : Bool :=
  sourceUnitAccepted? abstractMissingBodySource

def inheritedAbstractFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractFunctionBase"
            abstract := true
            items := [Solidity.ContractItem.function
              unimplementedFunctionDecl] }
      , Solidity.SourceItem.contract
          { name := "InheritsAbstractFunction"
            bases := [{ base := userPath "AbstractFunctionBase" }] } ] }

def inheritedAbstractFunctionRejected : Bool :=
  Result.isError (SourceUnit.check inheritedAbstractFunctionSource)

def abstractInheritsAbstractFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractFunctionBase2"
            abstract := true
            items := [Solidity.ContractItem.function
              unimplementedFunctionDecl] }
      , Solidity.SourceItem.contract
          { name := "AbstractInheritsAbstractFunction"
            abstract := true
            bases := [{ base := userPath "AbstractFunctionBase2" }] } ] }

def abstractInheritsAbstractFunctionAccepted : Bool :=
  sourceUnitAccepted? abstractInheritsAbstractFunctionSource

def inheritedInterfaceFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IInheritedReader"
            items := [Solidity.ContractItem.function
              interfaceFunctionDecl] }
      , Solidity.SourceItem.contract
          { name := "InheritsInterfaceFunction"
            bases := [{ base := userPath "IInheritedReader" }] } ] }

def inheritedInterfaceFunctionRejected : Bool :=
  Result.isError (SourceUnit.check inheritedInterfaceFunctionSource)

def implementedInterfaceFunction : Solidity.FunctionDecl :=
  { interfaceFunctionDecl with
    body := some (Solidity.Stmt.returnValues
      (some (numberExpr "1"))) }

def implementedInterfaceFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IImplementedReader"
            items := [Solidity.ContractItem.function
              interfaceFunctionDecl] }
      , Solidity.SourceItem.contract
          { name := "ImplementsInterfaceFunction"
            bases := [{ base := userPath "IImplementedReader" }]
            items := [Solidity.ContractItem.function
              implementedInterfaceFunction] } ] }

def implementedInterfaceFunctionAccepted : Bool :=
  sourceUnitAccepted? implementedInterfaceFunctionSource

def inheritedInterfaceFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IInheritedFallback"
            items := [Solidity.ContractItem.function
              interfaceFallbackDecl] }
      , Solidity.SourceItem.contract
          { name := "InheritsInterfaceFallback"
            bases := [{ base := userPath "IInheritedFallback" }] } ] }

def inheritedInterfaceFallbackRejected : Bool :=
  Result.isError (SourceUnit.check inheritedInterfaceFallbackSource)

def implementedInterfaceFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IImplementedFallback"
            items := [Solidity.ContractItem.function
              interfaceFallbackDecl] }
      , Solidity.SourceItem.contract
          { name := "ImplementsInterfaceFallback"
            bases := [{ base := userPath "IImplementedFallback" }]
            items :=
              [ Solidity.ContractItem.function
                  { interfaceFallbackDecl with
                    body := some Solidity.Stmt.empty } ] } ] }

def implementedInterfaceFallbackAccepted : Bool :=
  sourceUnitAccepted? implementedInterfaceFallbackSource

def inheritedInterfaceReceiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IInheritedReceive"
            items := [Solidity.ContractItem.function
              interfaceReceiveDecl] }
      , Solidity.SourceItem.contract
          { name := "InheritsInterfaceReceive"
            bases := [{ base := userPath "IInheritedReceive" }] } ] }

def inheritedInterfaceReceiveRejected : Bool :=
  Result.isError (SourceUnit.check inheritedInterfaceReceiveSource)

def implementedInterfaceReceiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IImplementedReceive"
            items := [Solidity.ContractItem.function
              interfaceReceiveDecl] }
      , Solidity.SourceItem.contract
          { name := "ImplementsInterfaceReceive"
            bases := [{ base := userPath "IImplementedReceive" }]
            items :=
              [ Solidity.ContractItem.function
                  { interfaceReceiveDecl with
                    body := some Solidity.Stmt.empty } ] } ] }

def implementedInterfaceReceiveAccepted : Bool :=
  sourceUnitAccepted? implementedInterfaceReceiveSource

def bodylessVirtualModifier : Solidity.ModifierDecl :=
  { name := "guard"
    virtual := true
    body := none }

def abstractBodylessModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractBodylessModifier"
            abstract := true
            items := [Solidity.ContractItem.modifierDecl
              bodylessVirtualModifier] } ] }

def abstractBodylessModifierAccepted : Bool :=
  sourceUnitAccepted? abstractBodylessModifierSource

def abstractBodylessModifierNoVirtualSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractBodylessModifierNoVirtual"
            abstract := true
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { bodylessVirtualModifier with virtual := false } ] } ] }

def abstractBodylessModifierNoVirtualRejected : Bool :=
  Result.isError (SourceUnit.check
    abstractBodylessModifierNoVirtualSource)

def nonAbstractBodylessModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonAbstractBodylessModifier"
            items := [Solidity.ContractItem.modifierDecl
              bodylessVirtualModifier] } ] }

def nonAbstractBodylessModifierRejected : Bool :=
  Result.isError (SourceUnit.check nonAbstractBodylessModifierSource)

def inheritedAbstractModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractModifierBase"
            abstract := true
            items := [Solidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , Solidity.SourceItem.contract
          { name := "InheritsAbstractModifier"
            bases := [{ base := userPath "AbstractModifierBase" }] } ] }

def inheritedAbstractModifierRejected : Bool :=
  Result.isError (SourceUnit.check inheritedAbstractModifierSource)

def abstractInheritsAbstractModifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractModifierBase2"
            abstract := true
            items := [Solidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , Solidity.SourceItem.contract
          { name := "AbstractInheritsAbstractModifier"
            abstract := true
            bases := [{ base := userPath "AbstractModifierBase2" }] } ] }

def abstractInheritsAbstractModifierAccepted : Bool :=
  sourceUnitAccepted? abstractInheritsAbstractModifierSource

def implementedAbstractModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractModifierBase3"
            abstract := true
            items := [Solidity.ContractItem.modifierDecl
              bodylessVirtualModifier] }
      , Solidity.SourceItem.contract
          { name := "ImplementsAbstractModifier"
            bases := [{ base := userPath "AbstractModifierBase3" }]
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { bodylessVirtualModifier with
                    override? := some { bases := [] }
                    body :=
                      some Solidity.Stmt.modifierPlaceholder } ] } ] }

def implementedAbstractModifierAccepted : Bool :=
  sourceUnitAccepted? implementedAbstractModifierSource

def libraryStateVarSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "BadLibrary"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x", ty := uint256 } ] } ] }

def libraryStateVarRejected : Bool :=
  Result.isError (SourceUnit.check libraryStateVarSource)

def libraryConstantSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "ConstantLibrary"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "ANSWER"
                    ty := uint256
                    mutability := Solidity.VarMutability.constant
                    init := some (numberExpr "42") }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "readAnswer"
                    visibility := some Solidity.Visibility.internal_
                    mutability := Solidity.StateMutability.pure
                    returns :=
                      [{ name := none, ty := uint256, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.ident "ANSWER"))) } ] } ] }

def libraryConstantAccepted : Bool :=
  sourceUnitAccepted? libraryConstantSource

def libraryImmutableSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "ImmutableLibrary"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    mutability := Solidity.VarMutability.immutable } ] } ] }

def libraryImmutableRejected : Bool :=
  Result.isError (SourceUnit.check libraryImmutableSource)

def libraryVirtualFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "VirtualLibrary"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "f"
                    virtual := true } ] } ] }

def libraryVirtualFunctionRejected : Bool :=
  Result.isError (SourceUnit.check libraryVirtualFunctionSource)

def libraryModifierFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "withModifier"
    visibility := some Solidity.Visibility.internal_
    modifiers := [{ target := userPath "onlyReady", args := [] }] }

def libraryModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "ModifierLibrary"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  passThroughModifier
              , Solidity.ContractItem.function
                  libraryModifierFunction ] } ] }

def libraryModifierAccepted : Bool :=
  sourceUnitAccepted? libraryModifierSource

def libraryVirtualModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "VirtualModifierLibrary"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { passThroughModifier with virtual := true }
              , Solidity.ContractItem.function
                  libraryModifierFunction ] } ] }

def libraryVirtualModifierRejected : Bool :=
  Result.isError (SourceUnit.check libraryVirtualModifierSource)

def emptyLibraryContract : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "Lib"
    items := [] }

def libraryTypeTy : Ty :=
  Solidity.Ty.user (userPath "Lib")

def libraryTypeAddressTy : Ty :=
  Solidity.Ty.address false

def libraryTypeUseSource (contractName : Name)
    (items : List Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract emptyLibraryContract
      , Solidity.SourceItem.contract
          { name := contractName, items := items } ] }

def libraryTypeExpressionFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "libraryAddress"
    params :=
      [{ name := some "input", ty := libraryTypeAddressTy, location := none }]
    returns :=
      [{ name := none, ty := libraryTypeAddressTy, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName libraryTypeAddressTy)
              [ Solidity.Arg.positional
                  (Solidity.Expr.call
                    (Solidity.Expr.typeName libraryTypeTy)
                    [ Solidity.Arg.positional
                        (Solidity.Expr.ident "input") ]) ]))) }

def libraryTypeExpressionSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeExpression"
    [Solidity.ContractItem.function libraryTypeExpressionFunction]

def libraryTypeParameterSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeParameter"
    [ Solidity.ContractItem.function
        { simpleReturnFunction with
          name := some "bad"
          visibility := some Solidity.Visibility.internal_
          params := [{ name := some "input", ty := libraryTypeTy }] } ]

def libraryTypeReturnSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeReturn"
    [ Solidity.ContractItem.function
        { simpleReturnFunction with
          name := some "bad"
          visibility := some Solidity.Visibility.internal_
          returns := [{ name := some "result", ty := libraryTypeTy }]
          body := some (Solidity.Stmt.block []) } ]

def libraryTypeLocalSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeLocal"
    [ Solidity.ContractItem.function
        { libraryTypeExpressionFunction with
          name := some "bad"
          body :=
            some
              (Solidity.Stmt.block
                [ Solidity.Stmt.varDecl
                    [ { name := some "value"
                        ty := some libraryTypeTy } ]
                    (some
                      (Solidity.Expr.call
                        (Solidity.Expr.typeName libraryTypeTy)
                        [Solidity.Arg.positional
                          (Solidity.Expr.ident "input")]))
                , Solidity.Stmt.returnValues
                    (some
                      (Solidity.Expr.call
                        (Solidity.Expr.typeName libraryTypeAddressTy)
                        [Solidity.Arg.positional
                          (Solidity.Expr.ident "value")])) ]) } ]

def libraryTypeStateSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeState"
    [ Solidity.ContractItem.stateVar
        { name := "value", ty := libraryTypeTy } ]

def libraryTypeStructSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeStruct"
    [ Solidity.ContractItem.structDecl
        { name := "Bad"
          fields := [{ name := "value", ty := libraryTypeTy }] } ]

def libraryTypeEventSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeEvent"
    [ Solidity.ContractItem.eventDecl
        { name := "Bad"
          params := [{ name := some "value", ty := libraryTypeTy }] } ]

def libraryTypeErrorSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeError"
    [ Solidity.ContractItem.errorDecl
        { name := "Bad"
          params := [{ name := some "value", ty := libraryTypeTy }] } ]

def libraryTypeMappingSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeMapping"
    [ Solidity.ContractItem.stateVar
        { name := "values"
          ty := Solidity.Ty.mapping libraryTypeTy uint256 } ]

def libraryTypeArraySource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeArray"
    [ Solidity.ContractItem.function
        { simpleReturnFunction with
          name := some "bad"
          visibility := some Solidity.Visibility.internal_
          params :=
            [ { name := some "values"
                ty := Solidity.Ty.array libraryTypeTy none
                location := some Solidity.DataLocation.memory } ] } ]

def libraryTypeFunctionSource : Solidity.SourceUnit :=
  libraryTypeUseSource "LibraryTypeFunction"
    [ Solidity.ContractItem.stateVar
        { name := "callback"
          ty := Solidity.Ty.function [libraryTypeTy] []
            Solidity.StateMutability.pure
            Solidity.Visibility.internal_ } ]

def libraryTypeUsingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract emptyLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := userPath "Lib", target := some libraryTypeTy } ] }

def libraryTypeUseDisciplineMatches : Bool :=
  sourceUnitAccepted? libraryTypeExpressionSource &&
    Result.isError (SourceUnit.check libraryTypeParameterSource) &&
    Result.isError (SourceUnit.check libraryTypeReturnSource) &&
    Result.isError (SourceUnit.check libraryTypeLocalSource) &&
    Result.isError (SourceUnit.check libraryTypeStateSource) &&
    Result.isError (SourceUnit.check libraryTypeStructSource) &&
    Result.isError (SourceUnit.check libraryTypeEventSource) &&
    Result.isError (SourceUnit.check libraryTypeErrorSource) &&
    Result.isError (SourceUnit.check libraryTypeMappingSource) &&
    Result.isError (SourceUnit.check libraryTypeArraySource) &&
    Result.isError (SourceUnit.check libraryTypeFunctionSource) &&
    Result.isError (SourceUnit.check libraryTypeUsingSource)

def libraryMemberExternalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "value", ty := uint256 }]
    returns := [{ name := none, ty := uint256 }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "value"))) }

def libraryWithExternalMember : Solidity.ContractDecl :=
  { emptyLibraryContract with
    items :=
      [Solidity.ContractItem.function
        libraryMemberExternalFunction] }

def libraryFunctionMemberSource (contractName : Name)
    (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract libraryWithExternalMember
      , Solidity.SourceItem.contract
          { name := contractName
            items := [Solidity.ContractItem.function fn] } ] }

def transientLibraryMemberBase : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName libraryTypeTy)
    [Solidity.Arg.positional
      (Solidity.Expr.ident "target")]

def libraryNamespaceSelectorSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "LibraryNamespaceSelector"
    { simpleReturnFunction with
      name := some "selector"
      returns :=
        [{ name := none, ty := Solidity.Ty.bytesN 4 }]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.member
                (Solidity.Expr.member
                  (Solidity.Expr.typeName libraryTypeTy) "f")
                "selector"))) }

def transientLibrarySelectorSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "TransientLibrarySelector"
    { simpleReturnFunction with
      name := some "bad"
      params := [{ name := some "target", ty := libraryTypeAddressTy }]
      returns :=
        [{ name := none, ty := Solidity.Ty.bytesN 4 }]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.member
                (Solidity.Expr.member
                  transientLibraryMemberBase "f")
                "selector"))) }

def libraryNamespaceAddressSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "LibraryNamespaceAddress"
    { simpleReturnFunction with
      name := some "bad"
      returns := [{ name := none, ty := libraryTypeAddressTy }]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.member
                (Solidity.Expr.member
                  (Solidity.Expr.typeName libraryTypeTy) "f")
                "address"))) }

def transientLibraryCallSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "TransientLibraryCall"
    { simpleReturnFunction with
      name := some "bad"
      params := [{ name := some "target", ty := libraryTypeAddressTy }]
      returns := [{ name := none, ty := uint256 }]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.call
                (Solidity.Expr.member
                  transientLibraryMemberBase "f")
                [Solidity.Arg.positional (numberExpr "1")]))) }

def transientLibraryCallOptionsSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "TransientLibraryCallOptions"
    { simpleReturnFunction with
      name := some "bad"
      params := [{ name := some "target", ty := libraryTypeAddressTy }]
      returns := [{ name := none, ty := uint256 }]
      visibility := some Solidity.Visibility.external_
      mutability := Solidity.StateMutability.nonpayable
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.member
                  transientLibraryMemberBase "f")
                [Solidity.CallOption.named "gas"
                  (numberExpr "100000")]
                [Solidity.Arg.positional (numberExpr "1")]))) }

def libraryAbiEncodeCallSource : Solidity.SourceUnit :=
  libraryFunctionMemberSource "LibraryAbiEncodeCall"
    { simpleReturnFunction with
      name := some "bad"
      returns :=
        [ { name := none
            ty := Solidity.Ty.bytes
            location := some Solidity.DataLocation.memory } ]
      body :=
        some
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.ident "abi") "encodeCall")
                [ Solidity.Arg.positional
                    (Solidity.Expr.member
                      (Solidity.Expr.typeName libraryTypeTy) "f")
                , Solidity.Arg.positional
                    (Solidity.Expr.tuple
                      [Solidity.TupleItem.value
                        (numberExpr "1")]) ]))) }

def libraryFunctionMemberDisciplineMatches : Bool :=
  sourceUnitAccepted? libraryNamespaceSelectorSource &&
    Result.isError (SourceUnit.check transientLibrarySelectorSource) &&
    Result.isError (SourceUnit.check libraryNamespaceAddressSource) &&
    Result.isError (SourceUnit.check transientLibraryCallSource) &&
    Result.isError (SourceUnit.check transientLibraryCallOptionsSource) &&
    Result.isError (SourceUnit.check libraryAbiEncodeCallSource)

def usingKnownLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract emptyLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := userPath "Lib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "UsesLib", items := [] } ] }

def usingKnownLibraryAccepted : Bool :=
  sourceUnitAccepted? usingKnownLibrarySource

def interfaceUsingDirectiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract emptyLibraryContract
      , Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IUsing"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "Lib"
                    target := some uint256 } ] } ] }

def interfaceUsingDirectiveRejected : Bool :=
  Result.isError (SourceUnit.check interfaceUsingDirectiveSource)

def usingUnknownLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.usingDecl
          { library := userPath "MissingLib"
            target := some uint256 } ] }

def usingUnknownLibraryRejected : Bool :=
  Result.isError (SourceUnit.check usingUnknownLibrarySource)

def usingNonLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NotALibrary", items := [] }
      , Solidity.SourceItem.usingDecl
          { library := userPath "NotALibrary"
            target := some uint256 } ] }

def usingNonLibraryRejected : Bool :=
  Result.isError (SourceUnit.check usingNonLibrarySource)

def usingFileWildcardSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract emptyLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := userPath "Lib" } ] }

def usingFileWildcardRejected : Bool :=
  Result.isError (SourceUnit.check usingFileWildcardSource)

def uintLibraryPlusOne : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "plusOne"
    params := [{ name := some "self", ty := uint256, location := none }]
    visibility := some Solidity.Visibility.public_
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.add
              (Solidity.Expr.ident "self")
              (numberExpr "1")))) }

def uintLibraryContract : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "UintLib"
    items := [Solidity.ContractItem.function
      uintLibraryPlusOne] }

def directLibraryCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "directLibrary"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "UintLib") "plusOne")
              [Solidity.Arg.positional (numberExpr "3")]))) }

def directLibraryCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract uintLibraryContract
      , Solidity.SourceItem.contract
          { name := "DirectLibrary"
            items := [Solidity.ContractItem.function
              directLibraryCallFunction] } ] }

def directLibraryCallAccepted : Bool :=
  sourceUnitAccepted? directLibraryCallSource

def usingLibraryMethodFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingLibrary"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member (numberExpr "3") "plusOne")
              []))) }

def usingLibraryMethodSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract uintLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := userPath "UintLib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "UsingLibrary"
            items := [Solidity.ContractItem.function
              usingLibraryMethodFunction] } ] }

def usingLibraryMethodAccepted : Bool :=
  sourceUnitAccepted? usingLibraryMethodSource

def explicitUsingLibraryMethodSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract uintLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["UintLib", "plusOne"] } }]
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ExplicitUsingLibrary"
            items := [Solidity.ContractItem.function
              usingLibraryMethodFunction] } ] }

def explicitUsingLibraryMethodAccepted : Bool :=
  sourceUnitAccepted? explicitUsingLibraryMethodSource

def freeUsingPlusOneFunction : Solidity.FunctionDecl :=
  { name := some "freeInc"
    params := [{ name := some "self", ty := uint256, location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.add
              (Solidity.Expr.ident "self")
              (numberExpr "1")))) }

def usingFreeFunctionMethodFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingFreeFunction"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member (numberExpr "3") "freeInc")
              []))) }

def explicitUsingFreeFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeFunction
          freeUsingPlusOneFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["freeInc"] } }]
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ExplicitUsingFree"
            items := [Solidity.ContractItem.function
              usingFreeFunctionMethodFunction] } ] }

def explicitUsingFreeFunctionAccepted : Bool :=
  sourceUnitAccepted? explicitUsingFreeFunctionSource

def usingHigherOrderInternalFunctionTy : Ty :=
  Solidity.Ty.function [uint256] [uint256]
    Solidity.StateMutability.pure
    Solidity.Visibility.internal_

def usingHigherOrderLibraryApply :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "runWith"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    params :=
      [ { name := some "self", ty := uint256, location := none }
      , { name := some "fn"
          ty := usingHigherOrderInternalFunctionTy
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "fn")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "self")]))) }

def usingHigherOrderLibrary : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "Runner"
    items :=
      [Solidity.ContractItem.function
        usingHigherOrderLibraryApply] }

def usingHigherOrderDouble :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "double"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    params := [{ name := some "x", ty := uint256, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.mul
              (Solidity.Expr.ident "x")
              (numberExpr "2")))) }

def usingHigherOrderDoubleOverload :
    Solidity.FunctionDecl :=
  { usingHigherOrderDouble with
    params :=
      [ { name := some "x", ty := uint256, location := none }
      , { name := some "y", ty := uint256, location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "x"))) }

def usingHigherOrderFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usingHigherOrder"
    mutability := Solidity.StateMutability.pure
    params := [{ name := some "x", ty := uint256, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "x") "runWith")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "double")]))) }

def usingHigherOrderNamedFunction :
    Solidity.FunctionDecl :=
  { usingHigherOrderFunction with
    name := some "usingHigherOrderNamed"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "x") "runWith")
              [Solidity.Arg.named "fn"
                (Solidity.Expr.ident "double")]))) }

def usingHigherOrderFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract usingHigherOrderLibrary
      , Solidity.SourceItem.contract
          { name := "UsingHigherOrder"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "Runner"
                    target := some uint256 }
              , Solidity.ContractItem.function
                  usingHigherOrderDouble
              , Solidity.ContractItem.function
                  usingHigherOrderFunction ] } ] }

def usingHigherOrderFunctionAccepted : Bool :=
  sourceUnitAccepted? usingHigherOrderFunctionSource

def usingHigherOrderNamedFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract usingHigherOrderLibrary
      , Solidity.SourceItem.contract
          { name := "UsingHigherOrderNamed"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "Runner"
                    target := some uint256 }
              , Solidity.ContractItem.function
                  usingHigherOrderDouble
              , Solidity.ContractItem.function
                  usingHigherOrderNamedFunction ] } ] }

def usingHigherOrderNamedFunctionAccepted : Bool :=
  sourceUnitAccepted? usingHigherOrderNamedFunctionSource

def usingHigherOrderFunctionOverloadedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract usingHigherOrderLibrary
      , Solidity.SourceItem.contract
          { name := "UsingHigherOrderOverloaded"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "Runner"
                    target := some uint256 }
              , Solidity.ContractItem.function
                  usingHigherOrderDoubleOverload
              , Solidity.ContractItem.function
                  usingHigherOrderDouble
              , Solidity.ContractItem.function
                  usingHigherOrderFunction ] } ] }

def usingHigherOrderFunctionOverloadedRejected : Bool :=
  Result.isError (SourceUnit.check usingHigherOrderFunctionOverloadedSource)

def usingHigherOrderNamedFunctionOverloadedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract usingHigherOrderLibrary
      , Solidity.SourceItem.contract
          { name := "UsingHigherOrderNamedOverloaded"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "Runner"
                    target := some uint256 }
              , Solidity.ContractItem.function
                  usingHigherOrderDoubleOverload
              , Solidity.ContractItem.function
                  usingHigherOrderDouble
              , Solidity.ContractItem.function
                  usingHigherOrderNamedFunction ] } ] }

def usingHigherOrderNamedFunctionOverloadedRejected : Bool :=
  Result.isError
    (SourceUnit.check usingHigherOrderNamedFunctionOverloadedSource)

def badExplicitUsingFreeFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["missingFree"] } }]
            target := some uint256 } ] }

def badExplicitUsingFreeFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitUsingFreeFunctionSource)

def badExplicitUsingFunctionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract uintLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["UintLib", "missing"] } }]
            target := some uint256 } ] }

def badExplicitUsingFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitUsingFunctionSource)

def badUsingLibraryReceiverSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract uintLibraryContract
      , Solidity.SourceItem.usingDecl
          { library := userPath "UintLib"
            target := some Solidity.Ty.bool }
      , Solidity.SourceItem.contract
          { name := "BadUsingLibrary"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badUsingLibrary"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (boolExpr true) "plusOne")
                              []))) } ] } ] }

def badUsingLibraryReceiverRejected : Bool :=
  Result.isError (SourceUnit.check badUsingLibraryReceiverSource)

def baseContract : Solidity.ContractDecl :=
  { name := "Base"
    items := [Solidity.ContractItem.function
      simpleReturnFunction] }

def derivedContract : Solidity.ContractDecl :=
  { name := "Derived"
    bases := [{ base := userPath "Base", args := [] }]
    items := [] }

def inheritanceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseContract
      , Solidity.SourceItem.contract derivedContract ] }

def inheritanceAccepted : Bool :=
  sourceUnitAccepted? inheritanceSource

def stateShadowBaseContract : Solidity.ContractDecl :=
  { name := "StateShadowBase"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            visibility := some Solidity.Visibility.internal_ } ] }

def stateShadowDerivedContract : Solidity.ContractDecl :=
  { name := "StateShadowDerived"
    bases := [{ base := userPath "StateShadowBase" }]
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := uint256 } ] }

def stateVariableShadowingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract stateShadowBaseContract
      , Solidity.SourceItem.contract
          stateShadowDerivedContract ] }

def stateVariableShadowingRejected : Bool :=
  Result.isError (SourceUnit.check stateVariableShadowingSource)

def privateStateShadowBaseContract : Solidity.ContractDecl :=
  { name := "PrivateStateShadowBase"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            visibility := some Solidity.Visibility.private_ } ] }

def privateStateShadowDerivedContract : Solidity.ContractDecl :=
  { name := "PrivateStateShadowDerived"
    bases := [{ base := userPath "PrivateStateShadowBase" }]
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x", ty := uint256 } ] }

def privateStateVariableShadowingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract privateStateShadowBaseContract
      , Solidity.SourceItem.contract
          privateStateShadowDerivedContract ] }

def privateStateVariableShadowingAccepted : Bool :=
  sourceUnitAccepted? privateStateVariableShadowingSource

def inheritedStateReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedStateBase"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] }
      , Solidity.SourceItem.contract
          { name := "InheritedStateDerived"
            bases := [{ base := userPath "InheritedStateBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "read"
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "x"))) } ] } ] }

def inheritedStateReadAccepted : Bool :=
  sourceUnitAccepted? inheritedStateReadSource

def privateInheritedStateReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PrivateInheritedStateBase"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    visibility :=
                      some Solidity.Visibility.private_
                    init := some (numberExpr "1") } ] }
      , Solidity.SourceItem.contract
          { name := "PrivateInheritedStateDerived"
            bases := [{ base := userPath "PrivateInheritedStateBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "read"
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.ident "x"))) } ] } ] }

def privateInheritedStateReadRejected : Bool :=
  Result.isError (SourceUnit.check privateInheritedStateReadSource)

def superBaseFunctionContract : Solidity.ContractDecl :=
  { name := "SuperTypeBase"
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.function
            name := some "setX"
            params := []
            returns := []
            visibility := some Solidity.Visibility.public_
            mutability := Solidity.StateMutability.nonpayable
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.function
            name := some "value"
            params := []
            returns := [{ name := none, ty := uint256, location := none }]
            visibility := some Solidity.Visibility.public_
            mutability := Solidity.StateMutability.view
            virtual := true
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some (numberExpr "1"))) } ] }

def superDerivedFunctionContract : Solidity.ContractDecl :=
  { name := "SuperTypeDerived"
    bases := [{ base := userPath "SuperTypeBase" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.function
            name := some "setViaSuper"
            params := []
            returns := []
            visibility := some Solidity.Visibility.public_
            mutability := Solidity.StateMutability.nonpayable
            body :=
              some
                (Solidity.Stmt.expr
                  (Solidity.Expr.call
                    (Solidity.Expr.member
                      (Solidity.Expr.ident "super") "setX")
                    [])) }
      , Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.function
            name := some "value"
            params := []
            returns := [{ name := none, ty := uint256, location := none }]
            visibility := some Solidity.Visibility.public_
            mutability := Solidity.StateMutability.view
            override? := some {}
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary
                      Solidity.BinaryOp.add
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.ident "super") "value")
                        [])
                      (numberExpr "2")))) } ] }

def superCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract superBaseFunctionContract
      , Solidity.SourceItem.contract
          superDerivedFunctionContract ] }

def superCallAccepted : Bool :=
  sourceUnitAccepted? superCallSource

def badSuperCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract superBaseFunctionContract
      , Solidity.SourceItem.contract
          { superDerivedFunctionContract with
            name := "BadSuperTypeDerived"
            bases := [{ base := userPath "SuperTypeBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSuper"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "super")
                                "missing")
                              []))) } ] } ] }

def badSuperCallRejected : Bool :=
  Result.isError (SourceUnit.check badSuperCallSource)

def superCallOptionsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract superBaseFunctionContract
      , Solidity.SourceItem.contract
          { superDerivedFunctionContract with
            name := "BadSuperOptions"
            bases := [{ base := userPath "SuperTypeBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badSuperOptions"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "super")
                                "value")
                              [gasOption "100"]
                              []))) } ] } ] }

def superCallOptionsRejected : Bool :=
  Result.isError (SourceUnit.check superCallOptionsSource)

def explicitBaseValueFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "value"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (numberExpr "11"))) }

def explicitBaseCallBaseContract : Solidity.ContractDecl :=
  { name := "ExplicitBaseTypeBase"
    items :=
      [ Solidity.ContractItem.function
          explicitBaseValueFunction ] }

def explicitBaseCallDerivedContract :
    Solidity.ContractDecl :=
  { name := "ExplicitBaseTypeDerived"
    bases := [{ base := userPath "ExplicitBaseTypeBase" }]
    items :=
      [ Solidity.ContractItem.function
          { simpleReturnFunction with
            name := some "directBase"
            mutability := Solidity.StateMutability.view
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.ident
                          "ExplicitBaseTypeBase")
                        "value")
                      []))) } ] }

def explicitBaseCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          explicitBaseCallBaseContract
      , Solidity.SourceItem.contract
          explicitBaseCallDerivedContract ] }

def explicitBaseCallAccepted : Bool :=
  sourceUnitAccepted? explicitBaseCallSource

def storageLayoutBaseContract : Solidity.ContractDecl :=
  { name := "StorageLayoutBase"
    items :=
      [ Solidity.ContractItem.stateVar
          { name := "x"
            ty := uint256
            init := some (numberExpr "1") } ] }

def storageLayoutAcceptedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract storageLayoutBaseContract
      , Solidity.SourceItem.contract
          { name := "StorageLayoutTop"
            layoutBase := some (numberExpr "5")
            bases := [{ base := userPath "StorageLayoutBase" }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "y"
                    ty := uint256
                    init := some (numberExpr "2") } ] } ] }

def storageLayoutAccepted : Bool :=
  sourceUnitAccepted? storageLayoutAcceptedSource

def constantStorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeConstant
          { name := "LAYOUT_SLOT"
            ty := uint256
            mutability := Solidity.VarMutability.constant
            init := some (numberExpr "8") }
      , Solidity.SourceItem.contract
          { name := "ConstantStorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.binary
                  Solidity.BinaryOp.add
                  (Solidity.Expr.ident "LAYOUT_SLOT")
                  (numberExpr "1"))
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def constantStorageLayoutAccepted : Bool :=
  sourceUnitAccepted? constantStorageLayoutSource

def unknownConstantStorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnknownConstantStorageLayout"
            layoutBase := some (Solidity.Expr.ident "MISSING")
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def unknownConstantStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check unknownConstantStorageLayoutSource)

def erc7201StorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Erc7201StorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "erc7201")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.literal
                        (Solidity.Literal.string
                          "example.main")) ])
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def erc7201StorageLayoutAccepted : Bool :=
  sourceUnitAccepted? erc7201StorageLayoutSource

def erc7201MinusOneStorageLayoutSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Erc7201MinusOneStorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.binary
                  Solidity.BinaryOp.sub
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "erc7201")
                    [ Solidity.Arg.positional
                        (Solidity.Expr.literal
                          (Solidity.Literal.string
                            "example.main")) ])
                  (numberExpr "1"))
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def erc7201MinusOneStorageLayoutAccepted : Bool :=
  sourceUnitAccepted? erc7201MinusOneStorageLayoutSource

def badErc7201StorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadErc7201StorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "erc7201")
                  [Solidity.Arg.positional (numberExpr "1")])
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def badErc7201StorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check badErc7201StorageLayoutSource)

def badErc7201ConcatStorageLayoutSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadErc7201ConcatStorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "erc7201")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.ident "string")
                          "concat")
                        [ Solidity.Arg.positional
                            (Solidity.Expr.literal
                              (Solidity.Literal.string
                                "example"))
                        , Solidity.Arg.positional
                            (Solidity.Expr.literal
                              (Solidity.Literal.string
                                ".main")) ]) ])
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def badErc7201ConcatStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check badErc7201ConcatStorageLayoutSource)

def badKeccakStorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadKeccakStorageLayout"
            layoutBase :=
              some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "keccak256")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.literal
                        (Solidity.Literal.string
                          "example.main")) ])
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def badKeccakStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check badKeccakStorageLayoutSource)

def inheritedStorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { storageLayoutBaseContract with
            name := "InheritedLayoutBase"
            layoutBase := some (numberExpr "3") }
      , Solidity.SourceItem.contract
          { name := "InheritedLayoutChild"
            bases := [{ base := userPath "InheritedLayoutBase" }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def inheritedStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check inheritedStorageLayoutSource)

def abstractStorageLayoutSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractStorageLayout"
            abstract := true
            layoutBase := some (numberExpr "5")
            items := [] } ] }

def abstractStorageLayoutRejected : Bool :=
  Result.isError (SourceUnit.check abstractStorageLayoutSource)

def mutableStorageLayoutBaseSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MutableStorageLayoutBase"
            layoutBase := some (Solidity.Expr.ident "x")
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := uint256
                    init := some (numberExpr "1") } ] } ] }

def mutableStorageLayoutBaseRejected : Bool :=
  Result.isError (SourceUnit.check mutableStorageLayoutBaseSource)

def badExplicitBaseCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          explicitBaseCallBaseContract
      , Solidity.SourceItem.contract
          { name := "NotAnExplicitBase"
            items := [Solidity.ContractItem.function
              explicitBaseValueFunction] }
      , Solidity.SourceItem.contract
          { explicitBaseCallDerivedContract with
            name := "BadExplicitBaseTypeDerived"
            bases := [{ base := userPath "ExplicitBaseTypeBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badDirectBase"
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident
                                  "NotAnExplicitBase")
                                "value")
                              []))) } ] } ] }

def badExplicitBaseCallRejected : Bool :=
  Result.isError (SourceUnit.check badExplicitBaseCallSource)

def contractUpcastFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "upcast"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "b"
                  ty := some
                    (Solidity.Ty.user (userPath "Base"))
                  location := none } ]
              (some (Solidity.Expr.ident "d"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def contractUpcastSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract baseContract
      , Solidity.SourceItem.contract derivedContract
      , Solidity.SourceItem.contract
          { name := "ContractUpcast"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "d"
                    ty := Solidity.Ty.user
                      (userPath "Derived") }
              , Solidity.ContractItem.function
                  contractUpcastFunction ] } ] }

def contractUpcastAccepted : Bool :=
  sourceUnitAccepted? contractUpcastSource

def unknownBaseSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DerivedMissing"
            bases := [{ base := userPath "MissingBase", args := [] }]
            items := [] } ] }

def unknownBaseRejected : Bool :=
  Result.isError (SourceUnit.check unknownBaseSource)

def virtualBaseFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "value"
    virtual := true }

def overrideValueFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "value"
    override? := some { bases := [] }
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.literal
              (Solidity.Literal.number "2")))) }

def virtualOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "VirtualBase"
            items := [Solidity.ContractItem.function
              virtualBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "VirtualDerived"
            bases := [{ base := userPath "VirtualBase", args := [] }]
            items := [Solidity.ContractItem.function
              overrideValueFunction] } ] }

def virtualOverrideAccepted : Bool :=
  sourceUnitAccepted? virtualOverrideSource

def missingOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MissingOverrideBase"
            items := [Solidity.ContractItem.function
              virtualBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "MissingOverrideDerived"
            bases :=
              [{ base := userPath "MissingOverrideBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with override? := none } ] } ] }

def missingOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingOverrideSource)

def nonvirtualOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonvirtualBase"
            items := [Solidity.ContractItem.function
              simpleReturnFunction] }
      , Solidity.SourceItem.contract
          { name := "NonvirtualDerived"
            bases := [{ base := userPath "NonvirtualBase", args := [] }]
            items := [Solidity.ContractItem.function
              overrideValueFunction] } ] }

def nonvirtualOverrideRejected : Bool :=
  Result.isError (SourceUnit.check nonvirtualOverrideSource)

def externalVirtualValueFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "value"
    params := []
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view
    virtual := true
    body := none }

def publicOverrideOfExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalBase"
            abstract := true
            items := [Solidity.ContractItem.function
              externalVirtualValueFunction] }
      , Solidity.SourceItem.contract
          { name := "PublicDerived"
            bases := [{ base := userPath "ExternalBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with
                    visibility :=
                      some Solidity.Visibility.public_
                    mutability :=
                      Solidity.StateMutability.pure } ] } ] }

def publicOverrideOfExternalAccepted : Bool :=
  sourceUnitAccepted? publicOverrideOfExternalSource

def externalCalldataVirtualReferenceFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "convert"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    virtual := true
    body := none }

def publicMemoryReferenceOverrideFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "convert"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    override? := some { bases := [] }
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "values"))) }

def externalReferenceLocationOverrideSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalReferenceLocationBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  externalCalldataVirtualReferenceFunction ] }
      , Solidity.SourceItem.contract
          { name := "ExternalReferenceLocationDerived"
            bases :=
              [ { base := userPath "ExternalReferenceLocationBase"
                  args := [] } ]
            items :=
              [ Solidity.ContractItem.function
                  publicMemoryReferenceOverrideFunction ] } ] }

def externalReferenceLocationOverrideAccepted : Bool :=
  sourceUnitAccepted? externalReferenceLocationOverrideSource

def pureStoragePointerPassFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "passStorage"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage } ]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "values"))) }

def pureStoragePointerPassSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureStoragePointerPass"
            items :=
              [ Solidity.ContractItem.function
                  pureStoragePointerPassFunction ] } ] }

def pureStoragePointerPassAccepted : Bool :=
  sourceUnitAccepted? pureStoragePointerPassSource

def pureStorageProjectionFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "readLength"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.storage } ]
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "values") "length"))) }

def pureStorageProjectionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureStorageProjection"
            items :=
              [ Solidity.ContractItem.function
                  pureStorageProjectionFunction ] } ] }

def pureStorageProjectionRejected : Bool :=
  Result.isError (SourceUnit.check pureStorageProjectionSource)

def storagePointerEffectDisciplineMatches : Bool :=
  pureStoragePointerPassAccepted && pureStorageProjectionRejected

def publicMemoryParamVirtualFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "readLength"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    virtual := true
    body := none }

def publicCalldataParamOverrideFunction :
    Solidity.FunctionDecl :=
  { publicMemoryParamVirtualFunction with
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    virtual := false
    override? := some { bases := [] }
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "values") "length"))) }

def publicParamLocationMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicParamLocationBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  publicMemoryParamVirtualFunction ] }
      , Solidity.SourceItem.contract
          { name := "PublicParamLocationDerived"
            bases :=
              [{ base := userPath "PublicParamLocationBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  publicCalldataParamOverrideFunction ] } ] }

def publicParamLocationMismatchRejected : Bool :=
  Result.isError (SourceUnit.check publicParamLocationMismatchSource)

def publicMemoryReturnVirtualFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "identity"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    virtual := true
    body := none }

def publicCalldataReturnOverrideFunction :
    Solidity.FunctionDecl :=
  { publicMemoryReturnVirtualFunction with
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    virtual := false
    override? := some { bases := [] }
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "values"))) }

def publicReturnLocationMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicReturnLocationBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  publicMemoryReturnVirtualFunction ] }
      , Solidity.SourceItem.contract
          { name := "PublicReturnLocationDerived"
            bases :=
              [{ base := userPath "PublicReturnLocationBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  publicCalldataReturnOverrideFunction ] } ] }

def publicReturnLocationMismatchRejected : Bool :=
  Result.isError (SourceUnit.check publicReturnLocationMismatchSource)

def internalMemoryVirtualReferenceFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "internalIdentity"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    virtual := true
    body := none }

def internalCalldataReferenceOverrideFunction :
    Solidity.FunctionDecl :=
  { internalMemoryVirtualReferenceFunction with
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    returns :=
      [ { name := none
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    virtual := false
    override? := some { bases := [] }
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "values"))) }

def internalLocationMismatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalLocationBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  internalMemoryVirtualReferenceFunction ] }
      , Solidity.SourceItem.contract
          { name := "InternalLocationDerived"
            bases :=
              [{ base := userPath "InternalLocationBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  internalCalldataReferenceOverrideFunction ] } ] }

def internalLocationMismatchRejected : Bool :=
  Result.isError (SourceUnit.check internalLocationMismatchSource)

def publicGetterOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.interface
            name := "IValue"
            items := [Solidity.ContractItem.function
              externalVirtualValueFunction] }
      , Solidity.SourceItem.contract
          { name := "GetterOverride"
            bases := [{ base := userPath "IValue", args := [] }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "value"
                    ty := uint256
                    visibility := some Solidity.Visibility.public_
                    override? := some { bases := [] } } ] } ] }

def publicGetterOverrideAccepted : Bool :=
  sourceUnitAccepted? publicGetterOverrideSource

def calleeGetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "get"
    params := [{ name := some "key", ty := uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "key"))) }

def calleeSetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "set"
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable }

def calleePayFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pay"
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.payable }

def calleeContract : Solidity.ContractDecl :=
  { name := "Callee"
    items :=
      [ Solidity.ContractItem.function calleeGetFunction
      , Solidity.ContractItem.function calleeSetFunction
      , Solidity.ContractItem.function calleePayFunction ] }

def calleeTy : Ty :=
  Solidity.Ty.user (userPath "Callee")

def externalMemberCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readRemote"
    params := [{ name := some "target", ty := calleeTy, location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "get")
              [ Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "7")) ]))) }

def externalMemberCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "ExternalMemberCaller"
            items := [Solidity.ContractItem.function
              externalMemberCallFunction] } ] }

def externalMemberCallAccepted : Bool :=
  sourceUnitAccepted? externalMemberCallSource

def bareExternalCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badBareExternal"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "get")
              [ Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "7")) ]))) }

def bareExternalCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BareExternalCall"
            items :=
              [ Solidity.ContractItem.function calleeGetFunction
              , Solidity.ContractItem.function
                  bareExternalCallFunction ] } ] }

def bareExternalCallRejected : Bool :=
  Result.isError (SourceUnit.check bareExternalCallSource)

def viewCallsNonpayableExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "ViewCallsNonpayableExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badRemoteWrite"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "set")
                              []))) } ] } ] }

def viewCallsNonpayableExternalRejected : Bool :=
  Result.isError (SourceUnit.check viewCallsNonpayableExternalSource)

def valueCallToNonpayableExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "ValueCallsNonpayableExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badValueRemote"
                    mutability := Solidity.StateMutability.payable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "get")
                              [valueOption "1"]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.number
                                      "7")) ]))) } ] } ] }

def valueCallToNonpayableExternalRejected : Bool :=
  Result.isError (SourceUnit.check valueCallToNonpayableExternalSource)

def valueCallToPayableExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "ValueCallsPayableExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "payRemote"
                    mutability := Solidity.StateMutability.payable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "pay")
                              [valueOption "1"] []))) } ] } ] }

def valueCallToPayableExternalAccepted : Bool :=
  sourceUnitAccepted? valueCallToPayableExternalSource

def signedValueOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "SignedValueOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badSignedValueRemote"
                    mutability := Solidity.StateMutability.payable
                    params :=
                      [ { name := some "target"
                          ty := calleeTy
                          location := none }
                      , { name := some "amount"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "pay")
                              [ Solidity.CallOption.named "value"
                                  (Solidity.Expr.ident "amount") ]
                              []))) } ] } ] }

def signedValueOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check signedValueOptionExternalSource)

def signedGasOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "SignedGasOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badSignedGasRemote"
                    mutability := Solidity.StateMutability.payable
                    params :=
                      [ { name := some "target"
                          ty := calleeTy
                          location := none }
                      , { name := some "gasAmount"
                          ty := int256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "pay")
                              [ Solidity.CallOption.named "gas"
                                  (Solidity.Expr.ident
                                    "gasAmount") ]
                              []))) } ] } ] }

def signedGasOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check signedGasOptionExternalSource)

def unknownCallOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "UnknownCallOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badUnknownCallOption"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "get")
                              [ Solidity.CallOption.named "foo"
                                  (numberExpr "1") ]
                              [ Solidity.Arg.positional
                                  (numberExpr "7") ]))) } ] } ] }

def unknownCallOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check unknownCallOptionExternalSource)

def saltCallOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "SaltCallOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badSaltCallOption"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "get")
                              [saltOption bytes32ZeroExpr]
                              [ Solidity.Arg.positional
                                  (numberExpr "7") ]))) } ] } ] }

def saltCallOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check saltCallOptionExternalSource)

def duplicateCallOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "DuplicateCallOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badDuplicateCallOption"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "get")
                              [ gasOption "1", gasOption "2" ]
                              [ Solidity.Arg.positional
                                  (numberExpr "7") ]))) } ] } ] }

def duplicateCallOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check duplicateCallOptionExternalSource)

def duplicateValueOptionExternalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract calleeContract
      , Solidity.SourceItem.contract
          { name := "DuplicateValueOptionExternal"
            items :=
              [ Solidity.ContractItem.function
                  { externalMemberCallFunction with
                    name := some "badDuplicateValueOption"
                    mutability := Solidity.StateMutability.payable
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "pay")
                              [valueOption "1", valueOption "2"]
                              []))) } ] } ] }

def duplicateValueOptionExternalRejected : Bool :=
  Result.isError (SourceUnit.check duplicateValueOptionExternalSource)

def internalCallOptionHelper : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "localValue"
    params := [{ name := some "x", ty := uint256, location := none }]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "x"))) }

def internalIdentifierCallOptionsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalIdentifierCallOptions"
            items :=
              [ Solidity.ContractItem.function
                  internalCallOptionHelper
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badInternalIdentifierOptions"
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.ident "localValue")
                              [gasOption "1"]
                              [Solidity.Arg.positional
                                (numberExpr "3")]))) } ] } ] }

def internalIdentifierCallOptionsRejected : Bool :=
  Result.isError (SourceUnit.check internalIdentifierCallOptionsSource)

def internalFunctionPointerCallOptionsSource :
    Solidity.SourceUnit :=
  let internalUintFunctionTy :=
    Solidity.Ty.function [uint256] [uint256]
      Solidity.StateMutability.pure
      Solidity.Visibility.internal_
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerCallOptions"
            items :=
              [ Solidity.ContractItem.function
                  internalCallOptionHelper
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badInternalFunctionPointerOptions"
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "fp"
                                  ty := some internalUintFunctionTy
                                  location := none } ]
                              (some
                                (Solidity.Expr.ident
                                  "localValue"))
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.callWithOptions
                                  (Solidity.Expr.ident "fp")
                                  [gasOption "1"]
                                  [Solidity.Arg.positional
                                    (numberExpr "3")])) ]) } ] } ] }

def internalFunctionPointerCallOptionsRejected : Bool :=
  Result.isError (SourceUnit.check internalFunctionPointerCallOptionsSource)

def lowLevelNamedArgumentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelNamedArgument"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badLowLevelNamedArgument"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "call")
                              [ Solidity.Arg.named "data"
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelNamedArgumentRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelNamedArgumentSource)

def lowLevelSaltOptionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelSaltOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badLowLevelSaltOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "call")
                              [saltOption bytes32ZeroExpr]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelSaltOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelSaltOptionSource)

def lowLevelUnknownOptionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelUnknownOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badLowLevelUnknownOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "call")
                              [ Solidity.CallOption.named "foo"
                                  (numberExpr "1") ]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelUnknownOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelUnknownOptionSource)

def lowLevelStaticValueOptionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelStaticValueOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badStaticValueOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "staticcall")
                              [valueOption "1"]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelStaticValueOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelStaticValueOptionSource)

def lowLevelDelegateValueOptionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelDelegateValueOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badDelegateValueOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "delegatecall")
                              [valueOption "1"]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelDelegateValueOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelDelegateValueOptionSource)

def lowLevelStaticSignedGasOptionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelStaticSignedGasOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badStaticSignedGasOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none }
                      , { name := some "gasAmount"
                          ty := int256
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "staticcall")
                              [ Solidity.CallOption.named "gas"
                                  (Solidity.Expr.ident
                                    "gasAmount") ]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelStaticSignedGasOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelStaticSignedGasOptionSource)

def lowLevelDuplicateGasOptionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelDuplicateGasOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badDuplicateGasOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "call")
                              [gasOption "1", gasOption "2"]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelDuplicateGasOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelDuplicateGasOptionSource)

def lowLevelDuplicateValueOptionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelDuplicateValueOption"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badDuplicateValueOption"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address true
                          location := none } ]
                    returns :=
                      [ { name := some "ok"
                          ty := Solidity.Ty.bool
                          location := none }
                      , { name := some "ret"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.callWithOptions
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "target")
                                "call")
                              [valueOption "1", valueOption "2"]
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1, 2])) ]))) } ] } ] }

def lowLevelDuplicateValueOptionRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelDuplicateValueOptionSource)

def arrayMemberCallOptionsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ArrayMemberCallOptions"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "items"
                    ty := Solidity.Ty.array uint256 none }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badArrayMemberOptions"
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.callWithOptions
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident "items")
                                  "push")
                                [gasOption "1"]
                                [Solidity.Arg.positional
                                  (numberExpr "3")])
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def arrayMemberCallOptionsRejected : Bool :=
  Result.isError (SourceUnit.check arrayMemberCallOptionsSource)

def highLevelCallOptionPlacementDisciplineMatches : Bool :=
  signedValueOptionExternalRejected &&
    signedGasOptionExternalRejected &&
    unknownCallOptionExternalRejected &&
    saltCallOptionExternalRejected &&
    duplicateCallOptionExternalRejected &&
    duplicateValueOptionExternalRejected

def lowLevelCallOptionPlacementDisciplineMatches : Bool :=
  lowLevelNamedArgumentRejected &&
    lowLevelSaltOptionRejected &&
    lowLevelUnknownOptionRejected &&
    lowLevelStaticValueOptionRejected &&
    lowLevelDelegateValueOptionRejected &&
    lowLevelStaticSignedGasOptionRejected &&
    lowLevelDuplicateGasOptionRejected &&
    lowLevelDuplicateValueOptionRejected

def nonExternalCallOptionPlacementDisciplineMatches : Bool :=
  superCallOptionsRejected &&
    internalIdentifierCallOptionsRejected &&
    internalFunctionPointerCallOptionsRejected &&
    arrayMemberCallOptionsRejected

def callOptionDisciplineRejected : Bool :=
  highLevelCallOptionPlacementDisciplineMatches &&
    nonExternalCallOptionPlacementDisciplineMatches &&
    lowLevelCallOptionPlacementDisciplineMatches

def lowLevelSendFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sendIt"
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address true
          location := none } ]
    returns :=
      [ { name := none
          ty := Solidity.Ty.bool
          location := none } ]
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "send")
              [ Solidity.Arg.positional
                  (Solidity.Expr.literal
                    (Solidity.Literal.number "1")) ]))) }

def lowLevelSendSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LowLevelSend"
            items := [Solidity.ContractItem.function
              lowLevelSendFunction] } ] }

def lowLevelSendAccepted : Bool :=
  sourceUnitAccepted? lowLevelSendSource

def lowLevelSendNonpayableAddressSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadLowLevelSend"
            items :=
              [ Solidity.ContractItem.function
                  { lowLevelSendFunction with
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ] } ] } ] }

def lowLevelSendNonpayableAddressRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelSendNonpayableAddressSource)

def lowLevelSendSignedAmountFunction :
    Solidity.FunctionDecl :=
  { lowLevelSendFunction with
    name := some "badSendSignedAmount"
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address true
          location := none }
      , { name := some "amount"
          ty := int256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "send")
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "amount") ]))) }

def lowLevelSendSignedAmountSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadLowLevelSendSignedAmount"
            items := [Solidity.ContractItem.function
              lowLevelSendSignedAmountFunction] } ] }

def lowLevelSendSignedAmountRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelSendSignedAmountSource)

def lowLevelTransferSignedAmountFunction :
    Solidity.FunctionDecl :=
  { lowLevelSendSignedAmountFunction with
    name := some "badTransferSignedAmount"
    returns := []
    body :=
      some
        (Solidity.Stmt.expr
          (Solidity.Expr.call
            (Solidity.Expr.member
              (Solidity.Expr.ident "target") "transfer")
            [ Solidity.Arg.positional
                (Solidity.Expr.ident "amount") ])) }

def lowLevelTransferSignedAmountSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadLowLevelTransferSignedAmount"
            items := [Solidity.ContractItem.function
              lowLevelTransferSignedAmountFunction] } ] }

def lowLevelTransferSignedAmountRejected : Bool :=
  Result.isError (SourceUnit.check lowLevelTransferSignedAmountSource)

def selfdestructFunction : Solidity.FunctionDecl :=
  { name := some "bye"
    visibility := some Solidity.Visibility.public_
    params :=
      [ { name := some "target"
          ty := Solidity.Ty.address true
          location := none } ]
    body :=
      some
        (Solidity.Stmt.expr
          (Solidity.Expr.call
            (Solidity.Expr.ident "selfdestruct")
            [ Solidity.Arg.positional
                (Solidity.Expr.ident "target") ])) }

def selfdestructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SelfdestructUse"
            items :=
              [Solidity.ContractItem.function
                selfdestructFunction] } ] }

def selfdestructAccepted : Bool :=
  sourceUnitAccepted? selfdestructSource

def selfdestructNonpayableAddressSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSelfdestructTarget"
            items :=
              [ Solidity.ContractItem.function
                  { selfdestructFunction with
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false
                          location := none } ] } ] } ] }

def selfdestructNonpayableAddressRejected : Bool :=
  Result.isError (SourceUnit.check selfdestructNonpayableAddressSource)

def selfdestructViewSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSelfdestructView"
            items :=
              [ Solidity.ContractItem.function
                  { selfdestructFunction with
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def selfdestructViewRejected : Bool :=
  Result.isError (SourceUnit.check selfdestructViewSource)

def c3XContract : Solidity.ContractDecl :=
  { name := "C3X" }

def c3AContract : Solidity.ContractDecl :=
  { name := "C3A"
    bases := [{ base := userPath "C3X", args := [] }] }

def c3BadContract : Solidity.ContractDecl :=
  { name := "C3Bad"
    bases :=
      [ { base := userPath "C3A", args := [] }
      , { base := userPath "C3X", args := [] } ] }

def c3BadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract c3XContract
      , Solidity.SourceItem.contract c3AContract
      , Solidity.SourceItem.contract c3BadContract ] }

def c3BadRejected : Bool :=
  Result.isError (SourceUnit.check c3BadSource)

def inheritedFunctionNameBaseFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "shadowed"
    virtual := true }

def inheritedFunctionNamePrivateBaseFunction :
    Solidity.FunctionDecl :=
  { inheritedFunctionNameBaseFunction with
    visibility := some Solidity.Visibility.private_
    virtual := false }

def privateStateShadowsInheritedFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedFunctionNameBase"
            items :=
              [Solidity.ContractItem.function
                inheritedFunctionNameBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "BadPrivateStateShadowsInheritedFunction"
            bases :=
              [{ base := userPath "InheritedFunctionNameBase", args := [] }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "shadowed"
                    ty := uint256
                    visibility :=
                      some Solidity.Visibility.private_ } ] } ] }

def privateStateShadowsInheritedFunctionRejected : Bool :=
  Result.isError
    (SourceUnit.check privateStateShadowsInheritedFunctionSource)

def privateStateShadowsInheritedPrivateFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedPrivateFunctionNameBase"
            items :=
              [Solidity.ContractItem.function
                inheritedFunctionNamePrivateBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "PrivateStateShadowsInheritedPrivateFunction"
            bases :=
              [ { base := userPath "InheritedPrivateFunctionNameBase"
                  args := [] } ]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "shadowed"
                    ty := uint256
                    visibility :=
                      some Solidity.Visibility.private_ } ] } ] }

def privateStateShadowsInheritedPrivateFunctionAccepted : Bool :=
  sourceUnitAccepted? privateStateShadowsInheritedPrivateFunctionSource

def inheritedStateNameBaseVar : Solidity.StateVarDecl :=
  { name := "stored"
    ty := uint256
    visibility := some Solidity.Visibility.internal_ }

def inheritedStateNamePrivateBaseVar :
    Solidity.StateVarDecl :=
  { inheritedStateNameBaseVar with
    visibility := some Solidity.Visibility.private_ }

def functionShadowsInheritedStateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedStateNameBase"
            items :=
              [Solidity.ContractItem.stateVar
                inheritedStateNameBaseVar] }
      , Solidity.SourceItem.contract
          { name := "BadFunctionShadowsInheritedState"
            bases :=
              [{ base := userPath "InheritedStateNameBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with name := some "stored" } ] } ] }

def functionShadowsInheritedStateRejected : Bool :=
  Result.isError (SourceUnit.check functionShadowsInheritedStateSource)

def functionShadowsInheritedPrivateStateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedPrivateStateNameBase"
            items :=
              [Solidity.ContractItem.stateVar
                inheritedStateNamePrivateBaseVar] }
      , Solidity.SourceItem.contract
          { name := "FunctionShadowsInheritedPrivateState"
            bases :=
              [ { base := userPath "InheritedPrivateStateNameBase"
                  args := [] } ]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with name := some "stored" } ] } ] }

def functionShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted? functionShadowsInheritedPrivateStateSource

def inheritedStateNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedStateNameBase"
      items :=
        [Solidity.ContractItem.stateVar
          inheritedStateNameBaseVar] }

def inheritedPrivateStateNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedPrivateStateNameBase"
      items :=
        [Solidity.ContractItem.stateVar
          inheritedStateNamePrivateBaseVar] }

def inheritedStateNameItemSource
    (item : Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ inheritedStateNameBaseSourceItem
      , Solidity.SourceItem.contract
          { name := "BadDeclarationShadowsInheritedState"
            bases :=
              [{ base := userPath "InheritedStateNameBase", args := [] }]
            items := [item] } ] }

def inheritedPrivateStateNameItemSource
    (item : Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ inheritedPrivateStateNameBaseSourceItem
      , Solidity.SourceItem.contract
          { name := "DeclarationShadowsInheritedPrivateState"
            bases :=
              [ { base := userPath "InheritedPrivateStateNameBase"
                  args := [] } ]
            items := [item] } ] }

def inheritedStateNameModifierItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.modifierDecl
    { name := "stored"
      body := some Solidity.Stmt.modifierPlaceholder }

def modifierShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource inheritedStateNameModifierItem))

def modifierShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource inheritedStateNameModifierItem)

def inheritedStateNameEventItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.eventDecl { name := "stored" }

def eventShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource inheritedStateNameEventItem))

def eventShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource inheritedStateNameEventItem)

def inheritedStateNameErrorItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.errorDecl { name := "stored" }

def errorShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource inheritedStateNameErrorItem))

def errorShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource inheritedStateNameErrorItem)

def inheritedStateNameStructItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.structDecl
    { name := "stored"
      fields := [{ name := "value", ty := uint256 }] }

def structShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource inheritedStateNameStructItem))

def structShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource inheritedStateNameStructItem)

def inheritedStateNameEnumItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.enumDecl
    { name := "stored", cases := ["Only"] }

def enumShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource inheritedStateNameEnumItem))

def enumShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource inheritedStateNameEnumItem)

def inheritedStateNameUserValueTypeItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.userValueTypeDecl
    { name := "stored", underlying := uint256 }

def userValueTypeShadowsInheritedStateRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedStateNameItemSource
        inheritedStateNameUserValueTypeItem))

def userValueTypeShadowsInheritedPrivateStateAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedPrivateStateNameItemSource
      inheritedStateNameUserValueTypeItem)

def inheritedFunctionNameEventItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.eventDecl { name := "shadowed" }

def eventShadowsInheritedFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedFunctionEventBase"
            items :=
              [Solidity.ContractItem.function
                inheritedFunctionNameBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "BadEventShadowsInheritedFunction"
            bases :=
              [{ base := userPath "InheritedFunctionEventBase", args := [] }]
            items := [inheritedFunctionNameEventItem] } ] }

def eventShadowsInheritedFunctionRejected : Bool :=
  Result.isError (SourceUnit.check eventShadowsInheritedFunctionSource)

def eventShadowsInheritedPrivateFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedPrivateFunctionEventBase"
            items :=
              [Solidity.ContractItem.function
                inheritedFunctionNamePrivateBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "EventShadowsInheritedPrivateFunction"
            bases :=
              [ { base := userPath "InheritedPrivateFunctionEventBase"
                  args := [] } ]
            items := [inheritedFunctionNameEventItem] } ] }

def eventShadowsInheritedPrivateFunctionAccepted : Bool :=
  sourceUnitAccepted? eventShadowsInheritedPrivateFunctionSource

def modifierShadowsInheritedFunctionItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.modifierDecl
    { name := "shadowed"
      body := some Solidity.Stmt.modifierPlaceholder }

def modifierShadowsInheritedFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedFunctionModifierBase"
            items :=
              [Solidity.ContractItem.function
                inheritedFunctionNameBaseFunction] }
      , Solidity.SourceItem.contract
          { name := "BadModifierShadowsInheritedFunction"
            bases :=
              [ { base := userPath "InheritedFunctionModifierBase"
                  args := [] } ]
            items := [modifierShadowsInheritedFunctionItem] } ] }

def modifierShadowsInheritedFunctionRejected : Bool :=
  Result.isError (SourceUnit.check modifierShadowsInheritedFunctionSource)

def inheritedModifierNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedModifierNameBase"
      items := [inheritedStateNameModifierItem] }

def inheritedModifierNameItemSource
    (item : Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ inheritedModifierNameBaseSourceItem
      , Solidity.SourceItem.contract
          { name := "BadDeclarationShadowsInheritedModifier"
            bases :=
              [{ base := userPath "InheritedModifierNameBase", args := [] }]
            items := [item] } ] }

def functionShadowsInheritedModifierFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "stored"
    mutability := Solidity.StateMutability.pure }

def functionShadowsInheritedModifierRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedModifierNameItemSource
        (Solidity.ContractItem.function
          functionShadowsInheritedModifierFunction)))

def stateShadowsInheritedModifierItem :
    Solidity.ContractItem :=
  Solidity.ContractItem.stateVar
    { name := "stored"
      ty := uint256
      visibility := some Solidity.Visibility.private_ }

def stateShadowsInheritedModifierRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedModifierNameItemSource
        stateShadowsInheritedModifierItem))

def eventShadowsInheritedModifierRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedModifierNameItemSource
        inheritedStateNameEventItem))

def inheritedEventNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedEventNameBase"
      items :=
        [Solidity.ContractItem.eventDecl
          { name := "announced" }] }

def inheritedEventNameItemSource
    (item : Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ inheritedEventNameBaseSourceItem
      , Solidity.SourceItem.contract
          { name := "BadDeclarationShadowsInheritedEvent"
            bases :=
              [{ base := userPath "InheritedEventNameBase", args := [] }]
            items := [item] } ] }

def functionShadowsInheritedEventFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "announced"
    mutability := Solidity.StateMutability.pure }

def functionShadowsInheritedEventRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedEventNameItemSource
        (Solidity.ContractItem.function
          functionShadowsInheritedEventFunction)))

def stateShadowsInheritedEventRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedEventNameItemSource
        (Solidity.ContractItem.stateVar
          { name := "announced"
            ty := uint256
            visibility := some Solidity.Visibility.private_ })))

def errorShadowsInheritedEventRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedEventNameItemSource
        (Solidity.ContractItem.errorDecl
          { name := "announced" })))

def eventOverloadsInheritedEventAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedEventNameItemSource
      (Solidity.ContractItem.eventDecl
        { name := "announced"
          params := [{ name := none, ty := uint256 }] }))

def eventDuplicatesInheritedEventRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedEventNameItemSource
        (Solidity.ContractItem.eventDecl
          { name := "announced" })))

def inheritedErrorNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedErrorNameBase"
      items :=
        [Solidity.ContractItem.errorDecl { name := "Problem" }] }

def inheritedErrorNameItemSource
    (item : Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [ inheritedErrorNameBaseSourceItem
      , Solidity.SourceItem.contract
          { name := "BadDeclarationShadowsInheritedError"
            bases :=
              [{ base := userPath "InheritedErrorNameBase", args := [] }]
            items := [item] } ] }

def eventShadowsInheritedErrorRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedErrorNameItemSource
        (Solidity.ContractItem.eventDecl
          { name := "Problem"
            params := [{ name := none, ty := uint256 }] })))

def revertInheritedErrorFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertInheritedError"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "Problem") [])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def revertInheritedErrorAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedErrorNameItemSource
      (Solidity.ContractItem.function
        revertInheritedErrorFunction))

def inheritedErrorShadowsFreeErrorBase :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedErrorShadowsFreeBase"
      items :=
        [Solidity.ContractItem.errorDecl
          { name := "Collision" }] }

def freeUintCollisionError :
    Solidity.SourceItem :=
  Solidity.SourceItem.freeError
    { name := "Collision"
      params := [{ name := none, ty := uint256, location := none }] }

def inheritedErrorShadowsFreeErrorSource
    (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ freeUintCollisionError
      , inheritedErrorShadowsFreeErrorBase
      , Solidity.SourceItem.contract
          { name := "InheritedErrorShadowsFree"
            bases :=
              [ { base := userPath "InheritedErrorShadowsFreeBase"
                  args := [] } ]
            items := [Solidity.ContractItem.function fn] } ] }

def revertFreeErrorSignatureFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "revertFreeErrorSignature"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "Collision")
                [Solidity.Arg.positional (numberExpr "1")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def inheritedErrorShadowsFreeErrorRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedErrorShadowsFreeErrorSource
        revertFreeErrorSignatureFunction))

def revertInheritedErrorSignatureFunction :
    Solidity.FunctionDecl :=
  { revertFreeErrorSignatureFunction with
    name := some "revertInheritedErrorSignature"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.revertCall
              (Solidity.Expr.call
                (Solidity.Expr.ident "Collision") [])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def inheritedErrorShadowAllowsInheritedSignatureAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedErrorShadowsFreeErrorSource
      revertInheritedErrorSignatureFunction)

def inheritedEventShadowsFreeEventBase :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedEventShadowsFreeBase"
      items :=
        [Solidity.ContractItem.eventDecl
          { name := "CollisionEvent" }] }

def freeUintCollisionEvent :
    Solidity.SourceItem :=
  Solidity.SourceItem.freeEvent
    { name := "CollisionEvent"
      params := [{ name := none, ty := uint256 }] }

def inheritedEventShadowsFreeEventSource
    (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ freeUintCollisionEvent
      , inheritedEventShadowsFreeEventBase
      , Solidity.SourceItem.contract
          { name := "InheritedEventShadowsFree"
            bases :=
              [ { base := userPath "InheritedEventShadowsFreeBase"
                  args := [] } ]
            items := [Solidity.ContractItem.function fn] } ] }

def emitFreeEventSignatureFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "emitFreeEventSignature"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.emitEvent
              (Solidity.Expr.call
                (Solidity.Expr.ident "CollisionEvent")
                [Solidity.Arg.positional (numberExpr "1")])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def inheritedEventShadowsFreeEventRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (inheritedEventShadowsFreeEventSource
        emitFreeEventSignatureFunction))

def emitInheritedEventSignatureFunction :
    Solidity.FunctionDecl :=
  { emitFreeEventSignatureFunction with
    name := some "emitInheritedEventSignature"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.emitEvent
              (Solidity.Expr.call
                (Solidity.Expr.ident "CollisionEvent") [])
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def inheritedEventShadowAllowsInheritedSignatureAccepted : Bool :=
  sourceUnitAccepted?
    (inheritedEventShadowsFreeEventSource
      emitInheritedEventSignatureFunction)

def inheritedStructNameBaseSourceItem :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "InheritedStructNameBase"
      items :=
        [Solidity.ContractItem.structDecl
          { name := "record"
            fields := [{ name := "value", ty := uint256 }] }] }

def functionShadowsInheritedTypeRejected : Bool :=
  Result.isError
    (SourceUnit.check
      { items :=
          [ inheritedStructNameBaseSourceItem
          , Solidity.SourceItem.contract
              { name := "BadFunctionShadowsInheritedType"
                bases :=
                  [{ base := userPath "InheritedStructNameBase", args := [] }]
                items :=
                  [ Solidity.ContractItem.function
                      { simpleReturnFunction with
                        name := some "record"
                        mutability :=
                          Solidity.StateMutability.pure } ] } ] })

def inheritedUserTypesBaseContract :
    Solidity.ContractDecl :=
  { name := "InheritedUserTypesBase"
    items :=
      [ Solidity.ContractItem.structDecl
          { name := "S"
            fields := [{ name := "x", ty := uint256 }] }
      , Solidity.ContractItem.enumDecl
          { name := "E", cases := ["A"] }
      , Solidity.ContractItem.userValueTypeDecl
          { name := "U", underlying := uint256 } ] }

def inheritedUserTypesStateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          inheritedUserTypesBaseContract
      , Solidity.SourceItem.contract
          { name := "InheritedUserTypesState"
            bases :=
              [{ base := userPath "InheritedUserTypesBase", args := [] }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "s"
                    ty := Solidity.Ty.user (userPath "S")
                    visibility :=
                      some Solidity.Visibility.internal_ }
              , Solidity.ContractItem.stateVar
                  { name := "e"
                    ty := Solidity.Ty.user (userPath "E")
                    visibility :=
                      some Solidity.Visibility.internal_ }
              , Solidity.ContractItem.stateVar
                  { name := "u"
                    ty := Solidity.Ty.user (userPath "U")
                    visibility :=
                      some Solidity.Visibility.internal_ } ] } ] }

def inheritedUserTypesStateAccepted : Bool :=
  sourceUnitAccepted? inheritedUserTypesStateSource

def qualifiedInheritedStructStateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          inheritedUserTypesBaseContract
      , Solidity.SourceItem.contract
          { name := "QualifiedInheritedStructState"
            bases :=
              [{ base := userPath "InheritedUserTypesBase", args := [] }]
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "s"
                    ty :=
                      Solidity.Ty.user
                        (TypeContext.qualifiedPath
                          "InheritedUserTypesBase" "S")
                    visibility :=
                      some Solidity.Visibility.internal_ } ] } ] }

def qualifiedInheritedStructStateAccepted : Bool :=
  sourceUnitAccepted? qualifiedInheritedStructStateSource

def freeStructShadowedByInheritedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          { name := "S"
            fields := [{ name := "y", ty := uint256 }] }
      , Solidity.SourceItem.contract
          inheritedUserTypesBaseContract
      , Solidity.SourceItem.contract
          { name := "FreeStructShadowedByInherited"
            bases :=
              [{ base := userPath "InheritedUserTypesBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "readInheritedX"
                    params :=
                      [ { name := some "s"
                          ty := Solidity.Ty.user (userPath "S")
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "s") "x"))) } ] } ] }

def freeStructShadowedByInheritedAccepted : Bool :=
  sourceUnitAccepted? freeStructShadowedByInheritedSource

def freeStructFieldHiddenByInheritedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          { name := "S"
            fields := [{ name := "y", ty := uint256 }] }
      , Solidity.SourceItem.contract
          inheritedUserTypesBaseContract
      , Solidity.SourceItem.contract
          { name := "FreeStructFieldHiddenByInherited"
            bases :=
              [{ base := userPath "InheritedUserTypesBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "readHiddenY"
                    params :=
                      [ { name := some "s"
                          ty := Solidity.Ty.user (userPath "S")
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "s") "y"))) } ] } ] }

def freeStructFieldHiddenByInheritedRejected : Bool :=
  Result.isError
    (SourceUnit.check freeStructFieldHiddenByInheritedSource)

def inheritedNameShadowingDisciplineMatches : Bool :=
  stateVariableShadowingRejected &&
    privateStateVariableShadowingAccepted &&
    inheritedStateReadAccepted &&
    privateInheritedStateReadRejected &&
    privateStateShadowsInheritedFunctionRejected &&
    privateStateShadowsInheritedPrivateFunctionAccepted &&
    functionShadowsInheritedStateRejected &&
    functionShadowsInheritedPrivateStateAccepted &&
    modifierShadowsInheritedStateRejected &&
    modifierShadowsInheritedPrivateStateAccepted &&
    eventShadowsInheritedStateRejected &&
    eventShadowsInheritedPrivateStateAccepted &&
    errorShadowsInheritedStateRejected &&
    errorShadowsInheritedPrivateStateAccepted &&
    structShadowsInheritedStateRejected &&
    structShadowsInheritedPrivateStateAccepted &&
    enumShadowsInheritedStateRejected &&
    enumShadowsInheritedPrivateStateAccepted &&
    userValueTypeShadowsInheritedStateRejected &&
    userValueTypeShadowsInheritedPrivateStateAccepted &&
    eventShadowsInheritedFunctionRejected &&
    eventShadowsInheritedPrivateFunctionAccepted &&
    modifierShadowsInheritedFunctionRejected &&
    functionShadowsInheritedModifierRejected &&
    stateShadowsInheritedModifierRejected &&
    eventShadowsInheritedModifierRejected &&
    functionShadowsInheritedEventRejected &&
    stateShadowsInheritedEventRejected &&
    errorShadowsInheritedEventRejected &&
    eventOverloadsInheritedEventAccepted &&
    eventDuplicatesInheritedEventRejected &&
    eventShadowsInheritedErrorRejected &&
    revertInheritedErrorAccepted &&
    inheritedErrorShadowsFreeErrorRejected &&
    inheritedErrorShadowAllowsInheritedSignatureAccepted &&
    inheritedEventShadowsFreeEventRejected &&
    inheritedEventShadowAllowsInheritedSignatureAccepted &&
    functionShadowsInheritedTypeRejected &&
    inheritedUserTypesStateAccepted &&
    qualifiedInheritedStructStateAccepted &&
    freeStructShadowedByInheritedAccepted &&
    freeStructFieldHiddenByInheritedRejected

def virtualModifier : Solidity.ModifierDecl :=
  { name := "guard"
    virtual := true
    body := some Solidity.Stmt.modifierPlaceholder }

def overrideModifier : Solidity.ModifierDecl :=
  { name := "guard"
    override? := some { bases := [] }
    body := some Solidity.Stmt.modifierPlaceholder }

def modifierOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierBase"
            items := [Solidity.ContractItem.modifierDecl
              virtualModifier] }
      , Solidity.SourceItem.contract
          { name := "ModifierDerived"
            bases := [{ base := userPath "ModifierBase", args := [] }]
            items := [Solidity.ContractItem.modifierDecl
              overrideModifier] } ] }

def modifierOverrideAccepted : Bool :=
  sourceUnitAccepted? modifierOverrideSource

def virtualMemoryReferenceModifier :
    Solidity.ModifierDecl :=
  { name := "referenceGuard"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.memory } ]
    virtual := true
    body := some Solidity.Stmt.modifierPlaceholder }

def calldataReferenceOverrideModifier :
    Solidity.ModifierDecl :=
  { name := "referenceGuard"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some Solidity.DataLocation.calldata } ]
    override? := some { bases := [] }
    body := some Solidity.Stmt.modifierPlaceholder }

def modifierLocationMismatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierLocationBase"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  virtualMemoryReferenceModifier ] }
      , Solidity.SourceItem.contract
          { name := "ModifierLocationDerived"
            bases :=
              [{ base := userPath "ModifierLocationBase", args := [] }]
            items :=
              [ Solidity.ContractItem.modifierDecl
                  calldataReferenceOverrideModifier ] } ] }

def modifierLocationMismatchRejected : Bool :=
  Result.isError (SourceUnit.check modifierLocationMismatchSource)

def abstractCallableIdentityFunction :
    Solidity.FunctionDecl :=
  { virtualBaseFunction with body := none }

def abstractConcreteCallableConflictSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractCallableConflictBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  abstractCallableIdentityFunction ] }
      , Solidity.SourceItem.contract
          { name := "ConcreteCallableConflictBase"
            items :=
              [ Solidity.ContractItem.function
                  virtualBaseFunction ] }
      , Solidity.SourceItem.contract
          { name := "AbstractConcreteCallableConflict"
            abstract := true
            bases :=
              [ { base := userPath "AbstractCallableConflictBase" }
              , { base := userPath "ConcreteCallableConflictBase" } ] } ] }

def abstractConcreteCallableConflictRejected : Bool :=
  Result.isError (SourceUnit.check abstractConcreteCallableConflictSource)

def twoAbstractCallableConflictSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FirstAbstractCallableBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  abstractCallableIdentityFunction ] }
      , Solidity.SourceItem.contract
          { name := "SecondAbstractCallableBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  abstractCallableIdentityFunction ] }
      , Solidity.SourceItem.contract
          { name := "TwoAbstractCallableConflict"
            abstract := true
            bases :=
              [ { base := userPath "FirstAbstractCallableBase" }
              , { base := userPath "SecondAbstractCallableBase" } ] } ] }

def twoAbstractCallableConflictRejected : Bool :=
  Result.isError (SourceUnit.check twoAbstractCallableConflictSource)

def abstractCallableDominanceSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractCallableAncestor"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  abstractCallableIdentityFunction ] }
      , Solidity.SourceItem.contract
          { name := "AbstractCallableImplementation"
            bases := [{ base := userPath "AbstractCallableAncestor" }]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with virtual := true } ] }
      , Solidity.SourceItem.contract
          { name := "AbstractCallableDominance"
            bases :=
              [ { base := userPath "AbstractCallableAncestor" }
              , { base := userPath "AbstractCallableImplementation" } ] } ] }

def abstractCallableDominanceAccepted : Bool :=
  sourceUnitAccepted? abstractCallableDominanceSource

def bodylessOverrideOfImplementedFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ImplementedCallableBase"
            items :=
              [ Solidity.ContractItem.function
                  virtualBaseFunction ] }
      , Solidity.SourceItem.contract
          { name := "BodylessImplementedCallableOverride"
            abstract := true
            bases := [{ base := userPath "ImplementedCallableBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { virtualBaseFunction with
                    body := none
                    override? := some { bases := [] } } ] } ] }

def bodylessOverrideOfImplementedFunctionRejected : Bool :=
  Result.isError
    (SourceUnit.check bodylessOverrideOfImplementedFunctionSource)

def modifierDominanceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractModifierAncestor"
            abstract := true
            items :=
              [ Solidity.ContractItem.modifierDecl
                  bodylessVirtualModifier ] }
      , Solidity.SourceItem.contract
          { name := "AbstractModifierImplementation"
            bases := [{ base := userPath "AbstractModifierAncestor" }]
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { virtualModifier with
                    virtual := true
                    override? := some { bases := [] } } ] }
      , Solidity.SourceItem.contract
          { name := "AbstractModifierDominance"
            bases :=
              [ { base := userPath "AbstractModifierAncestor" }
              , { base := userPath "AbstractModifierImplementation" } ] } ] }

def modifierDominanceAccepted : Bool :=
  sourceUnitAccepted? modifierDominanceSource

def bodylessOverrideOfImplementedModifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ImplementedModifierBase"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  virtualModifier ] }
      , Solidity.SourceItem.contract
          { name := "BodylessImplementedModifierOverride"
            abstract := true
            bases := [{ base := userPath "ImplementedModifierBase" }]
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { bodylessVirtualModifier with
                    override? := some { bases := [] } } ] } ] }

def bodylessOverrideOfImplementedModifierRejected : Bool :=
  Result.isError
    (SourceUnit.check bodylessOverrideOfImplementedModifierSource)

def unrelatedModifierConflictSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UnrelatedAbstractModifierBase"
            abstract := true
            items :=
              [ Solidity.ContractItem.modifierDecl
                  bodylessVirtualModifier ] }
      , Solidity.SourceItem.contract
          { name := "UnrelatedConcreteModifierBase"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  virtualModifier ] }
      , Solidity.SourceItem.contract
          { name := "UnrelatedModifierConflict"
            abstract := true
            bases :=
              [ { base := userPath "UnrelatedAbstractModifierBase" }
              , { base := userPath "UnrelatedConcreteModifierBase" } ] } ] }

def unrelatedModifierConflictRejected : Bool :=
  Result.isError (SourceUnit.check unrelatedModifierConflictSource)

def locationOnlyOverloadFunction
    (location : Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "locationOnly"
    params :=
      [ { name := some "values"
          ty := uintArrayTy
          location := some location } ]
    returns := []
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body := some Solidity.Stmt.empty }

def locationOnlyOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LocationOnlyOverload"
            items :=
              [ Solidity.ContractItem.function
                  (locationOnlyOverloadFunction
                    Solidity.DataLocation.memory)
              , Solidity.ContractItem.function
                  (locationOnlyOverloadFunction
                    Solidity.DataLocation.calldata) ] } ] }

def locationOnlyOverloadRejected : Bool :=
  Result.isError (SourceUnit.check locationOnlyOverloadSource)

def signatureIdentityOverloadFunction
    (paramName : Name) (returnTy : Ty)
    (visibility : Solidity.Visibility)
    (mutability : Solidity.StateMutability)
    (returnExpr : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "same"
    params :=
      [{ name := some paramName
         ty := uint256
         location := none }]
    returns := [{ name := none, ty := returnTy, location := none }]
    visibility := some visibility
    mutability := mutability
    body := some (Solidity.Stmt.returnValues (some returnExpr)) }

def signatureIdentityUintFunction
    (paramName : Name)
    (visibility : Solidity.Visibility :=
      Solidity.Visibility.internal_)
    (mutability : Solidity.StateMutability :=
      Solidity.StateMutability.pure) :
    Solidity.FunctionDecl :=
  signatureIdentityOverloadFunction paramName uint256 visibility mutability
    (Solidity.Expr.ident paramName)

def returnOnlyOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ReturnOnlyOverload"
            items :=
              [ Solidity.ContractItem.function
                  (signatureIdentityUintFunction "input")
              , Solidity.ContractItem.function
                  (signatureIdentityOverloadFunction "input"
                    Solidity.Ty.bool
                    Solidity.Visibility.internal_
                    Solidity.StateMutability.pure
                    (boolExpr true)) ] } ] }

def returnOnlyOverloadRejected : Bool :=
  Result.isError (SourceUnit.check returnOnlyOverloadSource)

def parameterNameOnlyOverloadSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ParameterNameOnlyOverload"
            items :=
              [ Solidity.ContractItem.function
                  (signatureIdentityUintFunction "first")
              , Solidity.ContractItem.function
                  (signatureIdentityUintFunction "second") ] } ] }

def parameterNameOnlyOverloadRejected : Bool :=
  Result.isError (SourceUnit.check parameterNameOnlyOverloadSource)

def visibilityOnlyOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "VisibilityOnlyOverload"
            items :=
              [ Solidity.ContractItem.function
                  (signatureIdentityUintFunction "input"
                    Solidity.Visibility.public_)
              , Solidity.ContractItem.function
                  (signatureIdentityUintFunction "input"
                    Solidity.Visibility.external_) ] } ] }

def visibilityOnlyOverloadRejected : Bool :=
  Result.isError (SourceUnit.check visibilityOnlyOverloadSource)

def mutabilityOnlyOverloadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MutabilityOnlyOverload"
            items :=
              [ Solidity.ContractItem.function
                  (signatureIdentityUintFunction "input"
                    Solidity.Visibility.public_
                    Solidity.StateMutability.pure)
              , Solidity.ContractItem.function
                  (signatureIdentityUintFunction "input"
                    Solidity.Visibility.public_
                    Solidity.StateMutability.view) ] } ] }

def mutabilityOnlyOverloadRejected : Bool :=
  Result.isError (SourceUnit.check mutabilityOnlyOverloadSource)

def selectorCollisionBurnFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "burn"
    params :=
      [{ name := some "value"
         ty := uint256
         location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "value"))) }

def selectorCollisionCollateFunction :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "collate_propagate_storage"
    params :=
      [{ name := some "value"
         ty := Solidity.Ty.bytesN 16
         location := none }]
    returns :=
      [{ name := none
         ty := Solidity.Ty.bytesN 16
         location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "value"))) }

def functionSelectorCollisionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FunctionSelectorCollision"
            items :=
              [ Solidity.ContractItem.function
                  selectorCollisionBurnFunction
              , Solidity.ContractItem.function
                  selectorCollisionCollateFunction ] } ] }

def functionSelectorCollisionRejected : Bool :=
  Result.isError (SourceUnit.check functionSelectorCollisionSource)

def getterSelectorCollisionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "GetterSelectorCollision"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "burn"
                    ty :=
                      Solidity.Ty.mapping
                        uint256 uint256
                    visibility := some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  selectorCollisionCollateFunction ] } ] }

def getterSelectorCollisionRejected : Bool :=
  Result.isError (SourceUnit.check getterSelectorCollisionSource)

def inheritedFunctionSelectorCollisionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SelectorCollisionBase"
            items :=
              [ Solidity.ContractItem.function
                  selectorCollisionBurnFunction ] }
      , Solidity.SourceItem.contract
          { name := "InheritedFunctionSelectorCollision"
            bases :=
              [{ base := { segments := ["SelectorCollisionBase"] }
                 args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  selectorCollisionCollateFunction ] } ] }

def inheritedFunctionSelectorCollisionRejected : Bool :=
  Result.isError
    (SourceUnit.check inheritedFunctionSelectorCollisionSource)

def inheritedGetterSelectorCollisionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "GetterSelectorCollisionBase"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "burn"
                    ty :=
                      Solidity.Ty.mapping
                        uint256 uint256
                    visibility := some Solidity.Visibility.public_ } ] }
      , Solidity.SourceItem.contract
          { name := "InheritedGetterSelectorCollision"
            bases :=
              [{ base := { segments := ["GetterSelectorCollisionBase"] }
                 args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  selectorCollisionCollateFunction ] } ] }

def inheritedGetterSelectorCollisionRejected : Bool :=
  Result.isError
    (SourceUnit.check inheritedGetterSelectorCollisionSource)

def callableSignatureIdentityDisciplineMatches : Bool :=
  locationOnlyOverloadRejected &&
    returnOnlyOverloadRejected &&
    parameterNameOnlyOverloadRejected &&
    visibilityOnlyOverloadRejected &&
    mutabilityOnlyOverloadRejected &&
    functionSelectorCollisionRejected &&
    getterSelectorCollisionRejected &&
    inheritedFunctionSelectorCollisionRejected &&
    inheritedGetterSelectorCollisionRejected

def overrideReturnTypeMismatchFunction :
    Solidity.FunctionDecl :=
  { overrideValueFunction with
    returns :=
      [{ name := none
         ty := Solidity.Ty.bool
         location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (boolExpr true))) }

def overrideReturnTypeMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "OverrideReturnTypeBase"
            items :=
              [ Solidity.ContractItem.function
                  virtualBaseFunction ] }
      , Solidity.SourceItem.contract
          { name := "OverrideReturnTypeMismatch"
            bases := [{ base := userPath "OverrideReturnTypeBase" }]
            items :=
              [ Solidity.ContractItem.function
                  overrideReturnTypeMismatchFunction ] } ] }

def overrideReturnTypeMismatchRejected : Bool :=
  Result.isError
    (SourceUnit.check overrideReturnTypeMismatchSource)

def overrideVisibilityMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "OverrideVisibilityBase"
            items :=
              [ Solidity.ContractItem.function
                  virtualBaseFunction ] }
      , Solidity.SourceItem.contract
          { name := "OverrideVisibilityMismatch"
            bases := [{ base := userPath "OverrideVisibilityBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with
                    visibility :=
                      some Solidity.Visibility.external_ } ] } ] }

def overrideVisibilityMismatchRejected : Bool :=
  Result.isError
    (SourceUnit.check overrideVisibilityMismatchSource)

def overrideMutabilityMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "OverrideMutabilityBase"
            items :=
              [ Solidity.ContractItem.function
                  virtualBaseFunction ] }
      , Solidity.SourceItem.contract
          { name := "OverrideMutabilityMismatch"
            bases := [{ base := userPath "OverrideMutabilityBase" }]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def overrideMutabilityMismatchRejected : Bool :=
  Result.isError
    (SourceUnit.check overrideMutabilityMismatchSource)

def multiBaseOverrideFirstBase :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "MultiBaseOverrideFirst"
      abstract := true
      items :=
        [ Solidity.ContractItem.function
            abstractCallableIdentityFunction ] }

def multiBaseOverrideSecondBase :
    Solidity.SourceItem :=
  Solidity.SourceItem.contract
    { name := "MultiBaseOverrideSecond"
      abstract := true
      items :=
        [ Solidity.ContractItem.function
            abstractCallableIdentityFunction ] }

def missingMultiBaseOverrideListSource :
    Solidity.SourceUnit :=
  { items :=
      [ multiBaseOverrideFirstBase
      , multiBaseOverrideSecondBase
      , Solidity.SourceItem.contract
          { name := "MissingMultiBaseOverrideList"
            bases :=
              [ { base := userPath "MultiBaseOverrideFirst" }
              , { base := userPath "MultiBaseOverrideSecond" } ]
            items :=
              [ Solidity.ContractItem.function
                  overrideValueFunction ] } ] }

def missingMultiBaseOverrideListRejected : Bool :=
  Result.isError
    (SourceUnit.check missingMultiBaseOverrideListSource)

def overrideBaseListMismatchSource :
    Solidity.SourceUnit :=
  { items :=
      [ multiBaseOverrideFirstBase
      , multiBaseOverrideSecondBase
      , Solidity.SourceItem.contract
          { name := "OverrideBaseListMismatch"
            bases :=
              [ { base := userPath "MultiBaseOverrideFirst" }
              , { base := userPath "MultiBaseOverrideSecond" } ]
            items :=
              [ Solidity.ContractItem.function
                  { overrideValueFunction with
                    override? :=
                      some
                        { bases :=
                            [userPath "MultiBaseOverrideFirst"] } } ] } ] }

def overrideBaseListMismatchRejected : Bool :=
  Result.isError
    (SourceUnit.check overrideBaseListMismatchSource)

def overrideSignatureCompatibilityDisciplineMatches : Bool :=
  virtualOverrideAccepted &&
    missingOverrideRejected &&
    nonvirtualOverrideRejected &&
    publicOverrideOfExternalAccepted &&
    overrideReturnTypeMismatchRejected &&
    overrideVisibilityMismatchRejected &&
    overrideMutabilityMismatchRejected &&
    missingMultiBaseOverrideListRejected &&
    overrideBaseListMismatchRejected

def callableIdentityDisciplineMatches : Bool :=
  abstractConcreteCallableConflictRejected &&
    twoAbstractCallableConflictRejected &&
    abstractCallableDominanceAccepted &&
    bodylessOverrideOfImplementedFunctionRejected &&
    modifierDominanceAccepted &&
    bodylessOverrideOfImplementedModifierRejected &&
    unrelatedModifierConflictRejected &&
    callableSignatureIdentityDisciplineMatches

def overrideDataLocationDisciplineMatches : Bool :=
  externalReferenceLocationOverrideAccepted &&
    publicParamLocationMismatchRejected &&
    publicReturnLocationMismatchRejected &&
    internalLocationMismatchRejected &&
    modifierLocationMismatchRejected

def missingModifierOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MissingModifierBase"
            items := [Solidity.ContractItem.modifierDecl
              virtualModifier] }
      , Solidity.SourceItem.contract
          { name := "MissingModifierDerived"
            bases :=
              [{ base := userPath "MissingModifierBase", args := [] }]
            items :=
              [ Solidity.ContractItem.modifierDecl
                  { overrideModifier with override? := none } ] } ] }

def missingModifierOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingModifierOverrideSource)

def inheritedBaseModifier : Solidity.ModifierDecl :=
  { name := "onlyBase"
    body := some Solidity.Stmt.modifierPlaceholder }

def inheritedModifierFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "usesInheritedModifier"
    modifiers := [{ target := userPath "onlyBase", args := [] }] }

def inheritedModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InheritedModifierBase"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  inheritedBaseModifier ] }
      , Solidity.SourceItem.contract
          { name := "InheritedModifierDerived"
            bases := [{ base := userPath "InheritedModifierBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  inheritedModifierFunction ] } ] }

def inheritedModifierAccepted : Bool :=
  sourceUnitAccepted? inheritedModifierSource

def stateX : Solidity.StateVarDecl :=
  { name := "x", ty := uint256 }

def pureStateReadFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readPure"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "x"))) }

def pureStateReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureReadsState"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.function
                  pureStateReadFunction ] } ] }

def pureStateReadRejected : Bool :=
  Result.isError (SourceUnit.check pureStateReadSource)

def viewStateReadFunction : Solidity.FunctionDecl :=
  { pureStateReadFunction with
    name := some "readView"
    mutability := Solidity.StateMutability.view }

def viewStateReadSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewReadsState"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.function
                  viewStateReadFunction ] } ] }

def viewStateReadAccepted : Bool :=
  sourceUnitAccepted? viewStateReadSource

def viewStateWriteFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "writeView"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "x")
                Solidity.AssignOp.assign
                (Solidity.Expr.literal
                  (Solidity.Literal.number "2")))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "1"))) ]) }

def viewStateWriteSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewWritesState"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.function
                  viewStateWriteFunction ] } ] }

def viewStateWriteRejected : Bool :=
  Result.isError (SourceUnit.check viewStateWriteSource)

def nonpayableStateWriteFunction : Solidity.FunctionDecl :=
  { viewStateWriteFunction with
    name := some "writeNonpayable"
    mutability := Solidity.StateMutability.nonpayable }

def nonpayableStateWriteSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonpayableWritesState"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.function
                  nonpayableStateWriteFunction ] } ] }

def nonpayableStateWriteAccepted : Bool :=
  sourceUnitAccepted? nonpayableStateWriteSource

def modifierArgFromParam : Solidity.ModifierDecl :=
  { name := "takesValue"
    params := [{ name := some "value", ty := uint256, location := none }]
    body := some Solidity.Stmt.modifierPlaceholder }

def modifierArgFromParamFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "passesParamToModifier"
    params := [{ name := some "v", ty := uint256, location := none }]
    modifiers :=
      [ { target := userPath "takesValue"
          args := [Solidity.Arg.positional
            (Solidity.Expr.ident "v")] } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "v"))) }

def modifierArgFromParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ModifierArgFromParam"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  modifierArgFromParam
              , Solidity.ContractItem.function
                  modifierArgFromParamFunction ] } ] }

def modifierArgFromParamAccepted : Bool :=
  sourceUnitAccepted? modifierArgFromParamSource

def stateReadModifier : Solidity.ModifierDecl :=
  { name := "readsState"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.ident "x")
          , Solidity.Stmt.modifierPlaceholder ]) }

def pureWithStateReadModifierFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pureWithReadModifier"
    mutability := Solidity.StateMutability.pure
    modifiers := [{ target := userPath "readsState", args := [] }] }

def pureWithStateReadModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureWithStateReadModifier"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.modifierDecl
                  stateReadModifier
              , Solidity.ContractItem.function
                  pureWithStateReadModifierFunction ] } ] }

def pureWithStateReadModifierRejected : Bool :=
  Result.isError (SourceUnit.check pureWithStateReadModifierSource)

def viewWithStateReadModifierFunction : Solidity.FunctionDecl :=
  { pureWithStateReadModifierFunction with
    name := some "viewWithReadModifier"
    mutability := Solidity.StateMutability.view }

def viewWithStateReadModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewWithStateReadModifier"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.modifierDecl
                  stateReadModifier
              , Solidity.ContractItem.function
                  viewWithStateReadModifierFunction ] } ] }

def viewWithStateReadModifierAccepted : Bool :=
  sourceUnitAccepted? viewWithStateReadModifierSource

def stateWriteModifier : Solidity.ModifierDecl :=
  { name := "writesState"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "x")
                Solidity.AssignOp.assign
                (Solidity.Expr.literal
                  (Solidity.Literal.number "5")))
          , Solidity.Stmt.modifierPlaceholder ]) }

def viewWithStateWriteModifierFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewWithWriteModifier"
    mutability := Solidity.StateMutability.view
    modifiers := [{ target := userPath "writesState", args := [] }] }

def viewWithStateWriteModifierSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewWithStateWriteModifier"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.modifierDecl
                  stateWriteModifier
              , Solidity.ContractItem.function
                  viewWithStateWriteModifierFunction ] } ] }

def viewWithStateWriteModifierRejected : Bool :=
  Result.isError (SourceUnit.check viewWithStateWriteModifierSource)

def nonpayableWithStateWriteModifierFunction :
    Solidity.FunctionDecl :=
  { viewWithStateWriteModifierFunction with
    name := some "nonpayableWithWriteModifier"
    mutability := Solidity.StateMutability.nonpayable }

def nonpayableWithStateWriteModifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonpayableWithStateWriteModifier"
            items :=
              [ Solidity.ContractItem.stateVar stateX
              , Solidity.ContractItem.modifierDecl
                  stateWriteModifier
              , Solidity.ContractItem.function
                  nonpayableWithStateWriteModifierFunction ] } ] }

def nonpayableWithStateWriteModifierAccepted : Bool :=
  sourceUnitAccepted? nonpayableWithStateWriteModifierSource

def viewTargetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "readOnly"
    mutability := Solidity.StateMutability.view }

def pureCallsViewFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "pureCallsView"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "readOnly") []))) }

def pureCallsViewSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureCallsView"
            items :=
              [ Solidity.ContractItem.function
                  viewTargetFunction
              , Solidity.ContractItem.function
                  pureCallsViewFunction ] } ] }

def pureCallsViewRejected : Bool :=
  Result.isError (SourceUnit.check pureCallsViewSource)

def viewCallsPureFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewCallsPure"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "f") []))) }

def viewCallsPureSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewCallsPure"
            items :=
              [ Solidity.ContractItem.function simpleReturnFunction
              , Solidity.ContractItem.function
                  viewCallsPureFunction ] } ] }

def viewCallsPureAccepted : Bool :=
  sourceUnitAccepted? viewCallsPureSource

def viewEmitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewEmits"
            items :=
              [ Solidity.ContractItem.eventDecl pingEvent
              , Solidity.ContractItem.function
                  { emitPingFunction with
                    name := some "viewEmit"
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def viewEmitRejected : Bool :=
  Result.isError (SourceUnit.check viewEmitSource)

def targetContractTy : Ty :=
  Solidity.Ty.user (userPath "Target")

def viewCreatesContractFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "viewCreates"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.newExpr targetContractTy [])
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.literal
                  (Solidity.Literal.number "1"))) ]) }

def viewCreatesContractSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Target", items := [] }
      , Solidity.SourceItem.contract
          { name := "ViewCreatesContract"
            items := [Solidity.ContractItem.function
              viewCreatesContractFunction] } ] }

def viewCreatesContractRejected : Bool :=
  Result.isError (SourceUnit.check viewCreatesContractSource)

def stateMutabilityDisciplineMatches : Bool :=
  pureStateReadRejected &&
    viewStateReadAccepted &&
    viewStateWriteRejected &&
    nonpayableStateWriteAccepted &&
    pureWithStateReadModifierRejected &&
    viewWithStateReadModifierAccepted &&
    viewWithStateWriteModifierRejected &&
    nonpayableWithStateWriteModifierAccepted &&
    pureCallsViewRejected &&
    viewCallsPureAccepted &&
    viewEmitRejected &&
    viewCreatesContractRejected

def externalViewUintFunctionTy : Ty :=
  Solidity.Ty.function [] [uint256]
    Solidity.StateMutability.view
    Solidity.Visibility.external_

def externalViewUintPairFunctionTy : Ty :=
  Solidity.Ty.function [] [uint256, uint256]
    Solidity.StateMutability.view
    Solidity.Visibility.external_

def externalViewBytesFunctionTy : Ty :=
  Solidity.Ty.functionWithLocations [] []
    [Solidity.Ty.bytes]
    [some Solidity.DataLocation.memory]
    Solidity.StateMutability.view
    Solidity.Visibility.external_

def externalPureUintFunctionTy : Ty :=
  Solidity.Ty.function [] [uint256]
    Solidity.StateMutability.pure
    Solidity.Visibility.external_

def internalPureUintFunctionTy : Ty :=
  Solidity.Ty.function [] [uint256]
    Solidity.StateMutability.pure
    Solidity.Visibility.internal_

def internalPureUintUnaryFunctionTy : Ty :=
  Solidity.Ty.function [uint256] [uint256]
    Solidity.StateMutability.pure
    Solidity.Visibility.internal_

def externalPayableFunctionTy : Ty :=
  Solidity.Ty.function [] []
    Solidity.StateMutability.payable
    Solidity.Visibility.external_

def internalPayableFunctionTy : Ty :=
  Solidity.Ty.function [] []
    Solidity.StateMutability.payable
    Solidity.Visibility.internal_

def publicPureUintFunctionTy : Ty :=
  Solidity.Ty.function [] [uint256]
    Solidity.StateMutability.pure
    Solidity.Visibility.public_

def externalFunctionTakingFunctionTy : Ty :=
  Solidity.Ty.function [externalPureUintFunctionTy] []
    Solidity.StateMutability.nonpayable
    Solidity.Visibility.external_

def externalFunctionTakingInternalFunctionTy : Ty :=
  Solidity.Ty.function [internalPureUintFunctionTy] []
    Solidity.StateMutability.nonpayable
    Solidity.Visibility.external_

def mappingUintToUintTy : Ty :=
  Solidity.Ty.mapping uint256 uint256

def externalFunctionTakingMappingTy : Ty :=
  Solidity.Ty.function [mappingUintToUintTy] []
    Solidity.StateMutability.nonpayable
    Solidity.Visibility.external_

def externalFunctionTakingFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalFunctionTakingFunction"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingFunctionTy } ] } ] }

def externalFunctionTakingFunctionAccepted : Bool :=
  sourceUnitAccepted? externalFunctionTakingFunctionSource

def externalFunctionTakingInternalFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadExternalFunctionTakingInternalFunction"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingInternalFunctionTy } ] } ] }

def externalFunctionTakingInternalFunctionRejected : Bool :=
  Result.isError
    (SourceUnit.check externalFunctionTakingInternalFunctionSource)

def externalFunctionTakingMappingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadExternalFunctionTakingMapping"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalFunctionTakingMappingTy } ] } ] }

def externalFunctionTakingMappingRejected : Bool :=
  Result.isError (SourceUnit.check externalFunctionTakingMappingSource)

def externalPayableFunctionTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalPayableFunctionType"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := externalPayableFunctionTy } ] } ] }

def externalPayableFunctionTypeAccepted : Bool :=
  sourceUnitAccepted? externalPayableFunctionTypeSource

def internalPayableFunctionTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadInternalPayableFunctionType"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fp"
                    ty := internalPayableFunctionTy } ] } ] }

def internalPayableFunctionTypeRejected : Bool :=
  Result.isError (SourceUnit.check internalPayableFunctionTypeSource)

def functionTypeAbiAdmissibilityDisciplineMatches : Bool :=
  externalFunctionTakingFunctionAccepted &&
    externalFunctionTakingInternalFunctionRejected &&
    externalFunctionTakingMappingRejected &&
    externalPayableFunctionTypeAccepted &&
    internalPayableFunctionTypeRejected

def functionTypeMutabilityConversionFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "functionTypeMutability"
    params :=
      [ { name := some "getter"
          ty := externalPureUintFunctionTy
          location := none } ]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "asView"
                  ty := some externalViewUintFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "getter"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def functionTypeMutabilityConversionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FunctionTypeMutability"
            items :=
              [Solidity.ContractItem.function
                functionTypeMutabilityConversionFunction] } ] }

def functionTypeMutabilityConversionAccepted : Bool :=
  sourceUnitAccepted? functionTypeMutabilityConversionSource

def namedFunctionTypeCallTarget : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "target"
    params :=
      [{ name := some "a"
         ty := uint256
         location := none }]
    visibility := some Solidity.Visibility.internal_
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "a"))) }

def namedFunctionTypeCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "bad"
    visibility := some Solidity.Visibility.internal_
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "fn"
                 ty := some internalPureUintUnaryFunctionTy
                 location := none }]
              (some (Solidity.Expr.ident "target"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fn")
                  [Solidity.Arg.named "a"
                    (numberExpr "1")])) ]) }

def namedFunctionTypeCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NamedFunctionTypeCall"
            items :=
              [ Solidity.ContractItem.function
                  namedFunctionTypeCallTarget
              , Solidity.ContractItem.function
                  namedFunctionTypeCallFunction ] } ] }

def namedFunctionTypeCallRejected : Bool :=
  Result.isError (SourceUnit.check namedFunctionTypeCallSource)

def functionLocationArrayTy : Ty :=
  Solidity.Ty.array uint256 none

def internalArrayFunctionTy
    (location : Solidity.DataLocation) : Ty :=
  Solidity.Ty.functionWithLocations
    [functionLocationArrayTy] [some location] [uint256] [none]
    Solidity.StateMutability.pure
    Solidity.Visibility.internal_

def functionLocationTarget (name : Name)
    (location : Solidity.DataLocation) :
    Solidity.FunctionDecl :=
  { name := some name
    params :=
      [{ name := some "values"
         ty := functionLocationArrayTy
         location := some location }]
    returns := [{ name := none, ty := uint256, location := none }]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "values") "length"))) }

def functionLocationAssignment (name target : Name) (expected : Ty) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "fn", ty := some expected, location := none }]
              (some (Solidity.Expr.ident target))
          , Solidity.Stmt.returnValues (some (numberExpr "1")) ]) }

def internalMemoryToCalldataFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MemoryToCalldataFunction"
            items :=
              [ Solidity.ContractItem.function
                  (functionLocationTarget "target"
                    Solidity.DataLocation.memory)
              , Solidity.ContractItem.function
                  (functionLocationAssignment "bad" "target"
                    (internalArrayFunctionTy
                      Solidity.DataLocation.calldata)) ] } ] }

def internalCalldataToMemoryFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CalldataToMemoryFunction"
            items :=
              [ Solidity.ContractItem.function
                  (functionLocationTarget "target"
                    Solidity.DataLocation.calldata)
              , Solidity.ContractItem.function
                  (functionLocationAssignment "bad" "target"
                    (internalArrayFunctionTy
                      Solidity.DataLocation.memory)) ] } ] }

def externalArrayFunctionTy
    (location : Solidity.DataLocation) : Ty :=
  Solidity.Ty.functionWithLocations
    [functionLocationArrayTy] [some location]
    [functionLocationArrayTy] [some location]
    Solidity.StateMutability.pure
    Solidity.Visibility.external_

def externalCalldataArrayFunctionSig : FunctionSig :=
  { name := "target"
    params := [functionLocationArrayTy]
    paramNames := [some "values"]
    paramStorageRefs := [false]
    paramDataLocations := [some Solidity.DataLocation.calldata]
    returns := [functionLocationArrayTy]
    returnStorageRefs := [false]
    returnDataLocations := [some Solidity.DataLocation.calldata]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure }

def functionTypeLocationDisciplineMatches : Bool :=
  Result.isError (SourceUnit.check internalMemoryToCalldataFunctionSource) &&
    Result.isError (SourceUnit.check internalCalldataToMemoryFunctionSource) &&
    namedFunctionTypeCallRejected &&
    match externalCalldataArrayFunctionSig.externalFunctionValueTy? with
    | some actual =>
        !Ty.canImplicitlyConvert actual
          (externalArrayFunctionTy Solidity.DataLocation.calldata) &&
        Ty.canImplicitlyConvert actual
          (externalArrayFunctionTy Solidity.DataLocation.memory)
    | none => false

def internalFunctionPointerAliasTarget :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "double"
    params :=
      [ { name := some "x"
          ty := uint256
          location := none } ]
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.mul
              (Solidity.Expr.ident "x")
              (numberExpr "2")))) }

def internalFunctionPointerAliasFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callViaPointer"
    params :=
      [ { name := some "x"
          ty := uint256
          location := none } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerAliasSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerAlias"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerAliasFunction ] } ] }

def internalFunctionPointerAliasAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerAliasSource

def internalFunctionPointerReassignTarget :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasTarget with
    name := some "triple"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.mul
              (Solidity.Expr.ident "x")
              (numberExpr "3")))) }

def internalFunctionPointerReassignFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaReassignedPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "fp")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "triple"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerReassignSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerReassign"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerReassignFunction ] } ] }

def internalFunctionPointerReassignAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerReassignSource

def internalFunctionPointerAssignAfterDeclFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaAssignedPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "fp")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "double"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerAssignAfterDeclSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerAssignAfterDecl"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerAssignAfterDeclFunction ] } ] }

def internalFunctionPointerAssignAfterDeclAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerAssignAfterDeclSource

def internalFunctionPointerDeleteThenAssignFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callViaDeletedThenAssignedPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.expr
              (Solidity.Expr.unary
                Solidity.UnaryOp.delete
                (Solidity.Expr.ident "fp"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "fp")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "triple"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerDeleteThenAssignSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerDeleteThenAssign"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerDeleteThenAssignFunction ] } ] }

def internalFunctionPointerDeleteThenAssignAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerDeleteThenAssignSource

def internalFunctionPointerUninitializedCallFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callUninitializedPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerUninitializedCallSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerUninitializedCall"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerUninitializedCallFunction ] } ] }

def internalFunctionPointerUninitializedCallAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerUninitializedCallSource

def internalFunctionPointerDeletedCallFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callDeletedPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.expr
              (Solidity.Expr.unary
                Solidity.UnaryOp.delete
                (Solidity.Expr.ident "fp"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "fp")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "x")])) ]) }

def internalFunctionPointerDeletedCallSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerDeletedCall"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerDeletedCallFunction ] } ] }

def internalFunctionPointerDeletedCallAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerDeletedCallSource

def internalFunctionPointerCopyFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "copyPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.varDecl
              [ { name := some "gp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "fp"))
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "fp")
                Solidity.AssignOp.assign
                (Solidity.Expr.ident "triple"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.binary
                  Solidity.BinaryOp.add
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "gp")
                    [Solidity.Arg.positional
                      (Solidity.Expr.ident "x")])
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "fp")
                    [Solidity.Arg.positional
                      (Solidity.Expr.ident "x")]))) ]) }

def internalFunctionPointerCopySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerCopy"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerReassignTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerCopyFunction ] } ] }

def internalFunctionPointerCopyAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerCopySource

def internalFunctionPointerParamApplyFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "applyPointer"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    params :=
      [ { name := some "fn"
          ty := internalPureUintUnaryFunctionTy
          location := none }
      , { name := some "x"
          ty := uint256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "fn")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "x")]))) }

def internalFunctionPointerParamCallerFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointer"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              (some (Solidity.Expr.ident "double"))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "applyPointer")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.ident "fp")
                  , Solidity.Arg.positional
                      (Solidity.Expr.ident "x") ])) ]) }

def internalFunctionPointerParamUninitializedCallerFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointerUninitialized"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "fp"
                  ty := some internalPureUintUnaryFunctionTy
                  location := none } ]
              none
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.ident "applyPointer")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.ident "fp")
                  , Solidity.Arg.positional
                      (Solidity.Expr.ident "x") ])) ]) }

def internalFunctionPointerParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerParam"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerParamApplyFunction
              , Solidity.ContractItem.function
                  internalFunctionPointerParamCallerFunction
              , Solidity.ContractItem.function
                  internalFunctionPointerParamUninitializedCallerFunction ] } ] }

def internalFunctionPointerParamAccepted : Bool :=
  sourceUnitAccepted? internalFunctionPointerParamSource

def internalFunctionPointerOverloadedTarget :
    Solidity.FunctionDecl :=
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
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "x"))) }

def internalFunctionPointerAliasOverloadedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerAliasOverloaded"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerOverloadedTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerAliasFunction ] } ] }

def internalFunctionPointerAliasOverloadedRejected : Bool :=
  Result.isError (SourceUnit.check internalFunctionPointerAliasOverloadedSource)

def internalFunctionPointerParamBareOverloadedCallerFunction :
    Solidity.FunctionDecl :=
  { internalFunctionPointerAliasFunction with
    name := some "callApplyPointerBare"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "applyPointer")
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "double")
              , Solidity.Arg.positional
                  (Solidity.Expr.ident "x") ]))) }

def internalFunctionPointerParamOverloadedSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "InternalFunctionPointerParamOverloaded"
            items :=
              [ Solidity.ContractItem.function
                  internalFunctionPointerOverloadedTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerAliasTarget
              , Solidity.ContractItem.function
                  internalFunctionPointerParamApplyFunction
              , Solidity.ContractItem.function
                  internalFunctionPointerParamBareOverloadedCallerFunction ] } ] }

def internalFunctionPointerParamOverloadedRejected : Bool :=
  Result.isError (SourceUnit.check internalFunctionPointerParamOverloadedSource)

def externalFunctionPointerGasCallFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callGetterWithGas"
    params :=
      [ { name := some "getter"
          ty := externalViewUintFunctionTy
          location := none } ]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.callWithOptions
              (Solidity.Expr.ident "getter")
              [gasOption "1000"] []))) }

def externalFunctionPointerGasCallSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalFunctionPointerGasCall"
            items :=
              [Solidity.ContractItem.function
                externalFunctionPointerGasCallFunction] } ] }

def externalFunctionPointerGasCallAccepted : Bool :=
  sourceUnitAccepted? externalFunctionPointerGasCallSource

def publicInternalFunctionPointerParamFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesInternalFunction"
    params :=
      [ { name := some "getter"
          ty := internalPureUintFunctionTy
          location := none } ] }

def publicInternalFunctionPointerParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadInternalFunctionPointerParam"
            items :=
              [Solidity.ContractItem.function
                publicInternalFunctionPointerParamFunction] } ] }

def publicInternalFunctionPointerParamRejected : Bool :=
  Result.isError (SourceUnit.check publicInternalFunctionPointerParamSource)

def invalidPublicFunctionTypeParamFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badFunctionTypeVisibility"
    params :=
      [ { name := some "getter"
          ty := publicPureUintFunctionTy
          location := none } ] }

def invalidPublicFunctionTypeParamSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFunctionTypeVisibility"
            items :=
              [Solidity.ContractItem.function
                invalidPublicFunctionTypeParamFunction] } ] }

def invalidPublicFunctionTypeParamRejected : Bool :=
  Result.isError (SourceUnit.check invalidPublicFunctionTypeParamSource)

def publicExternalFunctionPointerStateVarSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalFunctionPointerGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "getter"
                    ty := externalPureUintFunctionTy
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicExternalFunctionPointerStateVarAccepted : Bool :=
  sourceUnitAccepted? publicExternalFunctionPointerStateVarSource

def publicInternalFunctionPointerStateVarSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadInternalFunctionPointerGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "getter"
                    ty := internalPureUintFunctionTy
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicInternalFunctionPointerStateVarRejected : Bool :=
  Result.isError
    (SourceUnit.check publicInternalFunctionPointerStateVarSource)

def functionFieldStruct : Solidity.StructDecl :=
  { name := "FunctionField"
    fields := [{ name := "getter", ty := internalPureUintFunctionTy }] }

def functionFieldStructTy : Ty :=
  Solidity.Ty.user (userPath "FunctionField")

def publicStructInternalFunctionGetterSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct functionFieldStruct
      , Solidity.SourceItem.contract
          { name := "BadStructInternalFunctionGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "entry"
                    ty := functionFieldStructTy
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicStructInternalFunctionGetterRejected : Bool :=
  Result.isError
    (SourceUnit.check publicStructInternalFunctionGetterSource)

def publicFunctionTypeAbiBoundaryDisciplineMatches : Bool :=
  publicInternalFunctionPointerParamRejected &&
    invalidPublicFunctionTypeParamRejected &&
    publicExternalFunctionPointerStateVarAccepted &&
    publicInternalFunctionPointerStateVarRejected &&
    publicStructInternalFunctionGetterRejected

def nestedPublicGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedPublicGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.mapping uint256 uint256)
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.array uint256 none)
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def nestedPublicGetterAccepted : Bool :=
  sourceUnitAccepted? nestedPublicGetterSource

def publicBytesArrayGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicBytesArrayGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "blobs"
                    ty := Solidity.Ty.array
                      Solidity.Ty.bytes none
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicBytesArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicBytesArrayGetterSource

def publicStringArrayGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicStringArrayGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "names"
                    ty := Solidity.Ty.array
                      Solidity.Ty.string none
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicStringArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicStringArrayGetterSource

def publicFixedBytesArrayGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicFixedBytesArrayGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "fixedBlobs"
                    ty := Solidity.Ty.array
                      Solidity.Ty.bytes (some 2)
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicFixedBytesArrayGetterAccepted : Bool :=
  sourceUnitAccepted? publicFixedBytesArrayGetterSource

def publicStructGetterShapeStruct : Solidity.StructDecl :=
  { name := "PublicStructData"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "skipMap"
          ty := Solidity.Ty.mapping uint256 uint256 }
      , { name := "raw", ty := Solidity.Ty.bytes }
      , { name := "skipItems"
          ty := Solidity.Ty.array uint256 none }
      , { name := "ok", ty := Solidity.Ty.bool } ] }

def publicStructGetterShapeStateVar :
    Solidity.StateVarDecl :=
  { name := "entry"
    ty := Solidity.Ty.user (userPath "PublicStructData")
    visibility := some Solidity.Visibility.public_ }

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
        , Solidity.Ty.bytes
        , Solidity.Ty.bool ]
  | none => false

def publicStructGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , Solidity.SourceItem.contract
          { name := "PublicStructGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicStructGetterShapeStateVar ] } ] }

def publicStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicStructGetterSource

def publicNestedStructGetterInnerStruct :
    Solidity.StructDecl :=
  { name := "NestedPublicStruct"
    fields :=
      [ { name := "inner", ty := uint256 }
      , { name := "flag", ty := Solidity.Ty.bool } ] }

def publicNestedStructGetterOuterStruct :
    Solidity.StructDecl :=
  { name := "OuterPublicStruct"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "nested"
          ty :=
            Solidity.Ty.user
              (userPath "NestedPublicStruct") }
      , { name := "raw", ty := Solidity.Ty.bytes } ] }

def publicNestedStructGetterStateVar :
    Solidity.StateVarDecl :=
  { name := "entry"
    ty := Solidity.Ty.user (userPath "OuterPublicStruct")
    visibility := some Solidity.Visibility.public_ }

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
        , Solidity.Ty.user (userPath "NestedPublicStruct")
        , Solidity.Ty.bytes ]
  | none => false

def publicNestedStructGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicNestedStructGetterInnerStruct
      , Solidity.SourceItem.freeStruct
          publicNestedStructGetterOuterStruct
      , Solidity.SourceItem.contract
          { name := "PublicNestedStructGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicNestedStructGetterStateVar ] } ] }

def publicNestedStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicNestedStructGetterSource

def publicMappingStructGetterShapeStateVar :
    Solidity.StateVarDecl :=
  { name := "entries"
    ty :=
      Solidity.Ty.mapping uint256
        (Solidity.Ty.user (userPath "PublicStructData"))
    visibility := some Solidity.Visibility.public_ }

def publicMappingStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicMappingStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , Solidity.Ty.bytes
          , Solidity.Ty.bool ]
  | none => false

def publicMappingStructGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , Solidity.SourceItem.contract
          { name := "PublicMappingStructGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicMappingStructGetterShapeStateVar ] } ] }

def publicMappingStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicMappingStructGetterSource

def publicArrayStructGetterShapeStateVar :
    Solidity.StateVarDecl :=
  { name := "records"
    ty :=
      Solidity.Ty.array
        (Solidity.Ty.user (userPath "PublicStructData"))
        none
    visibility := some Solidity.Visibility.public_ }

def publicArrayStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicArrayStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , Solidity.Ty.bytes
          , Solidity.Ty.bool ]
  | none => false

def publicArrayStructGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , Solidity.SourceItem.contract
          { name := "PublicArrayStructGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicArrayStructGetterShapeStateVar ] } ] }

def publicArrayStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicArrayStructGetterSource

def publicFixedArrayStructGetterShapeStateVar :
    Solidity.StateVarDecl :=
  { name := "fixedRecords"
    ty :=
      Solidity.Ty.array
        (Solidity.Ty.user (userPath "PublicStructData"))
        (some 2)
    visibility := some Solidity.Visibility.public_ }

def publicFixedArrayStructGetterShapeReturns : Bool :=
  match StateVarDecl.publicGetterFunctionSig?
      publicStructGetterShapeTypes
      publicFixedArrayStructGetterShapeStateVar with
  | some sig =>
      sig.params == [uint256] &&
        sig.returns ==
          [ uint256
          , Solidity.Ty.bytes
          , Solidity.Ty.bool ]
  | none => false

def publicFixedArrayStructGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , Solidity.SourceItem.contract
          { name := "PublicFixedArrayStructGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicFixedArrayStructGetterShapeStateVar ] } ] }

def publicFixedArrayStructGetterAccepted : Bool :=
  sourceUnitAccepted? publicFixedArrayStructGetterSource

def deleteFixedArrayStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          publicStructGetterShapeStruct
      , Solidity.SourceItem.contract
          { name := "DeleteFixedArrayStruct"
            items :=
              [ Solidity.ContractItem.stateVar
                  publicFixedArrayStructGetterShapeStateVar
              , Solidity.ContractItem.function
                  { name := some "clear"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.ident
                              "fixedRecords"))) } ] } ] }

def deleteFixedArrayStructAccepted : Bool :=
  sourceUnitAccepted? deleteFixedArrayStructSource

def assignFixedStructArrayStruct : Solidity.StructDecl :=
  { name := "FixedStructArrayRecord"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "flag", ty := Solidity.Ty.bool } ] }

def assignFixedStructArrayRecordTy : Solidity.Ty :=
  Solidity.Ty.user (userPath "FixedStructArrayRecord")

def assignFixedStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "AssignFixedStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        assignFixedStructArrayRecordTy (some 2)
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              assignFixedStructArrayRecordTy (some 2)
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "records")
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident "values"))) } ] } ] }

def assignFixedStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignFixedStructArraySource

def assignDynamicStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "AssignDynamicStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              assignFixedStructArrayRecordTy none
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "records")
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident "values"))) } ] } ] }

def assignDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignDynamicStructArraySource

def indexAssignFixedStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "IndexAssignFixedStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        assignFixedStructArrayRecordTy (some 2)
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "records")
                              (numberExpr "1"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident "value"))) } ] } ] }

def indexAssignFixedStructArrayAccepted : Bool :=
  sourceUnitAccepted? indexAssignFixedStructArraySource

def indexAssignDynamicStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "IndexAssignDynamicStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "records")
                              (numberExpr "1"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident "value"))) } ] } ] }

def indexAssignDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? indexAssignDynamicStructArraySource

def indexAssignMappingStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "IndexAssignMappingStruct"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      Solidity.Ty.mapping uint256
                        assignFixedStructArrayRecordTy
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "entries")
                              (Solidity.Expr.ident "key"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident "value"))) } ] } ] }

def indexAssignMappingStructAccepted : Bool :=
  sourceUnitAccepted? indexAssignMappingStructSource

def pushStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          assignFixedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "PushStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        assignFixedStructArrayRecordTy none
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "pushValue"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "value"
                          ty := assignFixedStructArrayRecordTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "records")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "pushDefault"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "records")
                              "push")
                            [])) }
              , Solidity.ContractItem.function
                  { name := some "popOne"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "records")
                              "pop")
                            [])) }
              , Solidity.ContractItem.function
                  { name := some "deleteAll"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.ident
                              "records"))) } ] } ] }

def pushStructArrayAccepted : Bool :=
  sourceUnitAccepted? pushStructArraySource

def deleteNestedStructArrayStruct : Solidity.StructDecl :=
  { name := "NestedArrayRecord"
    fields :=
      [ { name := "amount", ty := uint256 }
      , { name := "items"
          ty := Solidity.Ty.array uint256 none } ] }

def deleteNestedStructArrayRecordTy : Solidity.Ty :=
  Solidity.Ty.user (userPath "NestedArrayRecord")

def deleteNestedStructArraySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "DeleteNestedStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "dynamicRecords"
                    ty :=
                      Solidity.Ty.array
                        deleteNestedStructArrayRecordTy none }
              , Solidity.ContractItem.stateVar
                  { name := "fixedRecords"
                    ty :=
                      Solidity.Ty.array
                        deleteNestedStructArrayRecordTy (some 2) }
              , Solidity.ContractItem.function
                  { name := some "clearDynamic"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.ident
                              "dynamicRecords"))) }
              , Solidity.ContractItem.function
                  { name := some "clearFixed"
                    visibility :=
                      some Solidity.Visibility.public_
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.ident
                              "fixedRecords"))) } ] } ] }

def deleteNestedStructArrayAccepted : Bool :=
  sourceUnitAccepted? deleteNestedStructArraySource

def assignNestedDynamicStructArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "AssignNestedDynamicStructArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "records"
                    ty :=
                      Solidity.Ty.array
                        deleteNestedStructArrayRecordTy none }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              deleteNestedStructArrayRecordTy none
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.ident "records")
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "values"))) } ] } ] }

def assignNestedDynamicStructArrayAccepted : Bool :=
  sourceUnitAccepted? assignNestedDynamicStructArraySource

def assignNestedStructMappingSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "AssignNestedStructMapping"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      Solidity.Ty.mapping uint256
                        deleteNestedStructArrayRecordTy }
              , Solidity.ContractItem.function
                  { name := some "set"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := deleteNestedStructArrayRecordTy
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "entries")
                              (Solidity.Expr.ident "key"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) } ] } ] }

def assignNestedStructMappingAccepted : Bool :=
  sourceUnitAccepted? assignNestedStructMappingSource

def indexedDynamicArrayAssignmentSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "IndexedDynamicArrayAssignment"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      Solidity.Ty.array
                        (Solidity.Ty.array
                          uint256 none)
                        none }
              , Solidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.array
                          uint256 none) }
              , Solidity.ContractItem.function
                  { name := some "setMatrix"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "index"
                          ty := uint256
                          location := none }
                      , { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              uint256 none
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "matrix")
                              (Solidity.Expr.ident "index"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "values"))) }
              , Solidity.ContractItem.function
                  { name := some "setBucket"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              uint256 none
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "buckets")
                              (Solidity.Expr.ident "key"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "values"))) } ] } ] }

def indexedDynamicArrayAssignmentAccepted : Bool :=
  sourceUnitAccepted? indexedDynamicArrayAssignmentSource

def deleteNestedIndexedStorageSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          deleteNestedStructArrayStruct
      , Solidity.SourceItem.contract
          { name := "DeleteNestedIndexedStorage"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      Solidity.Ty.array
                        (Solidity.Ty.array
                          uint256 none)
                        none }
              , Solidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      Solidity.Ty.mapping uint256
                        deleteNestedStructArrayRecordTy }
              , Solidity.ContractItem.function
                  { name := some "clearMatrix"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "index"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.ident "matrix")
                              (Solidity.Expr.ident
                                "index")))) }
              , Solidity.ContractItem.function
                  { name := some "clearEntry"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.ident
                                "entries")
                              (Solidity.Expr.ident
                                "key")))) } ] } ] }

def deleteNestedIndexedStorageAccepted : Bool :=
  sourceUnitAccepted? deleteNestedIndexedStorageSource

def nestedStoragePathSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedStoragePath"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      Solidity.Ty.array
                        (Solidity.Ty.array
                          uint256 none)
                        none }
              , Solidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.mapping
                          uint256 uint256) }
              , Solidity.ContractItem.function
                  { name := some "setMatrixCell"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "matrix")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident "inner"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "clearMatrixCell"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "matrix")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner")))) }
              , Solidity.ContractItem.function
                  { name := some "readMatrixCell"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "matrix")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner")))) }
              , Solidity.ContractItem.function
                  { name := some "setNested"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "nested")
                                (Solidity.Expr.ident
                                  "left"))
                              (Solidity.Expr.ident
                                "right"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "clearNested"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "nested")
                                (Solidity.Expr.ident
                                  "left"))
                              (Solidity.Expr.ident
                                "right")))) }
              , Solidity.ContractItem.function
                  { name := some "readNested"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "left"
                          ty := uint256
                          location := none }
                      , { name := some "right"
                          ty := uint256
                          location := none } ]
                    returns := [{ name := none, ty := uint256 }]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "nested")
                                (Solidity.Expr.ident
                                  "left"))
                              (Solidity.Expr.ident
                                "right")))) } ] } ] }

def nestedStoragePathAccepted : Bool :=
  sourceUnitAccepted? nestedStoragePathSource

def nestedStoragePathCompoundSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedStoragePathCompound"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      Solidity.Ty.array
                        (Solidity.Ty.array
                          uint256 none)
                        none }
              , Solidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.mapping
                          uint256 uint256) }
              , Solidity.ContractItem.function
                  { name := some "addMatrix"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "matrix")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner"))
                            Solidity.AssignOp.addAssign
                            (Solidity.Expr.ident
                              "delta"))) }
              , Solidity.ContractItem.function
                  { name := some "incMatrix"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.preIncrement
                              (Solidity.Expr.index
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "matrix")
                                  (Solidity.Expr.ident
                                    "outer"))
                                (Solidity.Expr.ident
                                  "inner"))))) }
              , Solidity.ContractItem.function
                  { name := some "addNested"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "nested")
                                (Solidity.Expr.ident
                                  "left"))
                              (Solidity.Expr.ident
                                "right"))
                            Solidity.AssignOp.addAssign
                            (Solidity.Expr.ident
                              "delta"))) } ] } ] }

def nestedStoragePathCompoundAccepted : Bool :=
  sourceUnitAccepted? nestedStoragePathCompoundSource

def structStoragePathRecord : Solidity.StructDecl :=
  { name := "StoragePathRecord"
    fields :=
      [ { name := "count", ty := uint256 }
      , { name := "values"
          ty := Solidity.Ty.array uint256 none }
      , { name := "blob", ty := Solidity.Ty.bytes }
      , { name := "scores"
          ty :=
            Solidity.Ty.mapping uint256 uint256 } ] }

def structStoragePathRecordTy : Solidity.Ty :=
  Solidity.Ty.user (userPath "StoragePathRecord")

def structStoragePathSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          structStoragePathRecord
      , Solidity.SourceItem.contract
          { name := "StructStoragePath"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "entries"
                    ty :=
                      Solidity.Ty.mapping uint256
                        structStoragePathRecordTy }
              , Solidity.ContractItem.function
                  { name := some "addCount"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.member
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "entries")
                                (Solidity.Expr.ident
                                  "key"))
                              "count")
                            Solidity.AssignOp.addAssign
                            (Solidity.Expr.ident
                              "delta"))) }
              , Solidity.ContractItem.function
                  { name := some "addValue"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "values")
                              (Solidity.Expr.ident
                                "index"))
                            Solidity.AssignOp.addAssign
                            (Solidity.Expr.ident
                              "delta"))) }
              , Solidity.ContractItem.function
                  { name := some "clearValue"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "index"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "values")
                              (Solidity.Expr.ident
                                "index")))) }
              , Solidity.ContractItem.function
                  { name := some "directPathArrayPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "values")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "directPathArrayPushAssign"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values")
                                "push")
                              [])
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "directPathArrayPop"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "values")
                              "pop")
                            [])) }
              , Solidity.ContractItem.function
                  { name := some "directPathBlobPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "blob")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "directPathBlobPushAssign"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob")
                                "push")
                              [])
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "directPathBlobPop"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.member
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key"))
                                "blob")
                              "pop")
                            [])) }
              , Solidity.ContractItem.function
                  { name := some "aliasCount"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "delta"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "ref"
                                  ty := some structStoragePathRecordTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key")))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "ref")
                                  "count")
                                Solidity.AssignOp.addAssign
                                (Solidity.Expr.ident
                                  "delta")) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasValue"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "ref"
                                  ty := some structStoragePathRecordTy
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "entries")
                                  (Solidity.Expr.ident
                                    "key")))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.index
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident
                                      "ref")
                                    "values")
                                  (Solidity.Expr.ident
                                    "index"))
                                Solidity.AssignOp.addAssign
                                (Solidity.Expr.ident
                                  "delta")) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasArrayPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (Solidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "vals")
                                  "push")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.ident
                                      "value") ]) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasArrayPushAssign"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (Solidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.call
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident
                                      "vals")
                                    "push")
                                  [])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident
                                  "value")) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasArrayPop"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "vals"
                                  ty :=
                                    some
                                      (Solidity.Ty.array
                                        uint256 none)
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "vals")
                                  "pop")
                                []) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasBlobPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some Solidity.Ty.bytes
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "blob")
                                  "push")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.ident
                                      "value") ]) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasBlobPushAssign"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some Solidity.Ty.bytes
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.call
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident
                                      "blob")
                                    "push")
                                  [])
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident
                                  "value")) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasBlobPop"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "blob"
                                  ty := some Solidity.Ty.bytes
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "blob")
                                  "pop")
                                []) ]) }
              , Solidity.ContractItem.function
                  { name := some "aliasScoreSet"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.varDecl
                              [ { name := some "scores"
                                  ty :=
                                    some
                                      (Solidity.Ty.mapping
                                        uint256 uint256)
                                  location :=
                                    some
                                      Solidity.DataLocation.storage } ]
                              (some
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "scores"))
                          , Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "scores")
                                  (Solidity.Expr.ident
                                    "subkey"))
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident
                                  "value")) ]) }
              , Solidity.ContractItem.function
                  { name := some "pushValuesStorage"
                    visibility :=
                      some Solidity.Visibility.internal_
                    params :=
                      [ { name := some "vals"
                          ty :=
                            Solidity.Ty.array
                              uint256 none
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident
                                "vals")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "pushBlobStorage"
                    visibility :=
                      some Solidity.Visibility.internal_
                    params :=
                      [ { name := some "blob"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident
                                "blob")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "setScoreStorage"
                    visibility :=
                      some Solidity.Visibility.internal_
                    params :=
                      [ { name := some "scores"
                          ty :=
                            Solidity.Ty.mapping
                              uint256 uint256
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.ident
                                "scores")
                              (Solidity.Expr.ident
                                "subkey"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.modifierDecl
                  { name := "withValues"
                    params :=
                      [ { name := some "vals"
                          ty :=
                            Solidity.Ty.array
                              uint256 none
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "vals")
                                  "push")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.ident
                                      "value") ])
                          , Solidity.Stmt.modifierPlaceholder ]) }
              , Solidity.ContractItem.modifierDecl
                  { name := "withBlob"
                    params :=
                      [ { name := some "blob"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.call
                                (Solidity.Expr.member
                                  (Solidity.Expr.ident
                                    "blob")
                                  "push")
                                [ Solidity.Arg.positional
                                    (Solidity.Expr.ident
                                      "value") ])
                          , Solidity.Stmt.modifierPlaceholder ]) }
              , Solidity.ContractItem.modifierDecl
                  { name := "withScore"
                    params :=
                      [ { name := some "scores"
                          ty :=
                            Solidity.Ty.mapping
                              uint256 uint256
                          location :=
                            some
                              Solidity.DataLocation.storage }
                      , { name := some "subkey"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.expr
                              (Solidity.Expr.assign
                                (Solidity.Expr.index
                                  (Solidity.Expr.ident
                                    "scores")
                                  (Solidity.Expr.ident
                                    "subkey"))
                                Solidity.AssignOp.assign
                                (Solidity.Expr.ident
                                  "value"))
                          , Solidity.Stmt.modifierPlaceholder ]) }
              , Solidity.ContractItem.function
                  { name := some "internalPathArrayPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident
                              "pushValuesStorage")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "internalPathBlobPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident
                              "pushBlobStorage")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "internalPathScoreSet"
                    visibility :=
                      some Solidity.Visibility.public_
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
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.ident
                              "setScoreStorage")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "scores")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "subkey")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ])) }
              , Solidity.ContractItem.function
                  { name := some "modifierPathArrayPush"
                    visibility :=
                      some Solidity.Visibility.public_
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
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "values")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ] } ]
                    body := some Solidity.Stmt.empty }
              , Solidity.ContractItem.function
                  { name := some "modifierPathBlobPush"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "key"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    modifiers :=
                      [ { target := userPath "withBlob"
                          args :=
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "blob")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ] } ]
                    body := some Solidity.Stmt.empty }
              , Solidity.ContractItem.function
                  { name := some "modifierPathScoreSet"
                    visibility :=
                      some Solidity.Visibility.public_
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
                            [ Solidity.Arg.positional
                                (Solidity.Expr.member
                                  (Solidity.Expr.index
                                    (Solidity.Expr.ident
                                      "entries")
                                    (Solidity.Expr.ident
                                      "key"))
                                  "scores")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "subkey")
                            , Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "value") ] } ]
                    body := some Solidity.Stmt.empty } ] } ] }

def structStoragePathAccepted : Bool :=
  sourceUnitAccepted? structStoragePathSource

def nestedBytesStoragePathSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedBytesStoragePath"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "blobs"
                    ty :=
                      Solidity.Ty.array
                        Solidity.Ty.bytes none }
              , Solidity.ContractItem.function
                  { name := some "setByte"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none }
                      , { name := some "value"
                          ty := Solidity.Ty.bytesN 1
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.assign
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "blobs")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner"))
                            Solidity.AssignOp.assign
                            (Solidity.Expr.ident
                              "value"))) }
              , Solidity.ContractItem.function
                  { name := some "clearByte"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.unary
                            Solidity.UnaryOp.delete
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "blobs")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner")))) }
              , Solidity.ContractItem.function
                  { name := some "readByte"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "outer"
                          ty := uint256
                          location := none }
                      , { name := some "inner"
                          ty := uint256
                          location := none } ]
                    returns :=
                      [ { name := none
                          ty := Solidity.Ty.bytesN 1 } ]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.index
                              (Solidity.Expr.index
                                (Solidity.Expr.ident
                                  "blobs")
                                (Solidity.Expr.ident
                                  "outer"))
                              (Solidity.Expr.ident
                                "inner")))) } ] } ] }

def nestedBytesStoragePathAccepted : Bool :=
  sourceUnitAccepted? nestedBytesStoragePathSource

def pushNestedDynamicArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PushNestedDynamicArray"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "matrix"
                    ty :=
                      Solidity.Ty.array
                        (Solidity.Ty.array
                          uint256 none)
                        none }
              , Solidity.ContractItem.function
                  { name := some "pushValues"
                    visibility :=
                      some Solidity.Visibility.public_
                    params :=
                      [ { name := some "values"
                          ty :=
                            Solidity.Ty.array
                              uint256 none
                          location :=
                            some Solidity.DataLocation.calldata } ]
                    body :=
                      some
                        (Solidity.Stmt.expr
                          (Solidity.Expr.call
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "matrix")
                              "push")
                            [ Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "values") ])) } ] } ] }

def pushNestedDynamicArrayAccepted : Bool :=
  sourceUnitAccepted? pushNestedDynamicArraySource

def publicMappingByteStringsGetterSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PublicMappingByteStringsGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "raw"
                    ty := Solidity.Ty.mapping
                      uint256 Solidity.Ty.bytes
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.stateVar
                  { name := "text"
                    ty := Solidity.Ty.mapping
                      uint256 Solidity.Ty.string
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def publicMappingByteStringsGetterAccepted : Bool :=
  sourceUnitAccepted? publicMappingByteStringsGetterSource

def nestedPublicGetterMemberCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NestedPublicGetterMemberCalls"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "nested"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.mapping uint256 uint256)
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.stateVar
                  { name := "buckets"
                    ty :=
                      Solidity.Ty.mapping uint256
                        (Solidity.Ty.array uint256 none)
                    visibility :=
                      some Solidity.Visibility.public_ }
              , Solidity.ContractItem.function
                  { name := some "readNested"
                    visibility := some Solidity.Visibility.public_
                    returns := [{ name := none, ty := uint256 }]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "this")
                                "nested")
                              [ Solidity.Arg.positional
                                  (numberExpr "4")
                              , Solidity.Arg.positional
                                  (numberExpr "5") ]))) }
              , Solidity.ContractItem.function
                  { name := some "readBucket"
                    visibility := some Solidity.Visibility.public_
                    returns := [{ name := none, ty := uint256 }]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "this")
                                "buckets")
                              [ Solidity.Arg.positional
                                  (numberExpr "7")
                              , Solidity.Arg.positional
                                  (numberExpr "1") ]))) } ] } ] }

def nestedPublicGetterMemberCallsAccepted : Bool :=
  sourceUnitAccepted? nestedPublicGetterMemberCallSource

def tryCatchZeroClause : Solidity.CatchClause :=
  Solidity.CatchClause.clause none []
    (Solidity.Stmt.returnValues
      (some
        (Solidity.Expr.literal
          (Solidity.Literal.number "0"))))

def tryExternalFunctionCall : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryExternal"
    params :=
      [ { name := some "getter"
          ty := externalViewUintFunctionTy
          location := none } ]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryExternalFunctionCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryExternalFunction"
            items := [Solidity.ContractItem.function
              tryExternalFunctionCall] } ] }

def tryExternalFunctionCallAccepted : Bool :=
  sourceUnitAccepted? tryExternalFunctionCallSource

def tryMemberTargetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "read"
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.view }

def tryContractMemberCallFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryMember"
    params :=
      [ { name := some "feed"
          ty := targetContractTy
          location := none } ]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.member
              (Solidity.Expr.ident "feed") "read") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryContractMemberCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Target"
            items :=
              [Solidity.ContractItem.function
                tryMemberTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "TryContractMember"
            items :=
              [Solidity.ContractItem.function
                tryContractMemberCallFunction] } ] }

def tryContractMemberCallAccepted : Bool :=
  sourceUnitAccepted? tryContractMemberCallSource

def tryInternalFunctionCall : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "tryInternal"
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "f") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def tryInternalFunctionCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryInternalFunction"
            items :=
              [ Solidity.ContractItem.function simpleReturnFunction
              , Solidity.ContractItem.function
                  tryInternalFunctionCall ] } ] }

def tryInternalFunctionCallRejected : Bool :=
  Result.isError (SourceUnit.check tryInternalFunctionCallSource)

def tryLowLevelCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryLowLevelCall"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryLowLevel"
                    params :=
                      [ { name := some "addr"
                          ty := Solidity.Ty.address false
                          location := none } ]
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.tryCatch
                              (memberCallExpr
                                (Solidity.Expr.ident "addr")
                                "call"
                                [Solidity.Arg.positional
                                  (memberCallExpr
                                    (Solidity.Expr.ident "abi")
                                    "encode" [])])
                              [tryCatchZeroClause]
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tryLowLevelCallRejected : Bool :=
  Result.isError (SourceUnit.check tryLowLevelCallSource)

def tryArrayPushSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryArrayPush"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "arr", ty := uintArrayTy }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryArrayPush"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.tryCatch
                              (arrayPushExpr
                                (Solidity.Expr.ident "arr")
                                [Solidity.Arg.positional
                                  (numberExpr "1")])
                              [tryCatchZeroClause]
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tryArrayPushRejected : Bool :=
  Result.isError (SourceUnit.check tryArrayPushSource)

def tryLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryLiteral"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.tryCatch
                              (Solidity.Expr.literal
                                (Solidity.Literal.number "1"))
                              [tryCatchZeroClause]
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.literal
                                  (Solidity.Literal.number "1"))) ]) } ] } ] }

def tryLiteralRejected : Bool :=
  Result.isError (SourceUnit.check tryLiteralSource)

def tryReturnMismatchFunction : Solidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryReturnMismatch"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "flag"
              ty := Solidity.Ty.bool
              location := none } ]
          (Solidity.Stmt.returnValues
            (some
              (Solidity.Expr.literal
                (Solidity.Literal.number "1"))))
          [tryCatchZeroClause]) }

def tryReturnMismatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryReturnMismatch"
            items := [Solidity.ContractItem.function
              tryReturnMismatchFunction] } ] }

def tryReturnMismatchRejected : Bool :=
  Result.isError (SourceUnit.check tryReturnMismatchSource)

def tryReturnsNoCatchFunction : Solidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryReturnsNoCatch"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          []) }

def tryReturnsNoCatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryReturnsNoCatch"
            items := [Solidity.ContractItem.function
              tryReturnsNoCatchFunction] } ] }

def tryReturnsNoCatchRejected : Bool :=
  Result.isError (SourceUnit.check tryReturnsNoCatchSource)

def tryNoCatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryNoCatch"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryNoCatch"
                    params :=
                      [ { name := some "getter"
                          ty := externalViewUintFunctionTy
                          location := none } ]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.tryCatch
                              (Solidity.Expr.call
                                (Solidity.Expr.ident "getter")
                                [])
                              []
                          , Solidity.Stmt.returnValues
                              (some (numberExpr "1")) ]) } ] } ] }

def tryNoCatchRejected : Bool :=
  Result.isError (SourceUnit.check tryNoCatchSource)

def tryReturnBytesMemoryFunction : Solidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryReturnBytesMemory"
    params :=
      [ { name := some "getter"
          ty := externalViewBytesFunctionTy
          location := none } ]
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "data"
              ty := Solidity.Ty.bytes
              location := some Solidity.DataLocation.memory } ]
          (Solidity.Stmt.returnValues
            (some (numberExpr "1")))
          [tryCatchZeroClause]) }

def tryReturnBytesMemorySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryReturnBytesMemory"
            items := [Solidity.ContractItem.function
              tryReturnBytesMemoryFunction] } ] }

def tryReturnBytesMemoryAccepted : Bool :=
  sourceUnitAccepted? tryReturnBytesMemorySource

def badTryReturnBytesCalldataFunction :
    Solidity.FunctionDecl :=
  { tryReturnBytesMemoryFunction with
    name := some "badTryReturnBytesCalldata"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "data"
              ty := Solidity.Ty.bytes
              location := some Solidity.DataLocation.calldata } ]
          (Solidity.Stmt.returnValues
            (some (numberExpr "1")))
          [tryCatchZeroClause]) }

def badTryReturnBytesCalldataSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTryReturnBytesCalldata"
            items := [Solidity.ContractItem.function
              badTryReturnBytesCalldataFunction] } ] }

def badTryReturnBytesCalldataRejected : Bool :=
  Result.isError (SourceUnit.check badTryReturnBytesCalldataSource)

def badTryReturnBytesStorageFunction :
    Solidity.FunctionDecl :=
  { tryReturnBytesMemoryFunction with
    name := some "badTryReturnBytesStorage"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "data"
              ty := Solidity.Ty.bytes
              location := some Solidity.DataLocation.storage } ]
          (Solidity.Stmt.returnValues
            (some (numberExpr "1")))
          [tryCatchZeroClause]) }

def badTryReturnBytesStorageSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTryReturnBytesStorage"
            items := [Solidity.ContractItem.function
              badTryReturnBytesStorageFunction] } ] }

def badTryReturnBytesStorageRejected : Bool :=
  Result.isError (SourceUnit.check badTryReturnBytesStorageSource)

def badTryReturnBytesNoLocationFunction :
    Solidity.FunctionDecl :=
  { tryReturnBytesMemoryFunction with
    name := some "badTryReturnBytesNoLocation"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "data"
              ty := Solidity.Ty.bytes
              location := none } ]
          (Solidity.Stmt.returnValues
            (some (numberExpr "1")))
          [tryCatchZeroClause]) }

def badTryReturnBytesNoLocationSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTryReturnBytesNoLocation"
            items := [Solidity.ContractItem.function
              badTryReturnBytesNoLocationFunction] } ] }

def badTryReturnBytesNoLocationRejected : Bool :=
  Result.isError (SourceUnit.check badTryReturnBytesNoLocationSource)

def duplicateTryReturnNameFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "duplicateTryReturnName"
    params :=
      [ { name := some "getter"
          ty := externalViewUintPairFunctionTy
          location := none } ]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [ { name := some "value"
              ty := uint256
              location := none }
          , { name := some "value"
              ty := uint256
              location := none } ]
          (Solidity.Stmt.returnValues
            (some (numberExpr "1")))
          [tryCatchZeroClause]) }

def duplicateTryReturnNameSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateTryReturnName"
            items :=
              [ Solidity.ContractItem.function
                  duplicateTryReturnNameFunction ] } ] }

def duplicateTryReturnNameRejected : Bool :=
  Result.isError (SourceUnit.check duplicateTryReturnNameSource)

def catchErrorClause : Solidity.CatchClause :=
  Solidity.CatchClause.clause (some "Error")
    [ { name := some "reason"
        ty := Solidity.Ty.string
        location := some Solidity.DataLocation.memory } ]
    (Solidity.Stmt.returnValues
      (some
        (Solidity.Expr.literal
          (Solidity.Literal.number "0"))))

def tryCatchErrorFunction : Solidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryCatchError"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [catchErrorClause]) }

def tryCatchErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryCatchError"
            items := [Solidity.ContractItem.function
              tryCatchErrorFunction] } ] }

def tryCatchErrorAccepted : Bool :=
  sourceUnitAccepted? tryCatchErrorSource

def badCatchErrorClause : Solidity.CatchClause :=
  Solidity.CatchClause.clause (some "Error")
    [{ name := some "code", ty := uint256, location := none }]
    (Solidity.Stmt.returnValues
      (some
        (Solidity.Expr.literal
          (Solidity.Literal.number "0"))))

def badCatchErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCatchError"
            items :=
              [ Solidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "badCatchError"
                    body :=
                      some
                        (Solidity.Stmt.tryCatchReturns
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (Solidity.Stmt.returnValues
                            (some (Solidity.Expr.ident "value")))
                          [badCatchErrorClause]) } ] } ] }

def badCatchErrorRejected : Bool :=
  Result.isError (SourceUnit.check badCatchErrorSource)

def catchPanicClause : Solidity.CatchClause :=
  Solidity.CatchClause.clause (some "Panic")
    [{ name := some "code", ty := uint256, location := none }]
    (Solidity.Stmt.returnValues
      (some
        (Solidity.Expr.literal
          (Solidity.Literal.number "0"))))

def catchBytesClause : Solidity.CatchClause :=
  Solidity.CatchClause.clause none
    [ { name := some "data"
        ty := Solidity.Ty.bytes
        location := some Solidity.DataLocation.memory } ]
    (Solidity.Stmt.returnValues
      (some
        (Solidity.Expr.literal
          (Solidity.Literal.number "0"))))

def tryCatchFullFunction : Solidity.FunctionDecl :=
  { tryExternalFunctionCall with
    name := some "tryCatchFull"
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter") [])
          [{ name := some "value", ty := uint256, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [catchErrorClause, catchPanicClause, catchBytesClause]) }

def tryCatchFullSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TryCatchFull"
            items := [Solidity.ContractItem.function
              tryCatchFullFunction] } ] }

def tryCatchFullAccepted : Bool :=
  sourceUnitAccepted? tryCatchFullSource

def duplicateCatchErrorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateCatchError"
            items :=
              [ Solidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateCatchError"
                    body :=
                      some
                        (Solidity.Stmt.tryCatchReturns
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (Solidity.Stmt.returnValues
                            (some (Solidity.Expr.ident "value")))
                          [catchErrorClause, catchErrorClause]) } ] } ] }

def duplicateCatchErrorRejected : Bool :=
  Result.isError (SourceUnit.check duplicateCatchErrorSource)

def duplicateCatchPanicSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateCatchPanic"
            items :=
              [ Solidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateCatchPanic"
                    body :=
                      some
                        (Solidity.Stmt.tryCatchReturns
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (Solidity.Stmt.returnValues
                            (some (Solidity.Expr.ident "value")))
                          [catchPanicClause, catchPanicClause]) } ] } ] }

def duplicateCatchPanicRejected : Bool :=
  Result.isError (SourceUnit.check duplicateCatchPanicSource)

def duplicateLowLevelCatchSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DuplicateLowLevelCatch"
            items :=
              [ Solidity.ContractItem.function
                  { tryExternalFunctionCall with
                    name := some "duplicateLowLevelCatch"
                    body :=
                      some
                        (Solidity.Stmt.tryCatchReturns
                          (Solidity.Expr.call
                            (Solidity.Expr.ident "getter") [])
                          [ { name := some "value"
                              ty := uint256
                              location := none } ]
                          (Solidity.Stmt.returnValues
                            (some (Solidity.Expr.ident "value")))
                          [tryCatchZeroClause, catchBytesClause]) } ] } ] }

def duplicateLowLevelCatchRejected : Bool :=
  Result.isError (SourceUnit.check duplicateLowLevelCatchSource)

def tryContractCreationSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Target", items := [] }
      , Solidity.SourceItem.contract
          { name := "TryContractCreation"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "tryCreate"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    body :=
                      some
                        (Solidity.Stmt.block
                          [ Solidity.Stmt.tryCatch
                              (Solidity.Expr.newExpr
                                targetContractTy [])
                              [tryCatchZeroClause]
                          , Solidity.Stmt.returnValues
                              (some
                                (Solidity.Expr.literal
                                  (Solidity.Literal.number "1"))) ]) } ] } ] }

def tryContractCreationAccepted : Bool :=
  sourceUnitAccepted? tryContractCreationSource

def tryCatchStaticDisciplineMatches : Bool :=
  tryExternalFunctionCallAccepted &&
    tryContractMemberCallAccepted &&
    tryInternalFunctionCallRejected &&
    tryLowLevelCallRejected &&
    tryArrayPushRejected &&
    tryLiteralRejected &&
    tryReturnMismatchRejected &&
    tryReturnsNoCatchRejected &&
    tryNoCatchRejected &&
    tryReturnBytesMemoryAccepted &&
    badTryReturnBytesCalldataRejected &&
    badTryReturnBytesStorageRejected &&
    badTryReturnBytesNoLocationRejected &&
    duplicateTryReturnNameRejected &&
    tryCatchErrorAccepted &&
    badCatchErrorRejected &&
    tryCatchFullAccepted &&
    duplicateCatchErrorRejected &&
    duplicateCatchPanicRejected &&
    duplicateLowLevelCatchRejected &&
    tryContractCreationAccepted

def pureMsgSigFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "sig"
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytesN 4
          location := none } ]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "msg") "sig"))) }

def pureMsgSigSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureMsgSig"
            items := [Solidity.ContractItem.function
              pureMsgSigFunction] } ] }

def pureMsgSigAccepted : Bool :=
  sourceUnitAccepted? pureMsgSigSource

def pureMsgValueFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "msgValue"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "msg") "value"))) }

def pureMsgValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureMsgValue"
            items := [Solidity.ContractItem.function
              pureMsgValueFunction] } ] }

def pureMsgValueRejected : Bool :=
  Result.isError (SourceUnit.check pureMsgValueSource)

def viewBlockTimestampFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "blockTime"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "block") "timestamp"))) }

def viewBlockTimestampSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewBlockTimestamp"
            items := [Solidity.ContractItem.function
              viewBlockTimestampFunction] } ] }

def viewBlockTimestampAccepted : Bool :=
  sourceUnitAccepted? viewBlockTimestampSource

def pureBlockTimestampSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureBlockTimestamp"
            items :=
              [ Solidity.ContractItem.function
                  { viewBlockTimestampFunction with
                    name := some "pureBlockTime"
                    mutability :=
                      Solidity.StateMutability.pure } ] } ] }

def pureBlockTimestampRejected : Bool :=
  Result.isError (SourceUnit.check pureBlockTimestampSource)

def viewAmbientBuiltinsFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "ambient"
    mutability := Solidity.StateMutability.view
    returns :=
      [ { name := some "blockHash"
          ty := Solidity.Ty.bytesN 32
          location := none }
      , { name := some "blobHash"
          ty := Solidity.Ty.bytesN 32
          location := none }
      , { name := some "remainingGas"
          ty := uint256
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "blockhash")
                    [Solidity.Arg.positional
                      (numberExpr "7")])
              , Solidity.TupleItem.value
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "blobhash")
                    [Solidity.Arg.positional
                      (numberExpr "1")])
              , Solidity.TupleItem.value
                  (Solidity.Expr.call
                    (Solidity.Expr.ident "gasleft")
                    []) ]))) }

def viewAmbientBuiltinsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewAmbientBuiltins"
            items :=
              [Solidity.ContractItem.function
                viewAmbientBuiltinsFunction] } ] }

def viewAmbientBuiltinsAccepted : Bool :=
  sourceUnitAccepted? viewAmbientBuiltinsSource

def viewAmbientBuiltinsPreCancunRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.shanghai
      viewAmbientBuiltinsSource)

def preParisRandaoAliasSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PreParisRandaoAlias"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "randao"
                    returns :=
                      [ { name := none, ty := uint256, location := none }
                      , { name := none, ty := uint256, location := none } ]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident "block")
                                    "difficulty")
                              , Solidity.TupleItem.value
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident "block")
                                    "prevrandao") ]))) } ] } ] }

def preParisRandaoAliasAccepted : Bool :=
  Result.isOk
    (SourceUnit.checkWithEvmVersion EvmVersion.london
      preParisRandaoAliasSource)

def blobbasefeeFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "blobbasefee"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "block") "blobbasefee"))) }

def blobbasefeeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Blobbasefee"
            items :=
              [Solidity.ContractItem.function
                blobbasefeeFunction] } ] }

def blobbasefeePreCancunRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.shanghai
      blobbasefeeSource)

def basefeeFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "basefee"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "block") "basefee"))) }

def basefeeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Basefee"
            items :=
              [Solidity.ContractItem.function
                basefeeFunction] } ] }

def basefeeAccepted : Bool :=
  sourceUnitAccepted? basefeeSource

def basefeePreLondonRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.berlin
      basefeeSource)

def chainidFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "chainid"
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.ident "block") "chainid"))) }

def chainidSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Chainid"
            items :=
              [Solidity.ContractItem.function
                chainidFunction] } ] }

def chainidAccepted : Bool :=
  sourceUnitAccepted? chainidSource

def chainidPreIstanbulRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.petersburg
      chainidSource)

def addressCodehashFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "codehash"
    returns :=
      [{ name := none
         ty := Solidity.Ty.bytesN 32
         location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.member
              (Solidity.Expr.literal
                (Solidity.Literal.address 0xbeef))
              "codehash"))) }

def addressCodehashSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddressCodehash"
            items :=
              [Solidity.ContractItem.function
                addressCodehashFunction] } ] }

def addressCodehashAccepted : Bool :=
  sourceUnitAccepted? addressCodehashSource

def addressCodehashPreConstantinopleRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.byzantium
      addressCodehashSource)

def saltedConstructorCreatePreConstantinopleRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.byzantium
      saltedConstructorCreateSource)

def transientStoragePreCancunRejected : Bool :=
  Result.isError
    (SourceUnit.checkWithEvmVersion EvmVersion.shanghai
      (sourceUnitForContractDecl
        Solidity.Executable.Examples.transientStorageContract))

def evmVersionBuiltinDisciplineAccepted : Bool :=
  viewAmbientBuiltinsAccepted &&
    preParisRandaoAliasAccepted &&
    basefeeAccepted &&
    chainidAccepted &&
    addressCodehashAccepted &&
    saltedConstructorCreateAccepted

def evmVersionBuiltinDisciplineRejected : Bool :=
  viewAmbientBuiltinsPreCancunRejected &&
    blobbasefeePreCancunRejected &&
    basefeePreLondonRejected &&
    chainidPreIstanbulRejected &&
    addressCodehashPreConstantinopleRejected &&
    saltedConstructorCreatePreConstantinopleRejected &&
    transientStoragePreCancunRejected

def pureGasleftFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "remainingGas"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "gasleft")
              []))) }

def pureGasleftSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureGasleft"
            items :=
              [Solidity.ContractItem.function
                pureGasleftFunction] } ] }

def pureGasleftRejected : Bool :=
  Result.isError (SourceUnit.check pureGasleftSource)

def pureBlockhashFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "blockHash"
    returns :=
      [{ name := none
         ty := Solidity.Ty.bytesN 32
         location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "blockhash")
              [Solidity.Arg.positional
                (numberExpr "7")]))) }

def pureBlockhashSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureBlockhash"
            items :=
              [Solidity.ContractItem.function
                pureBlockhashFunction] } ] }

def pureBlockhashRejected : Bool :=
  Result.isError (SourceUnit.check pureBlockhashSource)

def badBlockhashArgFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badBlockHashArg"
    returns :=
      [{ name := none
         ty := Solidity.Ty.bytesN 32
         location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "blockhash")
              [Solidity.Arg.positional
                (boolExpr true)]))) }

def badBlockhashArgSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBlockhashArg"
            items :=
              [Solidity.ContractItem.function
                badBlockhashArgFunction] } ] }

def badBlockhashArgRejected : Bool :=
  Result.isError (SourceUnit.check badBlockhashArgSource)

def signedBlockhashArgFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "signedBlockHashArg"
    params := [{ name := some "n", ty := int256, location := none }]
    returns :=
      [{ name := none
         ty := Solidity.Ty.bytesN 32
         location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "blockhash")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "n")]))) }

def signedBlockhashArgSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SignedBlockhashArg"
            items :=
              [Solidity.ContractItem.function
                signedBlockhashArgFunction] } ] }

def signedBlockhashArgRejected : Bool :=
  Result.isError (SourceUnit.check signedBlockhashArgSource)

def signedBlobhashArgFunction : Solidity.FunctionDecl :=
  { signedBlockhashArgFunction with
    name := some "signedBlobHashArg"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "blobhash")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "n")]))) }

def signedBlobhashArgSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SignedBlobhashArg"
            items :=
              [Solidity.ContractItem.function
                signedBlobhashArgFunction] } ] }

def signedBlobhashArgRejected : Bool :=
  Result.isError (SourceUnit.check signedBlobhashArgSource)

def viewAddressEnvMembersFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "accountInfo"
    mutability := Solidity.StateMutability.view
    returns :=
      [ { name := none, ty := uint256, location := none }
      , { name := none, ty := uint256, location := none }
      , { name := none
          ty := Solidity.Ty.bytesN 32
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value
                  (Solidity.Expr.member
                    (Solidity.Expr.literal
                      (Solidity.Literal.address 0xbeef))
                    "balance")
              , Solidity.TupleItem.value
                  (Solidity.Expr.member
                    (Solidity.Expr.member
                      (Solidity.Expr.literal
                        (Solidity.Literal.address 0xbeef))
                      "code")
                    "length")
              , Solidity.TupleItem.value
                  (Solidity.Expr.member
                    (Solidity.Expr.literal
                      (Solidity.Literal.address 0xbeef))
                    "codehash") ]))) }

def viewAddressEnvMembersSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ViewAddressEnvMembers"
            items :=
              [Solidity.ContractItem.function
                viewAddressEnvMembersFunction] } ] }

def viewAddressEnvMembersAccepted : Bool :=
  sourceUnitAccepted? viewAddressEnvMembersSource

def pureAddressEnvMembersSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PureAddressEnvMembers"
            items :=
              [ Solidity.ContractItem.function
                  { viewAddressEnvMembersFunction with
                    name := some "pureAccountInfo"
                    mutability :=
                      Solidity.StateMutability.pure } ] } ] }

def pureAddressEnvMembersRejected : Bool :=
  Result.isError (SourceUnit.check pureAddressEnvMembersSource)

def nonAddressMemberReceiverSource
    (target : Solidity.ContractDecl) (readerName member : Name)
    (returnTy : Ty) (returnLocation : Option Solidity.DataLocation) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract target
      , Solidity.SourceItem.contract
          { name := readerName
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "bad"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.user
                            (userPath target.name) } ]
                    returns :=
                      [ { name := none
                          ty := returnTy
                          location := returnLocation } ]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "target")
                              member))) } ] } ] }

def contractBalanceMemberSource : Solidity.SourceUnit :=
  nonAddressMemberReceiverSource { name := "BalanceTarget" }
    "ContractBalanceReader" "balance" uint256 none

def contractCodeMemberSource : Solidity.SourceUnit :=
  nonAddressMemberReceiverSource { name := "CodeTargetMember" }
    "ContractCodeReader" "code" Solidity.Ty.bytes
    (some Solidity.DataLocation.memory)

def contractCodehashMemberSource : Solidity.SourceUnit :=
  nonAddressMemberReceiverSource { name := "CodehashTarget" }
    "ContractCodehashReader" "codehash"
    (Solidity.Ty.bytesN 32) none

def libraryConversionMemberSource (libraryName readerName member : Name)
    (returnTy : Ty) (returnLocation : Option Solidity.DataLocation) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := libraryName }
      , Solidity.SourceItem.contract
          { name := readerName
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "bad"
                    params :=
                      [ { name := some "target"
                          ty := Solidity.Ty.address false } ]
                    returns :=
                      [ { name := none
                          ty := returnTy
                          location := returnLocation } ]
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.call
                                (Solidity.Expr.typeName
                                  (Solidity.Ty.user
                                    (userPath libraryName)))
                                [Solidity.Arg.positional
                                  (Solidity.Expr.ident "target")])
                              member))) } ] } ] }

def libraryBalanceMemberSource : Solidity.SourceUnit :=
  libraryConversionMemberSource "BalanceLibrary"
    "LibraryBalanceReader" "balance" uint256 none

def libraryCodeMemberSource : Solidity.SourceUnit :=
  libraryConversionMemberSource "CodeLibraryMember"
    "LibraryCodeReader" "code" Solidity.Ty.bytes
    (some Solidity.DataLocation.memory)

def libraryCodehashMemberSource : Solidity.SourceUnit :=
  libraryConversionMemberSource "CodehashLibrary"
    "LibraryCodehashReader" "codehash"
    (Solidity.Ty.bytesN 32) none

def addressEnvironmentMemberReceiverDisciplineMatches : Bool :=
  viewAddressEnvMembersAccepted &&
    Result.isError (SourceUnit.check contractBalanceMemberSource) &&
    Result.isError (SourceUnit.check contractCodeMemberSource) &&
    Result.isError (SourceUnit.check contractCodehashMemberSource) &&
    Result.isError (SourceUnit.check libraryBalanceMemberSource) &&
    Result.isError (SourceUnit.check libraryCodeMemberSource) &&
    Result.isError (SourceUnit.check libraryCodehashMemberSource)

def uint8 : Ty := Solidity.Ty.uint 8

def uint16 : Ty := Solidity.Ty.uint 16

def uint32 : Ty := Solidity.Ty.uint 32

def int8 : Ty := Solidity.Ty.int 8

def int16 : Ty := Solidity.Ty.int 16

def bytes2 : Ty := Solidity.Ty.bytesN 2

def bytes4 : Ty := Solidity.Ty.bytesN 4

def bytes32 : Ty := Solidity.Ty.bytesN 32

def addressTy : Ty := Solidity.Ty.address false

def payableAddressTy : Ty := Solidity.Ty.address true

def fixed8x1 : Ty := Solidity.Ty.fixed 8 1

def fixed16x2 : Ty := Solidity.Ty.fixed 16 2

def fixed128x18 : Ty := Solidity.Ty.fixed 128 18

def ufixed8x1 : Ty := Solidity.Ty.ufixed 8 1

def ufixed128x18 : Ty := Solidity.Ty.ufixed 128 18

def oneExpr : Solidity.Expr :=
  Solidity.Expr.literal (Solidity.Literal.number "1")

def zeroExpr : Solidity.Expr :=
  Solidity.Expr.literal (Solidity.Literal.number "0")

def zeroBySubExpr : Solidity.Expr :=
  Solidity.Expr.binary
    Solidity.BinaryOp.sub oneExpr oneExpr

def fixedPointArithmeticFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "mixFixed"
    params :=
      [ { name := some "a", ty := fixed16x2, location := none }
      , { name := some "b", ty := ufixed8x1, location := none } ]
    returns := [{ name := none, ty := fixed16x2, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.add
              (Solidity.Expr.ident "a")
              (Solidity.Expr.ident "b")))) }

def fixedPointLiteralFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "literalFixed"
    returns := [{ name := none, ty := fixed128x18, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (numberExpr "1.25"))) }

def fixedPointSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType
          { name := "Wad", underlying := fixed128x18 }
      , Solidity.SourceItem.contract
          { name := "FixedPointSurface"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "rates"
                    ty := Solidity.Ty.mapping fixed128x18 uint256 }
              , Solidity.ContractItem.stateVar
                  { name := "plain", ty := ufixed128x18 } ] } ] }

def fixedPointSourceAccepted : Bool :=
  sourceUnitAccepted? fixedPointSource

def fixedPointUnusedLocalFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "unusedLocal"
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "x"
                  ty := some fixed128x18
                  location := none } ] none
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def fixedPointUnusedLocalSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FixedPointUnusedLocal"
            items :=
              [Solidity.ContractItem.function
                fixedPointUnusedLocalFunction] } ] }

def fixedPointUnusedLocalAccepted : Bool :=
  sourceUnitAccepted? fixedPointUnusedLocalSource

def fixedPointAbiCanonicalMatches : Bool :=
  TypeContext.abiCanonical? TypeContext.empty fixed128x18 ==
      some "fixed128x18" &&
    TypeContext.abiCanonical? TypeContext.empty ufixed8x1 ==
      some "ufixed8x1"

def fixedPointExecutableTypeRejected : Bool :=
  match Solidity.Executable.Ty.toCore? fixed128x18 with
  | none => true
  | some _ => false

def fixedPointArithmeticSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointArithmetic"
            items :=
              [ Solidity.ContractItem.function
                  fixedPointArithmeticFunction ] } ] }

def fixedPointLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointLiteral"
            items :=
              [ Solidity.ContractItem.function
                  fixedPointLiteralFunction ] } ] }

def fixedPointStateInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointStateInit"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := fixed128x18
                    init := some (numberExpr "1.25") } ] } ] }

def fixedPointPublicGetterSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointPublicGetter"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "x"
                    ty := fixed128x18
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def fixedPointLocalInitFunction : Solidity.FunctionDecl :=
  { fixedPointUnusedLocalFunction with
    name := some "badLocalInit"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "x"
                  ty := some fixed128x18
                  location := none } ]
              (some (numberExpr "1.25"))
          , Solidity.Stmt.returnValues
              (some (numberExpr "1")) ]) }

def fixedPointLocalInitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointLocalInit"
            items :=
              [ Solidity.ContractItem.function
                  fixedPointLocalInitFunction ] } ] }

def badFixedPointBitsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointBits"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "bad"
                    ty := Solidity.Ty.fixed 7 1 } ] } ] }

def badFixedPointDecimalsSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointDecimals"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "bad"
                    ty := Solidity.Ty.ufixed 128 81 } ] } ] }

def badFixedPointImplicitFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badImplicit"
    params := [{ name := some "a", ty := ufixed8x1, location := none }]
    returns := [{ name := none, ty := fixed8x1, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "a"))) }

def badFixedPointImplicitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointImplicit"
            items :=
              [ Solidity.ContractItem.function
                  badFixedPointImplicitFunction ] } ] }

def badFixedPointBitwiseFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badBitwise"
    params :=
      [ { name := some "a", ty := fixed128x18, location := none }
      , { name := some "b", ty := fixed128x18, location := none } ]
    returns := [{ name := none, ty := fixed128x18, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.bitAnd
              (Solidity.Expr.ident "a")
              (Solidity.Expr.ident "b")))) }

def badFixedPointBitwiseSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFixedPointBitwise"
            items :=
              [ Solidity.ContractItem.function
                  badFixedPointBitwiseFunction ] } ] }

def fixedPointSourceDisciplineAccepted : Bool :=
  fixedPointSourceAccepted &&
    fixedPointUnusedLocalAccepted &&
    fixedPointAbiCanonicalMatches &&
    fixedPointExecutableTypeRejected

def fixedPointSourceDisciplineRejected : Bool :=
  Result.isError (SourceUnit.check badFixedPointBitsSource) &&
    Result.isError (SourceUnit.check badFixedPointDecimalsSource) &&
    Result.isError (SourceUnit.check fixedPointArithmeticSource) &&
    Result.isError (SourceUnit.check fixedPointLiteralSource) &&
    Result.isError (SourceUnit.check fixedPointStateInitSource) &&
    Result.isError (SourceUnit.check fixedPointPublicGetterSource) &&
    Result.isError (SourceUnit.check fixedPointLocalInitSource) &&
    Result.isError (SourceUnit.check badFixedPointImplicitSource) &&
    Result.isError (SourceUnit.check badFixedPointBitwiseSource)

def int8OneExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName int8)
    [Solidity.Arg.positional oneExpr]

def uint8OneExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName uint8)
    [Solidity.Arg.positional oneExpr]

def badWidthAndSignCastExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName uint16)
    [Solidity.Arg.positional
      (Solidity.Expr.ident "x")]

def uint160OneExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName (Solidity.Ty.uint 160))
    [Solidity.Arg.positional oneExpr]

def uint160ZeroExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName (Solidity.Ty.uint 160))
    [Solidity.Arg.positional zeroExpr]

def addressCastExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName addressTy)
    [Solidity.Arg.positional uint160OneExpr]

def addressUint160ZeroExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName addressTy)
    [Solidity.Arg.positional uint160ZeroExpr]

def literalUint8ReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LiteralUint8"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "small"
                    returns := [{ name := none, ty := uint8, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some oneExpr)) } ] } ] }

def literalUint8Accepted : Bool :=
  sourceUnitAccepted? literalUint8ReturnSource

def takesUint8Function : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesSmall"
    params := [{ name := some "x", ty := uint8, location := none }]
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (Solidity.Expr.ident "x"))) }

def callUint8LiteralFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "callSmall"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesSmall")
              [Solidity.Arg.positional oneExpr]))) }

def callUint8LiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CallUint8Literal"
            items :=
              [ Solidity.ContractItem.function
                  takesUint8Function
              , Solidity.ContractItem.function
                  callUint8LiteralFunction ] } ] }

def callUint8LiteralAccepted : Bool :=
  sourceUnitAccepted? callUint8LiteralSource

def badCallUint8LiteralFunction : Solidity.FunctionDecl :=
  { callUint8LiteralFunction with
    name := some "badCallSmall"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesSmall")
              [Solidity.Arg.positional
                (numberExpr "300")]))) }

def badCallUint8LiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCallUint8Literal"
            items :=
              [ Solidity.ContractItem.function
                  takesUint8Function
              , Solidity.ContractItem.function
                  badCallUint8LiteralFunction ] } ] }

def badCallUint8LiteralRejected : Bool :=
  Result.isError (SourceUnit.check badCallUint8LiteralSource)

def signedBaseUnsignedExponentFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "powSignedBase"
    params :=
      [ { name := some "x", ty := int256, location := none }
      , { name := some "y", ty := uint8, location := none } ]
    returns := [{ name := none, ty := int256, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.exp
              (Solidity.Expr.ident "x")
              (Solidity.Expr.ident "y")))) }

def signedBaseUnsignedExponentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "SignedBaseUnsignedExponent"
            items :=
              [ Solidity.ContractItem.function
                  signedBaseUnsignedExponentFunction ] } ] }

def signedBaseUnsignedExponentAccepted : Bool :=
  sourceUnitAccepted? signedBaseUnsignedExponentSource

def signedExponentFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badSignedExponent"
    params :=
      [ { name := some "x", ty := uint256, location := none }
      , { name := some "y", ty := int8, location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.exp
              (Solidity.Expr.ident "x")
              (Solidity.Expr.ident "y")))) }

def signedExponentSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadSignedExponent"
            items :=
              [ Solidity.ContractItem.function
                  signedExponentFunction ] } ] }

def signedExponentRejected : Bool :=
  Result.isError (SourceUnit.check signedExponentSource)

def uint16TwoExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName uint16)
    [Solidity.Arg.positional (numberExpr "2")]

def arrayLiteralWideningFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "arrayWiden"
    returns :=
      [ { name := none
          ty := Solidity.Ty.array uint16 (some 2)
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [uint8OneExpr, uint16TwoExpr]))) }

def arrayLiteralWideningSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ArrayLiteralWidening"
            items :=
              [Solidity.ContractItem.function
                arrayLiteralWideningFunction] } ] }

def arrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? arrayLiteralWideningSource

def badTypedElementArrayLiteralWideningFunction :
    Solidity.FunctionDecl :=
  { arrayLiteralWideningFunction with
    name := some "badTypedElementArrayWiden"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [uint8OneExpr, numberExpr "2"]))) }

def badTypedElementArrayLiteralWideningSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTypedElementArrayLiteralWidening"
            items :=
              [Solidity.ContractItem.function
                badTypedElementArrayLiteralWideningFunction] } ] }

def badTypedElementArrayLiteralWideningRejected : Bool :=
  Result.isError
    (SourceUnit.check badTypedElementArrayLiteralWideningSource)

def takesUint16ArrayFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesWideArray"
    params :=
      [ { name := some "xs"
          ty := Solidity.Ty.array uint16 (some 2)
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := uint16, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "xs")
              zeroExpr))) }

def badTypedElementArrayLiteralArgumentFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "badTypedElementArrayArg"
    returns := [{ name := none, ty := uint16, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesWideArray")
              [Solidity.Arg.positional
                (Solidity.Expr.array
                  [uint8OneExpr, numberExpr "2"])]))) }

def badTypedElementArrayLiteralArgumentSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTypedElementArrayLiteralArgument"
            items :=
              [ Solidity.ContractItem.function
                  takesUint16ArrayFunction
              , Solidity.ContractItem.function
                  badTypedElementArrayLiteralArgumentFunction ] } ] }

def badTypedElementArrayLiteralArgumentRejected : Bool :=
  Result.isError
    (SourceUnit.check badTypedElementArrayLiteralArgumentSource)

def bytes1TwelveExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 1))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [0x12]))]

def bytes2ThirtyFourExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.bytesN 2))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [0x34, 0x56]))]

def fixedBytesArrayLiteralWideningFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "fixedBytesArrayWiden"
    returns :=
      [ { name := none
          ty :=
            Solidity.Ty.array
              (Solidity.Ty.bytesN 2) (some 2)
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [bytes1TwelveExpr, bytes2ThirtyFourExpr]))) }

def fixedBytesArrayLiteralWideningSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FixedBytesArrayLiteralWidening"
            items :=
              [Solidity.ContractItem.function
                fixedBytesArrayLiteralWideningFunction] } ] }

def fixedBytesArrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? fixedBytesArrayLiteralWideningSource

def legacyFixedBytes1TwelveExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.fixedBytes 1))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [0x12]))]

def legacyFixedBytes2ThirtyFourExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName
      (Solidity.Ty.fixedBytes 2))
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [0x34, 0x56]))]

def legacyFixedBytesArrayLiteralWideningFunction :
    Solidity.FunctionDecl :=
  { fixedBytesArrayLiteralWideningFunction with
    name := some "legacyFixedBytesArrayWiden"
    returns :=
      [ { name := none
          ty :=
            Solidity.Ty.array
              (Solidity.Ty.fixedBytes 2) (some 2)
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [ legacyFixedBytes1TwelveExpr
              , legacyFixedBytes2ThirtyFourExpr ]))) }

def legacyFixedBytesArrayLiteralWideningSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "LegacyFixedBytesArrayLiteralWidening"
            items :=
              [Solidity.ContractItem.function
                legacyFixedBytesArrayLiteralWideningFunction] } ] }

def legacyFixedBytesArrayLiteralWideningAccepted : Bool :=
  sourceUnitAccepted? legacyFixedBytesArrayLiteralWideningSource

def badArrayLiteralCommonTypeFunction :
    Solidity.FunctionDecl :=
  { arrayLiteralWideningFunction with
    name := some "badArrayCommon"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [uint8OneExpr, boolExpr true]))) }

def badArrayLiteralCommonTypeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadArrayLiteralCommonType"
            items :=
              [Solidity.ContractItem.function
                badArrayLiteralCommonTypeFunction] } ] }

def badArrayLiteralCommonTypeRejected : Bool :=
  Result.isError (SourceUnit.check badArrayLiteralCommonTypeSource)

def untypedNarrowArrayLiteralReturnFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "untypedNarrowArrayReturn"
    returns :=
      [ { name := none
          ty := Solidity.Ty.array uint8 (some 2)
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [numberExpr "1", numberExpr "2"]))) }

def untypedNarrowArrayLiteralReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UntypedNarrowArrayLiteralReturn"
            items :=
              [Solidity.ContractItem.function
                untypedNarrowArrayLiteralReturnFunction] } ] }

def untypedNarrowArrayLiteralReturnAccepted : Bool :=
  sourceUnitAccepted? untypedNarrowArrayLiteralReturnSource

def untypedNarrowArrayLiteralLocalFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "untypedNarrowArrayLocal"
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "xs"
                  ty := some (Solidity.Ty.array uint8 (some 2))
                  location := some Solidity.DataLocation.memory } ]
              (some
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "2"]))
          , Solidity.Stmt.returnValues
              (some (numberExpr "0")) ]) }

def untypedNarrowArrayLiteralLocalSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UntypedNarrowArrayLiteralLocal"
            items :=
              [Solidity.ContractItem.function
                untypedNarrowArrayLiteralLocalFunction] } ] }

def untypedNarrowArrayLiteralLocalAccepted : Bool :=
  sourceUnitAccepted? untypedNarrowArrayLiteralLocalSource

def untypedNarrowArrayLiteralOverflowFunction :
    Solidity.FunctionDecl :=
  { untypedNarrowArrayLiteralReturnFunction with
    name := some "untypedNarrowArrayOverflow"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.array
              [numberExpr "1", numberExpr "300"]))) }

def untypedNarrowArrayLiteralOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UntypedNarrowArrayLiteralOverflow"
            items :=
              [Solidity.ContractItem.function
                untypedNarrowArrayLiteralOverflowFunction] } ] }

def untypedNarrowArrayLiteralOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    untypedNarrowArrayLiteralOverflowSource)

def contextualArrayLiteralArgCallee :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takesNarrowArray"
    returns := [{ name := none, ty := uint8, location := none }]
    params :=
      [ { name := some "xs"
          ty := Solidity.Ty.array uint8 (some 2)
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "xs")
              (numberExpr "0")))) }

def contextualArrayLiteralArgCaller :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "contextualArrayArg"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesNarrowArray")
              [Solidity.Arg.positional
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "2"])]))) }

def contextualArrayLiteralArgSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralArg"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  contextualArrayLiteralArgCaller ] } ] }

def contextualArrayLiteralArgAccepted : Bool :=
  sourceUnitAccepted? contextualArrayLiteralArgSource

def contextualArrayLiteralArgOverflowCaller :
    Solidity.FunctionDecl :=
  { contextualArrayLiteralArgCaller with
    name := some "contextualArrayArgOverflow"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesNarrowArray")
              [Solidity.Arg.positional
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "300"])]))) }

def contextualArrayLiteralArgOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralArgOverflow"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  contextualArrayLiteralArgOverflowCaller ] } ] }

def contextualArrayLiteralArgOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayLiteralArgOverflowSource)

def contextualNamedArrayLiteralArgCaller :
    Solidity.FunctionDecl :=
  { contextualArrayLiteralArgCaller with
    name := some "contextualNamedArrayArg"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesNarrowArray")
              [Solidity.Arg.named "xs"
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "2"])]))) }

def contextualNamedArrayLiteralArgSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralArg"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  contextualNamedArrayLiteralArgCaller ] } ] }

def contextualNamedArrayLiteralArgAccepted : Bool :=
  sourceUnitAccepted? contextualNamedArrayLiteralArgSource

def contextualNamedArrayLiteralArgOverflowCaller :
    Solidity.FunctionDecl :=
  { contextualNamedArrayLiteralArgCaller with
    name := some "contextualNamedArrayArgOverflow"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesNarrowArray")
              [Solidity.Arg.named "xs"
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "300"])]))) }

def contextualNamedArrayLiteralArgOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralArgOverflow"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  contextualNamedArrayLiteralArgOverflowCaller ] } ] }

def contextualNamedArrayLiteralArgOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualNamedArrayLiteralArgOverflowSource)

def contextualUsingArrayLiteralArgLibraryFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takeUsingArray"
    visibility := some Solidity.Visibility.internal_
    mutability := Solidity.StateMutability.pure
    params :=
      [ { name := some "self", ty := uint256, location := none }
      , { name := some "xs"
          ty := Solidity.Ty.array uint8 (some 2)
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "xs")
              (numberExpr "0")))) }

def contextualUsingArrayLiteralArgLibrary :
    Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "ContextualUsingArrayLib"
    items :=
      [Solidity.ContractItem.function
        contextualUsingArrayLiteralArgLibraryFunction] }

def contextualUsingArrayLiteralArgCaller :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "contextualUsingArrayArg"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (numberExpr "1") "takeUsingArray")
              [Solidity.Arg.positional
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "2"])]))) }

def contextualUsingArrayLiteralArgSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualUsingArrayLiteralArgLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "ContextualUsingArrayLib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ContextualUsingArrayArg"
            items :=
              [Solidity.ContractItem.function
                contextualUsingArrayLiteralArgCaller] } ] }

def contextualUsingArrayLiteralArgAccepted : Bool :=
  sourceUnitAccepted? contextualUsingArrayLiteralArgSource

def contextualUsingArrayLiteralArgOverflowCaller :
    Solidity.FunctionDecl :=
  { contextualUsingArrayLiteralArgCaller with
    name := some "contextualUsingArrayArgOverflow"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (numberExpr "1") "takeUsingArray")
              [Solidity.Arg.positional
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "300"])]))) }

def contextualUsingArrayLiteralArgOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualUsingArrayLiteralArgLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "ContextualUsingArrayLib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ContextualUsingArrayArgOverflow"
            items :=
              [Solidity.ContractItem.function
                contextualUsingArrayLiteralArgOverflowCaller] } ] }

def contextualUsingArrayLiteralArgOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualUsingArrayLiteralArgOverflowSource)

def contextualUsingNamedArrayLiteralArgCaller :
    Solidity.FunctionDecl :=
  { contextualUsingArrayLiteralArgCaller with
    name := some "contextualUsingNamedArrayArg"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (numberExpr "1") "takeUsingArray")
              [Solidity.Arg.named "xs"
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "2"])]))) }

def contextualUsingNamedArrayLiteralArgSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualUsingArrayLiteralArgLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "ContextualUsingArrayLib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ContextualUsingNamedArrayArg"
            items :=
              [Solidity.ContractItem.function
                contextualUsingNamedArrayLiteralArgCaller] } ] }

def contextualUsingNamedArrayLiteralArgAccepted : Bool :=
  sourceUnitAccepted? contextualUsingNamedArrayLiteralArgSource

def contextualUsingNamedArrayLiteralArgOverflowCaller :
    Solidity.FunctionDecl :=
  { contextualUsingNamedArrayLiteralArgCaller with
    name := some "contextualUsingNamedArrayArgOverflow"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (numberExpr "1") "takeUsingArray")
              [Solidity.Arg.named "xs"
                (Solidity.Expr.array
                  [numberExpr "1", numberExpr "300"])]))) }

def contextualUsingNamedArrayLiteralArgOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualUsingArrayLiteralArgLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "ContextualUsingArrayLib"
            target := some uint256 }
      , Solidity.SourceItem.contract
          { name := "ContextualUsingNamedArrayArgOverflow"
            items :=
              [Solidity.ContractItem.function
                contextualUsingNamedArrayLiteralArgOverflowCaller] } ] }

def contextualUsingNamedArrayLiteralArgOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualUsingNamedArrayLiteralArgOverflowSource)

def contextualNarrowArrayTy : Ty :=
  Solidity.Ty.array uint8 (some 2)

def contextualNarrowArrayExpr : Solidity.Expr :=
  Solidity.Expr.array [numberExpr "1", numberExpr "2"]

def contextualNarrowArrayOverflowExpr : Solidity.Expr :=
  Solidity.Expr.array [numberExpr "1", numberExpr "300"]

def contextualNarrowArraySecondExpr : Solidity.Expr :=
  Solidity.Expr.array [numberExpr "3", numberExpr "4"]

def emptyArrayLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EmptyArrayLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badEmptyArrayLiteral"
                    returns :=
                      [ { name := none
                          ty := uintArrayTy
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some (Solidity.Expr.array []))) } ] } ] }

def emptyArrayLiteralRejected : Bool :=
  Result.isError (SourceUnit.check emptyArrayLiteralSource)

def mixedArrayLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MixedArrayLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badMixedArrayLiteral"
                    returns :=
                      [ { name := none
                          ty := uintArrayTy
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.array
                              [ numberExpr "1"
                              , boolExpr true ]))) } ] } ] }

def mixedArrayLiteralRejected : Bool :=
  Result.isError (SourceUnit.check mixedArrayLiteralSource)

def arrayLiteralAcceptednessDisciplineMatches : Bool :=
  emptyArrayLiteralRejected && mixedArrayLiteralRejected

def contextualArrayTupleReturnFunction
    (name : Name) (first : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    returns :=
      [ { name := none
          ty := contextualNarrowArrayTy
          location := some Solidity.DataLocation.memory }
      , { name := none
          ty := contextualNarrowArrayTy
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.tuple
              [ Solidity.TupleItem.value first
              , Solidity.TupleItem.value
                  contextualNarrowArraySecondExpr ]))) }

def contextualArrayTupleReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTupleReturn"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTupleReturnFunction
                    "returnArrayTuple" contextualNarrowArrayExpr) ] } ] }

def contextualArrayTupleReturnAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTupleReturnSource

def contextualArrayTupleReturnOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTupleReturnOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTupleReturnFunction
                    "returnArrayTupleOverflow"
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayTupleReturnOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTupleReturnOverflowSource)

def contextualArrayTupleAssignmentFunction
    (name : Name) (first : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    returns :=
      [ { name := some "a"
          ty := contextualNarrowArrayTy
          location := some Solidity.DataLocation.memory }
      , { name := some "b"
          ty := contextualNarrowArrayTy
          location := some Solidity.DataLocation.memory } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.ident "a")
                  , Solidity.TupleItem.value
                      (Solidity.Expr.ident "b") ])
                Solidity.AssignOp.assign
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value first
                  , Solidity.TupleItem.value
                      contextualNarrowArraySecondExpr ]))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.ident "a")
                  , Solidity.TupleItem.value
                      (Solidity.Expr.ident "b") ])) ]) }

def contextualArrayTupleAssignmentSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTupleAssignment"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTupleAssignmentFunction
                    "assignArrayTuple" contextualNarrowArrayExpr) ] } ] }

def contextualArrayTupleAssignmentAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTupleAssignmentSource

def contextualArrayTupleAssignmentOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTupleAssignmentOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTupleAssignmentFunction
                    "assignArrayTupleOverflow"
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayTupleAssignmentOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTupleAssignmentOverflowSource)

def contextualArrayTernaryFlagParam : Solidity.Parameter :=
  { name := some "flag"
    ty := Solidity.Ty.bool
    location := none }

def contextualArrayTernaryExpr
    (first : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.ternary
    (Solidity.Expr.ident "flag")
    first
    contextualNarrowArraySecondExpr

def contextualArrayAssignmentFunction
    (name : Name) (params : List Solidity.Parameter)
    (rhs : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params := params
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "xs"
                  ty := some contextualNarrowArrayTy
                  location := some Solidity.DataLocation.memory } ]
              none
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "xs")
                Solidity.AssignOp.assign
                rhs)
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.index
                  (Solidity.Expr.ident "xs")
                  (numberExpr "0"))) ]) }

def contextualArrayAssignmentSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayAssignment"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayAssignmentFunction
                    "assignArray" [] contextualNarrowArrayExpr) ] } ] }

def contextualArrayAssignmentAccepted : Bool :=
  sourceUnitAccepted? contextualArrayAssignmentSource

def contextualArrayAssignmentOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayAssignmentOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayAssignmentFunction
                    "assignArrayOverflow" []
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayAssignmentOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayAssignmentOverflowSource)

def contextualArrayTernaryAssignmentSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryAssignment"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayAssignmentFunction
                    "assignTernaryArray"
                    [contextualArrayTernaryFlagParam]
                    (contextualArrayTernaryExpr
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayTernaryAssignmentAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTernaryAssignmentSource

def contextualArrayTernaryAssignmentOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryAssignmentOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayAssignmentFunction
                    "assignTernaryArrayOverflow"
                    [contextualArrayTernaryFlagParam]
                    (contextualArrayTernaryExpr
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayTernaryAssignmentOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTernaryAssignmentOverflowSource)

def contextualArrayTernaryLocalFunction
    (name : Name) (first : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params := [contextualArrayTernaryFlagParam]
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "xs"
                  ty := some contextualNarrowArrayTy
                  location := some Solidity.DataLocation.memory } ]
              (some (contextualArrayTernaryExpr first))
          , Solidity.Stmt.returnValues
              (some (numberExpr "0")) ]) }

def contextualArrayTernaryLocalSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryLocal"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTernaryLocalFunction
                    "ternaryLocal" contextualNarrowArrayExpr) ] } ] }

def contextualArrayTernaryLocalAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTernaryLocalSource

def contextualArrayTernaryLocalOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryLocalOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTernaryLocalFunction
                    "ternaryLocalOverflow"
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayTernaryLocalOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTernaryLocalOverflowSource)

def contextualArrayTernaryReturnFunction
    (name : Name) (first : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params := [contextualArrayTernaryFlagParam]
    returns :=
      [{ name := none
         ty := contextualNarrowArrayTy
         location := some Solidity.DataLocation.memory }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (contextualArrayTernaryExpr first))) }

def contextualArrayTernaryReturnSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryReturn"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTernaryReturnFunction
                    "ternaryReturn" contextualNarrowArrayExpr) ] } ] }

def contextualArrayTernaryReturnAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTernaryReturnSource

def contextualArrayTernaryReturnOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryReturnOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayTernaryReturnFunction
                    "ternaryReturnOverflow"
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayTernaryReturnOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTernaryReturnOverflowSource)

def contextualArrayTernaryArgFunction
    (name : Name) (first : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { contextualArrayLiteralArgCaller with
    name := some name
    params := [contextualArrayTernaryFlagParam]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "takesNarrowArray")
              [ Solidity.Arg.positional
                  (contextualArrayTernaryExpr first) ]))) }

def contextualArrayTernaryArgSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryArg"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  (contextualArrayTernaryArgFunction
                    "ternaryArg" contextualNarrowArrayExpr) ] } ] }

def contextualArrayTernaryArgAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTernaryArgSource

def contextualArrayTernaryArgOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayTernaryArgOverflow"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayLiteralArgCallee
              , Solidity.ContractItem.function
                  (contextualArrayTernaryArgFunction
                    "ternaryArgOverflow"
                    contextualNarrowArrayOverflowExpr) ] } ] }

def contextualArrayTernaryArgOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTernaryArgOverflowSource)

def contextualArrayStruct : Solidity.StructDecl :=
  { name := "ContextualArrayStruct"
    fields :=
      [{ name := "xs"
         ty := contextualNarrowArrayTy }] }

def contextualArrayStructTy : Ty :=
  Solidity.Ty.user (userPath "ContextualArrayStruct")

def contextualArrayStructConstructorFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.member
                (Solidity.Expr.call
                  (Solidity.Expr.typeName
                    contextualArrayStructTy)
                  [arg])
                "xs")
              (numberExpr "0")))) }

def contextualArrayStructConstructorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          contextualArrayStruct
      , Solidity.SourceItem.contract
          { name := "ContextualArrayStructCtor"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayStructConstructorFunction
                    "structArrayArg"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayStructConstructorAccepted : Bool :=
  sourceUnitAccepted? contextualArrayStructConstructorSource

def contextualArrayStructConstructorOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          contextualArrayStruct
      , Solidity.SourceItem.contract
          { name := "ContextualArrayStructCtorOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayStructConstructorFunction
                    "structArrayArgOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayStructConstructorOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayStructConstructorOverflowSource)

def contextualNamedArrayStructConstructorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          contextualArrayStruct
      , Solidity.SourceItem.contract
          { name := "ContextualNamedArrayStructCtor"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayStructConstructorFunction
                    "structNamedArrayArg"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayExpr)) ] } ] }

def contextualNamedArrayStructConstructorAccepted : Bool :=
  sourceUnitAccepted? contextualNamedArrayStructConstructorSource

def contextualNamedArrayStructConstructorOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct
          contextualArrayStruct
      , Solidity.SourceItem.contract
          { name := "ContextualNamedArrayStructCtorOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayStructConstructorFunction
                    "structNamedArrayArgOverflow"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualNamedArrayStructConstructorOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualNamedArrayStructConstructorOverflowSource)

def contextualArrayLiteralEventDecl :
    Solidity.EventDecl :=
  { name := "NarrowArrayEvent"
    params :=
      [{ name := some "xs"
         ty := contextualNarrowArrayTy
         indexed := false }] }

def contextualArrayLiteralEventFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.emitEvent
              (Solidity.Expr.call
                (Solidity.Expr.ident "NarrowArrayEvent")
                [arg])
          , Solidity.Stmt.returnValues
              (some (numberExpr "7")) ]) }

def contextualArrayLiteralEventSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralEvent"
            items :=
              [ Solidity.ContractItem.eventDecl
                  contextualArrayLiteralEventDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralEventFunction
                    "eventArrayArg"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayLiteralEventAccepted : Bool :=
  sourceUnitAccepted? contextualArrayLiteralEventSource

def contextualArrayLiteralEventOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralEventOverflow"
            items :=
              [ Solidity.ContractItem.eventDecl
                  contextualArrayLiteralEventDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralEventFunction
                    "eventArrayArgOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayLiteralEventOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayLiteralEventOverflowSource)

def contextualNamedArrayLiteralEventSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralEvent"
            items :=
              [ Solidity.ContractItem.eventDecl
                  contextualArrayLiteralEventDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralEventFunction
                    "eventNamedArrayArg"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayExpr)) ] } ] }

def contextualNamedArrayLiteralEventAccepted : Bool :=
  sourceUnitAccepted? contextualNamedArrayLiteralEventSource

def contextualNamedArrayLiteralEventOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralEventOverflow"
            items :=
              [ Solidity.ContractItem.eventDecl
                  contextualArrayLiteralEventDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralEventFunction
                    "eventNamedArrayArgOverflow"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualNamedArrayLiteralEventOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualNamedArrayLiteralEventOverflowSource)

def contextualArrayLiteralErrorDecl :
    Solidity.ErrorDecl :=
  { name := "NarrowArrayError"
    params :=
      [{ name := some "xs"
         ty := contextualNarrowArrayTy
         location := none }] }

def contextualArrayLiteralErrorFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    body :=
      some
        (Solidity.Stmt.revertCall
          (Solidity.Expr.call
            (Solidity.Expr.ident "NarrowArrayError")
            [arg])) }

def contextualArrayLiteralErrorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralError"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralErrorFunction
                    "errorArrayArg"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayLiteralErrorAccepted : Bool :=
  sourceUnitAccepted? contextualArrayLiteralErrorSource

def contextualArrayLiteralErrorOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralErrorOverflow"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralErrorFunction
                    "errorArrayArgOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayLiteralErrorOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayLiteralErrorOverflowSource)

def contextualNamedArrayLiteralErrorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralError"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralErrorFunction
                    "errorNamedArrayArg"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayExpr)) ] } ] }

def contextualNamedArrayLiteralErrorAccepted : Bool :=
  sourceUnitAccepted? contextualNamedArrayLiteralErrorSource

def contextualNamedArrayLiteralErrorOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualNamedArrayLiteralErrorOverflow"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralErrorFunction
                    "errorNamedArrayArgOverflow"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualNamedArrayLiteralErrorOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualNamedArrayLiteralErrorOverflowSource)

def contextualArrayLiteralRequireErrorFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.call
                (Solidity.Expr.ident "require")
                [ Solidity.Arg.positional (boolExpr false)
                , Solidity.Arg.positional
                    (Solidity.Expr.call
                      (Solidity.Expr.ident "NarrowArrayError")
                      [arg]) ])
          , Solidity.Stmt.returnValues
              (some (numberExpr "7")) ]) }

def contextualArrayLiteralRequireErrorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralRequireError"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralRequireErrorFunction
                    "requireArrayArg"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayLiteralRequireErrorAccepted : Bool :=
  sourceUnitAccepted? contextualArrayLiteralRequireErrorSource

def contextualArrayLiteralRequireErrorOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralRequireErrorOverflow"
            items :=
              [ Solidity.ContractItem.errorDecl
                  contextualArrayLiteralErrorDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralRequireErrorFunction
                    "requireArrayArgOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayLiteralRequireErrorOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayLiteralRequireErrorOverflowSource)

def contextualArrayLiteralModifierDecl :
    Solidity.ModifierDecl :=
  { name := "narrowArrayMod"
    params :=
      [{ name := some "xs"
         ty := contextualNarrowArrayTy
         location := some Solidity.DataLocation.memory }]
    body := some Solidity.Stmt.modifierPlaceholder }

def contextualArrayLiteralModifierFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    modifiers :=
      [{ target := userPath "narrowArrayMod"
         args := [arg] }] }

def contextualArrayLiteralModifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralModifier"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  contextualArrayLiteralModifierDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralModifierFunction
                    "modifierArrayArg"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayLiteralModifierAccepted : Bool :=
  sourceUnitAccepted? contextualArrayLiteralModifierSource

def contextualArrayLiteralModifierOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ContextualArrayLiteralModifierOverflow"
            items :=
              [ Solidity.ContractItem.modifierDecl
                  contextualArrayLiteralModifierDecl
              , Solidity.ContractItem.function
                  (contextualArrayLiteralModifierFunction
                    "modifierArrayArgOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayLiteralModifierOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayLiteralModifierOverflowSource)

def contextualArrayConstructorTargetTy : Ty :=
  Solidity.Ty.user (userPath "ContextualArrayCtorTarget")

def contextualArrayConstructorTargetContract :
    Solidity.ContractDecl :=
  { name := "ContextualArrayCtorTarget"
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            params :=
              [{ name := some "xs"
                 ty := contextualNarrowArrayTy
                 location := some Solidity.DataLocation.memory }]
            body := some Solidity.Stmt.empty } ] }

def contextualArrayConstructorCreateFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.newExpr
                contextualArrayConstructorTargetTy [arg])
          , Solidity.Stmt.returnValues
              (some (numberExpr "7")) ]) }

def contextualArrayConstructorCreateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualArrayCtorMaker"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayConstructorCreateFunction
                    "makeArrayCtor"
                    (Solidity.Arg.positional
                      contextualNarrowArrayExpr)) ] } ] }

def contextualArrayConstructorCreateAccepted : Bool :=
  sourceUnitAccepted? contextualArrayConstructorCreateSource

def contextualArrayConstructorCreateOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualArrayCtorMakerOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayConstructorCreateFunction
                    "makeArrayCtorOverflow"
                    (Solidity.Arg.positional
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualArrayConstructorCreateOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayConstructorCreateOverflowSource)

def contextualNamedArrayConstructorCreateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualNamedArrayCtorMaker"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayConstructorCreateFunction
                    "makeNamedArrayCtor"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayExpr)) ] } ] }

def contextualNamedArrayConstructorCreateAccepted : Bool :=
  sourceUnitAccepted? contextualNamedArrayConstructorCreateSource

def contextualNamedArrayConstructorCreateOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualNamedArrayCtorMakerOverflow"
            items :=
              [ Solidity.ContractItem.function
                  (contextualArrayConstructorCreateFunction
                    "makeNamedArrayCtorOverflow"
                    (Solidity.Arg.named "xs"
                      contextualNarrowArrayOverflowExpr)) ] } ] }

def contextualNamedArrayConstructorCreateOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualNamedArrayConstructorCreateOverflowSource)

def contextualArrayConstructorSaltedCreateFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "makeSaltedArrayCtor"
    params :=
      [{ name := some "salt"
         ty := bytes32
         location := none }]
    mutability := Solidity.StateMutability.nonpayable
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.expr
              (Solidity.Expr.callWithOptions
                (Solidity.Expr.newExpr
                  contextualArrayConstructorTargetTy [])
                [saltOption (Solidity.Expr.ident "salt")]
                [Solidity.Arg.positional
                  contextualNarrowArrayExpr])
          , Solidity.Stmt.returnValues
              (some (numberExpr "7")) ]) }

def contextualArrayConstructorSaltedCreateSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualSaltedArrayCtorMaker"
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayConstructorSaltedCreateFunction ] } ] }

def contextualArrayConstructorSaltedCreateAccepted : Bool :=
  sourceUnitAccepted? contextualArrayConstructorSaltedCreateSource

def contextualArrayBaseSpecifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualArrayBaseSpecifier"
            bases :=
              [{ base := userPath "ContextualArrayCtorTarget"
                 args :=
                  [Solidity.Arg.positional
                    contextualNarrowArrayExpr] }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def contextualArrayBaseSpecifierAccepted : Bool :=
  sourceUnitAccepted? contextualArrayBaseSpecifierSource

def contextualArrayBaseSpecifierOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          { name := "ContextualArrayBaseSpecifierOverflow"
            bases :=
              [{ base := userPath "ContextualArrayCtorTarget"
                 args :=
                  [Solidity.Arg.positional
                    contextualNarrowArrayOverflowExpr] }]
            items :=
              [Solidity.ContractItem.function
                simpleReturnFunction] } ] }

def contextualArrayBaseSpecifierOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayBaseSpecifierOverflowSource)

def contextualArrayBaseModifierDerived
    (name : Name) (arg : Solidity.Arg) :
    Solidity.ContractDecl :=
  { name := name
    bases := [{ base := userPath "ContextualArrayCtorTarget" }]
    items :=
      [ Solidity.ContractItem.function
          { kind := Solidity.FunctionKind.constructor
            modifiers :=
              [{ target := userPath "ContextualArrayCtorTarget"
                 args := [arg] }]
            body := some Solidity.Stmt.empty }
      , Solidity.ContractItem.function simpleReturnFunction ] }

def contextualArrayBaseModifierSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          (contextualArrayBaseModifierDerived
            "ContextualArrayBaseModifier"
            (Solidity.Arg.positional
              contextualNarrowArrayExpr)) ] }

def contextualArrayBaseModifierAccepted : Bool :=
  sourceUnitAccepted? contextualArrayBaseModifierSource

def contextualArrayBaseModifierOverflowSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayConstructorTargetContract
      , Solidity.SourceItem.contract
          (contextualArrayBaseModifierDerived
            "ContextualArrayBaseModifierOverflow"
            (Solidity.Arg.positional
              contextualNarrowArrayOverflowExpr)) ] }

def contextualArrayBaseModifierOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayBaseModifierOverflowSource)

def bytes4ValueExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.typeName bytes4)
    [Solidity.Arg.positional
      (Solidity.Expr.literal
        (Solidity.Literal.bytes [1, 2, 3, 4]))]

def shiftWideCountFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "shiftWide"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.shl
              uint8OneExpr
              uint16TwoExpr))) }

def shiftWideCountSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ShiftWideCount"
            items := [Solidity.ContractItem.function
              shiftWideCountFunction] } ] }

def shiftWideCountAccepted : Bool :=
  sourceUnitAccepted? shiftWideCountSource

def badShiftSignedCountFunction : Solidity.FunctionDecl :=
  { shiftWideCountFunction with
    name := some "badShiftSigned"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.shl
              uint8OneExpr
              int8OneExpr))) }

def badShiftSignedCountSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadShiftSignedCount"
            items := [Solidity.ContractItem.function
              badShiftSignedCountFunction] } ] }

def badShiftSignedCountRejected : Bool :=
  Result.isError (SourceUnit.check badShiftSignedCountSource)

def bytesBitwiseFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "bytesBitwise"
    returns := [{ name := none, ty := bytes4, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.bitAnd
              bytes4ValueExpr
              bytes4ValueExpr))) }

def bytesBitwiseSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BytesBitwise"
            items := [Solidity.ContractItem.function
              bytesBitwiseFunction] } ] }

def bytesBitwiseAccepted : Bool :=
  sourceUnitAccepted? bytesBitwiseSource

def badBytesArithmeticFunction : Solidity.FunctionDecl :=
  { bytesBitwiseFunction with
    name := some "badBytesArithmetic"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.add
              bytes4ValueExpr
              bytes4ValueExpr))) }

def badBytesArithmeticSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBytesArithmetic"
            items := [Solidity.ContractItem.function
              badBytesArithmeticFunction] } ] }

def badBytesArithmeticRejected : Bool :=
  Result.isError (SourceUnit.check badBytesArithmeticSource)

def compoundShiftFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "compoundShift"
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [ { name := some "x"
                  ty := some uint8
                  location := none } ]
              (some uint8OneExpr)
          , Solidity.Stmt.expr
              (Solidity.Expr.assign
                (Solidity.Expr.ident "x")
                Solidity.AssignOp.shlAssign
                uint16TwoExpr)
          , Solidity.Stmt.returnValues
              (some (Solidity.Expr.ident "x")) ]) }

def compoundShiftSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "CompoundShift"
            items := [Solidity.ContractItem.function
              compoundShiftFunction] } ] }

def compoundShiftAccepted : Bool :=
  sourceUnitAccepted? compoundShiftSource

def widthAndSignCastSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadCast"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badCast"
                    params := [{ name := some "x", ty := int8, location := none }]
                    returns := [{ name := none, ty := uint16, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some badWidthAndSignCastExpr)) } ] } ] }

def widthAndSignCastRejected : Bool :=
  Result.isError (SourceUnit.check widthAndSignCastSource)

def addressCastAcceptedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddressCast"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "addr"
                    returns := [{ name := none, ty := addressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some addressCastExpr)) } ] } ] }

def addressCastAccepted : Bool :=
  sourceUnitAccepted? addressCastAcceptedSource

def directPayableTypeConversionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "DirectPayableCast"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableCast"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.typeName payableAddressTy)
                              [Solidity.Arg.positional
                                zeroExpr]))) } ] } ] }

def directPayableTypeConversionRejected : Bool :=
  Result.isError (SourceUnit.check directPayableTypeConversionSource)

def payableZeroSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableZero"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableZero"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              zeroExpr))) } ] } ] }

def payableZeroAccepted : Bool :=
  sourceUnitAccepted? payableZeroSource

def payableZeroExpressionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableZeroExpression"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableZeroExpression"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              zeroBySubExpr))) } ] } ] }

def payableZeroExpressionAccepted : Bool :=
  sourceUnitAccepted? payableZeroExpressionSource

def payableTypedUint160ZeroSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadPayableUint160Zero"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "badPayableUint160Zero"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              uint160ZeroExpr))) } ] } ] }

def payableTypedUint160ZeroRejected : Bool :=
  Result.isError (SourceUnit.check payableTypedUint160ZeroSource)

def payableAddressUint160ZeroSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableAddressUint160Zero"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableAddressUint160Zero"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              addressUint160ZeroExpr))) } ] } ] }

def payableAddressUint160ZeroAccepted : Bool :=
  sourceUnitAccepted? payableAddressUint160ZeroSource

def payableOneSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableOne"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "payableOne"
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              oneExpr))) } ] } ] }

def payableOneRejected : Bool :=
  Result.isError (SourceUnit.check payableOneSource)

def payableReceiveFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.receive
    name := none
    params := []
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.payable
    body := some Solidity.Stmt.empty }

def typedFallbackFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.fallback
    name := none
    params :=
      [ { name := some "input"
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.calldata } ]
    returns :=
      [ { name := some "output"
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body := some Solidity.Stmt.empty }

def typedFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "TypedFallback"
            items := [Solidity.ContractItem.function
              typedFallbackFunction] } ] }

def typedFallbackAccepted : Bool :=
  sourceUnitAccepted? typedFallbackSource

def badFallbackViewSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFallbackView"
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with
                    mutability :=
                      Solidity.StateMutability.view } ] } ] }

def badFallbackViewRejected : Bool :=
  Result.isError (SourceUnit.check badFallbackViewSource)

def badFallbackParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFallbackParam"
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with
                    params :=
                      [{ name := some "input"
                         ty := uint256
                         location := none }]
                    returns := [] } ] } ] }

def badFallbackParamRejected : Bool :=
  Result.isError (SourceUnit.check badFallbackParamSource)

def badTypedFallbackMemoryParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTypedFallbackMemoryParam"
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with
                    params :=
                      [ { name := some "input"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.memory } ] } ] } ] }

def badTypedFallbackMemoryParamRejected : Bool :=
  Result.isError (SourceUnit.check badTypedFallbackMemoryParamSource)

def badTypedFallbackCalldataReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTypedFallbackCalldataReturn"
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with
                    returns :=
                      [ { name := some "output"
                          ty := Solidity.Ty.bytes
                          location :=
                            some
                              Solidity.DataLocation.calldata } ] } ] } ] }

def badTypedFallbackCalldataReturnRejected : Bool :=
  Result.isError (SourceUnit.check badTypedFallbackCalldataReturnSource)

def badTypedFallbackNoReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadTypedFallbackNoReturn"
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with returns := [] } ] } ] }

def badTypedFallbackNoReturnRejected : Bool :=
  Result.isError (SourceUnit.check badTypedFallbackNoReturnSource)

def untypedFallbackFunction : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.fallback
    name := none
    params := []
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body := some Solidity.Stmt.empty }

def untypedFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "UntypedFallback"
            items := [Solidity.ContractItem.function
              untypedFallbackFunction] } ] }

def untypedFallbackAccepted : Bool :=
  sourceUnitAccepted? untypedFallbackSource

def payableFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableFallback"
            items :=
              [ Solidity.ContractItem.function
                  { untypedFallbackFunction with
                    mutability :=
                      Solidity.StateMutability.payable } ] } ] }

def payableFallbackAccepted : Bool :=
  sourceUnitAccepted? payableFallbackSource

def badFallbackPublicSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadFallbackPublic"
            items :=
              [ Solidity.ContractItem.function
                  { untypedFallbackFunction with
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def badFallbackPublicRejected : Bool :=
  Result.isError (SourceUnit.check badFallbackPublicSource)

def virtualFallbackFunction : Solidity.FunctionDecl :=
  { untypedFallbackFunction with virtual := true }

def fallbackOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "FallbackBase"
            items := [Solidity.ContractItem.function
              virtualFallbackFunction] }
      , Solidity.SourceItem.contract
          { name := "FallbackDerived"
            bases := [{ base := userPath "FallbackBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { typedFallbackFunction with
                    override? := some { bases := [] } } ] } ] }

def fallbackOverrideAccepted : Bool :=
  sourceUnitAccepted? fallbackOverrideSource

def missingFallbackOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MissingFallbackBase"
            items := [Solidity.ContractItem.function
              virtualFallbackFunction] }
      , Solidity.SourceItem.contract
          { name := "MissingFallbackDerived"
            bases := [{ base := userPath "MissingFallbackBase", args := [] }]
            items := [Solidity.ContractItem.function
              untypedFallbackFunction] } ] }

def missingFallbackOverrideRejected : Bool :=
  Result.isError (SourceUnit.check missingFallbackOverrideSource)

def payableFallbackOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonpayableFallbackBase"
            items := [Solidity.ContractItem.function
              virtualFallbackFunction] }
      , Solidity.SourceItem.contract
          { name := "PayableFallbackDerived"
            bases :=
              [{ base := userPath "NonpayableFallbackBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { untypedFallbackFunction with
                    mutability :=
                      Solidity.StateMutability.payable
                    override? := some { bases := [] } } ] } ] }

def payableFallbackOverrideRejected : Bool :=
  Result.isError (SourceUnit.check payableFallbackOverrideSource)

def virtualReceiveFunction : Solidity.FunctionDecl :=
  { payableReceiveFunction with virtual := true }

def receiveOverrideSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ReceiveBase"
            items := [Solidity.ContractItem.function
              virtualReceiveFunction] }
      , Solidity.SourceItem.contract
          { name := "ReceiveDerived"
            bases := [{ base := userPath "ReceiveBase", args := [] }]
            items :=
              [ Solidity.ContractItem.function
                  { payableReceiveFunction with
                    override? := some { bases := [] } } ] } ] }

def receiveOverrideAccepted : Bool :=
  sourceUnitAccepted? receiveOverrideSource

def receiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Receive"
            items := [Solidity.ContractItem.function
              payableReceiveFunction] } ] }

def receiveAccepted : Bool :=
  sourceUnitAccepted? receiveSource

def badReceiveNonpayableSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadReceiveNonpayable"
            items :=
              [ Solidity.ContractItem.function
                  { payableReceiveFunction with
                    mutability :=
                      Solidity.StateMutability.nonpayable } ] } ] }

def badReceiveNonpayableRejected : Bool :=
  Result.isError (SourceUnit.check badReceiveNonpayableSource)

def badReceivePublicSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadReceivePublic"
            items :=
              [ Solidity.ContractItem.function
                  { payableReceiveFunction with
                    visibility :=
                      some Solidity.Visibility.public_ } ] } ] }

def badReceivePublicRejected : Bool :=
  Result.isError (SourceUnit.check badReceivePublicSource)

def badReceiveParamSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadReceiveParam"
            items :=
              [ Solidity.ContractItem.function
                  { payableReceiveFunction with
                    params :=
                      [{ name := some "value", ty := uint256, location := none }] } ] } ] }

def badReceiveParamRejected : Bool :=
  Result.isError (SourceUnit.check badReceiveParamSource)

def badReceiveReturnSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadReceiveReturn"
            items :=
              [ Solidity.ContractItem.function
                  { payableReceiveFunction with
                    returns :=
                      [{ name := none, ty := uint256, location := none }] } ] } ] }

def badReceiveReturnRejected : Bool :=
  Result.isError (SourceUnit.check badReceiveReturnSource)

def multipleReceiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MultipleReceive"
            items :=
              [ Solidity.ContractItem.function
                  payableReceiveFunction
              , Solidity.ContractItem.function
                  payableReceiveFunction ] } ] }

def multipleReceiveRejected : Bool :=
  Result.isError (SourceUnit.check multipleReceiveSource)

def multipleFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "MultipleFallback"
            items :=
              [ Solidity.ContractItem.function
                  untypedFallbackFunction
              , Solidity.ContractItem.function
                  typedFallbackFunction ] } ] }

def multipleFallbackRejected : Bool :=
  Result.isError (SourceUnit.check multipleFallbackSource)

def libraryFallbackSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "LibraryFallback"
            items := [Solidity.ContractItem.function
              untypedFallbackFunction] } ] }

def libraryFallbackRejected : Bool :=
  Result.isError (SourceUnit.check libraryFallbackSource)

def libraryReceiveSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { kind := Solidity.ContractKind.library
            name := "LibraryReceive"
            items := [Solidity.ContractItem.function
              payableReceiveFunction] } ] }

def libraryReceiveRejected : Bool :=
  Result.isError (SourceUnit.check libraryReceiveSource)

def fallbackReceiveCallableFormDisciplineMatches : Bool :=
  interfaceFallbackAccepted &&
    interfaceReceiveAccepted &&
    interfaceTypedFallbackAccepted &&
    untypedFallbackAccepted &&
    payableFallbackAccepted &&
    typedFallbackAccepted &&
    receiveAccepted &&
    badFallbackPublicRejected &&
    badFallbackViewRejected &&
    badFallbackParamRejected &&
    badTypedFallbackMemoryParamRejected &&
    badTypedFallbackCalldataReturnRejected &&
    badTypedFallbackNoReturnRejected &&
    badReceiveNonpayableRejected &&
    badReceivePublicRejected &&
    badReceiveParamRejected &&
    badReceiveReturnRejected &&
    multipleReceiveRejected &&
    multipleFallbackRejected &&
    libraryFallbackRejected &&
    libraryReceiveRejected

def constructorVirtualSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ConstructorVirtual"
            items :=
              [ Solidity.ContractItem.function
                  { (seedConstructor
                      Solidity.StateMutability.nonpayable) with
                    virtual := true } ] } ] }

def constructorVirtualRejected : Bool :=
  Result.isError (SourceUnit.check constructorVirtualSource)

def freeVirtualSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeFunction
          { simpleReturnFunction with
            visibility := none
            virtual := true } ] }

def freeVirtualRejected : Bool :=
  Result.isError (SourceUnit.check freeVirtualSource)

def freePayableSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeFunction
          { simpleReturnFunction with
            visibility := none
            mutability :=
              Solidity.StateMutability.payable } ] }

def freePayableRejected : Bool :=
  Result.isError (SourceUnit.check freePayableSource)

def abstractFallbackWithoutVirtualSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbstractFallbackWithoutVirtual"
            abstract := true
            items :=
              [ Solidity.ContractItem.function
                  { untypedFallbackFunction with body := none } ] } ] }

def abstractFallbackWithoutVirtualRejected : Bool :=
  Result.isError (SourceUnit.check abstractFallbackWithoutVirtualSource)

def callableHeaderAndOverrideDisciplineMatches : Bool :=
  fallbackOverrideAccepted &&
    receiveOverrideAccepted &&
    missingFallbackOverrideRejected &&
    payableFallbackOverrideRejected &&
    constructorVirtualRejected &&
    freeVirtualRejected &&
    freePayableRejected &&
    abstractFallbackWithoutVirtualRejected

def payableContractConversionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableTarget"
            items := [Solidity.ContractItem.function
              payableReceiveFunction] }
      , Solidity.SourceItem.contract
          { name := "PayableContractConversion"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "PayableTarget") }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "asPayable"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              (Solidity.Expr.ident "target")))) } ] } ] }

def payableContractConversionAccepted : Bool :=
  sourceUnitAccepted? payableContractConversionSource

def nonpayableContractConversionSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NonpayableTarget", items := [] }
      , Solidity.SourceItem.contract
          { name := "BadPayableContractConversion"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "NonpayableTarget") }
              , Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "asPayable"
                    mutability :=
                      Solidity.StateMutability.nonpayable
                    returns :=
                      [{ name := none, ty := payableAddressTy, location := none }]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.payableConversion
                              (Solidity.Expr.ident "target")))) } ] } ] }

def nonpayableContractConversionRejected : Bool :=
  Result.isError (SourceUnit.check nonpayableContractConversionSource)

def oneStepConversionFunction (name : Name) (sourceTy targetTy : Ty) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params := [{ name := some "input", ty := sourceTy, location := none }]
    returns := [{ name := none, ty := targetTy, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName targetTy)
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "input") ]))) }

def numericBytesConversionValidSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "NumericBytesConversionValid"
            items :=
              [ Solidity.ContractItem.function
                  (oneStepConversionFunction "uint16FromUint8" uint8 uint16)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "uint8FromUint16" uint16 uint8)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "uint8FromInt8" int8 uint8)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "int8FromUint8" uint8 int8)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "bytes4FromBytes2" bytes2 bytes4)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "bytes2FromBytes4" bytes4 bytes2)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "bytes2FromUint16" uint16 bytes2)
              , Solidity.ContractItem.function
                  (oneStepConversionFunction "uint16FromBytes2" bytes2 uint16) ] } ] }

def int8ToUint16ConversionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Int8ToUint16"
            items :=
              [ Solidity.ContractItem.function
                  (oneStepConversionFunction "convert" int8 uint16) ] } ] }

def uint8ToInt16ConversionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Uint8ToInt16"
            items :=
              [ Solidity.ContractItem.function
                  (oneStepConversionFunction "convert" uint8 int16) ] } ] }

def bytes2ToUint8ConversionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Bytes2ToUint8"
            items :=
              [ Solidity.ContractItem.function
                  (oneStepConversionFunction "convert" bytes2 uint8) ] } ] }

def uint32ToBytes2ConversionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "Uint32ToBytes2"
            items :=
              [ Solidity.ContractItem.function
                  (oneStepConversionFunction "convert" uint32 bytes2) ] } ] }

def numericBytesConversionDisciplineMatches : Bool :=
  sourceUnitAccepted? numericBytesConversionValidSource &&
    Result.isError (SourceUnit.check int8ToUint16ConversionSource) &&
    Result.isError (SourceUnit.check uint8ToInt16ConversionSource) &&
    Result.isError (SourceUnit.check bytes2ToUint8ConversionSource) &&
    Result.isError (SourceUnit.check uint32ToBytes2ConversionSource)

def addressToContractFunction (name : Name) (sourceTy targetTy : Ty) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params := [{ name := some "input", ty := sourceTy, location := none }]
    returns := [{ name := none, ty := targetTy, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.typeName targetTy)
              [ Solidity.Arg.positional
                  (Solidity.Expr.ident "input") ]))) }

def addressValueConversionValidSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddressValueConversionValid"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "addressToBytes20" addressTy
                    (Solidity.Ty.bytesN 20))
              , Solidity.ContractItem.function
                  (addressToContractFunction "addressToUint160" addressTy
                    (Solidity.Ty.uint 160))
              , Solidity.ContractItem.function
                  (addressToContractFunction "bytes20ToAddress"
                    (Solidity.Ty.bytesN 20) addressTy)
              , Solidity.ContractItem.function
                  (addressToContractFunction "uint160ToAddress"
                    (Solidity.Ty.uint 160) addressTy) ] } ] }

def payableAddressToBytes20Source : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableAddressToBytes20"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" payableAddressTy
                    (Solidity.Ty.bytesN 20)) ] } ] }

def payableAddressToUint160Source : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "PayableAddressToUint160"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" payableAddressTy
                    (Solidity.Ty.uint 160)) ] } ] }

def addressToBytes32Source : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddressToBytes32"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy
                    (Solidity.Ty.bytesN 32)) ] } ] }

def addressToUint256Source : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AddressToUint256"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy uint256) ] } ] }

def addressValueConversionDisciplineMatches : Bool :=
  sourceUnitAccepted? addressValueConversionValidSource &&
    Result.isError (SourceUnit.check payableAddressToBytes20Source) &&
    Result.isError (SourceUnit.check payableAddressToUint160Source) &&
    Result.isError (SourceUnit.check addressToBytes32Source) &&
    Result.isError (SourceUnit.check addressToUint256Source)

def payableAddressConversionTarget : Solidity.ContractDecl :=
  { name := "PayableAddressConversionTarget"
    items :=
      [ Solidity.ContractItem.function payableReceiveFunction ] }

def payableAddressConversionTargetTy : Ty :=
  Solidity.Ty.user (userPath "PayableAddressConversionTarget")

def addressToPayableContractSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract payableAddressConversionTarget
      , Solidity.SourceItem.contract
          { name := "AddressToPayableContract"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy
                    payableAddressConversionTargetTy) ] } ] }

def addressToPayableContractRejected : Bool :=
  Result.isError (SourceUnit.check addressToPayableContractSource)

def payableFallbackAddressConversionTarget :
    Solidity.ContractDecl :=
  { name := "PayableFallbackAddressConversionTarget"
    items :=
      [ Solidity.ContractItem.function
          { untypedFallbackFunction with
            mutability := Solidity.StateMutability.payable } ] }

def payableFallbackAddressConversionTargetTy : Ty :=
  Solidity.Ty.user
    (userPath "PayableFallbackAddressConversionTarget")

def addressToPayableFallbackContractSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          payableFallbackAddressConversionTarget
      , Solidity.SourceItem.contract
          { name := "AddressToPayableFallbackContract"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy
                    payableFallbackAddressConversionTargetTy) ] } ] }

def addressToPayableFallbackContractRejected : Bool :=
  Result.isError (SourceUnit.check addressToPayableFallbackContractSource)

def payableAddressToPayableContractSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract payableAddressConversionTarget
      , Solidity.SourceItem.contract
          { name := "PayableAddressToPayableContract"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" payableAddressTy
                    payableAddressConversionTargetTy) ] } ] }

def payableAddressToPayableContractAccepted : Bool :=
  sourceUnitAccepted? payableAddressToPayableContractSource

def nonpayableAddressConversionTarget : Solidity.ContractDecl :=
  { name := "NonpayableAddressConversionTarget" }

def nonpayableAddressConversionTargetTy : Ty :=
  Solidity.Ty.user
    (userPath "NonpayableAddressConversionTarget")

def addressToNonpayableContractSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          nonpayableAddressConversionTarget
      , Solidity.SourceItem.contract
          { name := "AddressToNonpayableContract"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy
                    nonpayableAddressConversionTargetTy) ] } ] }

def addressToNonpayableContractAccepted : Bool :=
  sourceUnitAccepted? addressToNonpayableContractSource

def inheritedPayableConversionBase : Solidity.ContractDecl :=
  { name := "InheritedPayableConversionBase"
    items :=
      [ Solidity.ContractItem.function payableReceiveFunction ] }

def inheritedPayableConversionTarget : Solidity.ContractDecl :=
  { name := "InheritedPayableConversionTarget"
    bases := [{ base := userPath "InheritedPayableConversionBase" }] }

def inheritedPayableConversionTargetTy : Ty :=
  Solidity.Ty.user
    (userPath "InheritedPayableConversionTarget")

def addressToInheritedPayableContractSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract inheritedPayableConversionBase
      , Solidity.SourceItem.contract inheritedPayableConversionTarget
      , Solidity.SourceItem.contract
          { name := "AddressToInheritedPayableContract"
            items :=
              [ Solidity.ContractItem.function
                  (addressToContractFunction "convert" addressTy
                    inheritedPayableConversionTargetTy) ] } ] }

def addressToInheritedPayableContractRejected : Bool :=
  Result.isError (SourceUnit.check addressToInheritedPayableContractSource)

def inheritedPayableContractValueFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "asPayable"
    params :=
      [ { name := some "input"
          ty := inheritedPayableConversionTargetTy
          location := none } ]
    returns := [{ name := none, ty := payableAddressTy, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.payableConversion
              (Solidity.Expr.ident "input")))) }

def inheritedPayableContractValueSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract inheritedPayableConversionBase
      , Solidity.SourceItem.contract inheritedPayableConversionTarget
      , Solidity.SourceItem.contract
          { name := "InheritedPayableContractValue"
            items :=
              [ Solidity.ContractItem.function
                  inheritedPayableContractValueFunction ] } ] }

def inheritedPayableContractValueAccepted : Bool :=
  sourceUnitAccepted? inheritedPayableContractValueSource

def addressContractConversionDisciplineMatches : Bool :=
  addressToPayableContractRejected &&
    addressToPayableFallbackContractRejected &&
    payableAddressToPayableContractAccepted &&
    addressToNonpayableContractAccepted &&
    addressToInheritedPayableContractRejected &&
    inheritedPayableContractValueAccepted &&
    nonpayableContractConversionRejected

def priceTy : Ty :=
  Solidity.Ty.user (userPath "Price")

def priceDecl : Solidity.UserValueTypeDecl :=
  { name := "Price", underlying := uint256 }

def wrappedPriceOneExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.member
      (Solidity.Expr.typeName priceTy) "wrap")
    [Solidity.Arg.positional oneExpr]

def unwrappedPriceOneExpr : Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.member
      (Solidity.Expr.typeName priceTy) "unwrap")
    [Solidity.Arg.positional wrappedPriceOneExpr]

def userValueWrapUnwrapSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.contract
          { name := "UserValueWrap"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "unwrap"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some unwrappedPriceOneExpr)) } ] } ] }

def userValueWrapUnwrapAccepted : Bool :=
  sourceUnitAccepted? userValueWrapUnwrapSource

def badUserValueUnwrapSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.contract
          { name := "BadUserValueUnwrap"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "unwrap"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.typeName priceTy)
                                "unwrap")
                              [Solidity.Arg.positional
                                oneExpr]))) } ] } ] }

def badUserValueUnwrapRejected : Bool :=
  Result.isError (SourceUnit.check badUserValueUnwrapSource)

def priceMathPlusOneFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "inc"
    visibility := some Solidity.Visibility.internal_
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
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.typeName priceTy) "wrap")
              [ Solidity.Arg.positional
                  (Solidity.Expr.binary
                    Solidity.BinaryOp.add
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.typeName priceTy)
                        "unwrap")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "self")])
                    (numberExpr "1")) ]))) }

def priceMathLibrary : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "PriceMath"
    items :=
      [Solidity.ContractItem.function
        priceMathPlusOneFunction] }

def globalUsingPriceFunction : Solidity.FunctionDecl :=
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
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "price"
                 ty := some priceTy
                 location := none }]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.member
                    (Solidity.Expr.typeName priceTy) "wrap")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "raw")]))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.member
                    (Solidity.Expr.typeName priceTy) "unwrap")
                  [ Solidity.Arg.positional
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.ident "price") "inc")
                        []) ])) ]) }

def globalUsingPriceSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.contract priceMathLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "PriceMath"
            target := some priceTy
            global := true }
      , Solidity.SourceItem.contract
          { name := "GlobalUsingPrice"
            items :=
              [Solidity.ContractItem.function
                globalUsingPriceFunction] } ] }

def globalUsingPriceAccepted : Bool :=
  sourceUnitAccepted? globalUsingPriceSource

def priceOperatorAddFunction : Solidity.FunctionDecl :=
  { name := some "priceAdd"
    params :=
      [ { name := some "left", ty := priceTy, location := none }
      , { name := some "right", ty := priceTy, location := none } ]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.typeName priceTy) "wrap")
              [ Solidity.Arg.positional
                  (Solidity.Expr.binary
                    Solidity.BinaryOp.add
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.typeName priceTy)
                        "unwrap")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "left")])
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.typeName priceTy)
                        "unwrap")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "right")])) ]))) }

def priceOperatorLtFunction : Solidity.FunctionDecl :=
  { name := some "priceLt"
    params :=
      [ { name := some "left", ty := priceTy, location := none }
      , { name := some "right", ty := priceTy, location := none } ]
    returns := [{ name := some "out", ty := Solidity.Ty.bool }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary
              Solidity.BinaryOp.lt
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.typeName priceTy) "unwrap")
                [Solidity.Arg.positional
                  (Solidity.Expr.ident "left")])
              (Solidity.Expr.call
                (Solidity.Expr.member
                  (Solidity.Expr.typeName priceTy) "unwrap")
                [Solidity.Arg.positional
                  (Solidity.Expr.ident "right")])))) }

def priceOperatorNegFunction : Solidity.FunctionDecl :=
  { name := some "priceNeg"
    params := [{ name := some "value", ty := priceTy, location := none }]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.typeName priceTy) "wrap")
              [ Solidity.Arg.positional
                  (Solidity.Expr.binary
                    Solidity.BinaryOp.add
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.typeName priceTy)
                        "unwrap")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "value")])
                    (numberExpr "1")) ]))) }

def priceOperatorBitNotFunction : Solidity.FunctionDecl :=
  { name := some "priceBitNot"
    params := [{ name := some "value", ty := priceTy, location := none }]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.typeName priceTy) "wrap")
              [ Solidity.Arg.positional
                  (Solidity.Expr.binary
                    Solidity.BinaryOp.add
                    (Solidity.Expr.call
                      (Solidity.Expr.member
                        (Solidity.Expr.typeName priceTy)
                        "unwrap")
                      [Solidity.Arg.positional
                        (Solidity.Expr.ident "value")])
                    (numberExpr "2")) ]))) }

def globalUsingPriceOperatorFunction :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "runOperator"
    params :=
      [ { name := some "left", ty := uint256, location := none }
      , { name := some "right", ty := uint256, location := none } ]
    returns :=
      [ { name := some "sum", ty := uint256, location := none }
      , { name := some "less", ty := Solidity.Ty.bool,
          location := none }
      , { name := some "negated", ty := uint256, location := none }
      , { name := some "inverted", ty := uint256, location := none } ]
    body :=
      some
        (Solidity.Stmt.block
          [ Solidity.Stmt.varDecl
              [{ name := some "a", ty := some priceTy, location := none }]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.member
                    (Solidity.Expr.typeName priceTy) "wrap")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "left")]))
          , Solidity.Stmt.varDecl
              [{ name := some "b", ty := some priceTy, location := none }]
              (some
                (Solidity.Expr.call
                  (Solidity.Expr.member
                    (Solidity.Expr.typeName priceTy) "wrap")
                  [Solidity.Arg.positional
                    (Solidity.Expr.ident "right")]))
          , Solidity.Stmt.returnValues
              (some
                (Solidity.Expr.tuple
                  [ Solidity.TupleItem.value
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.typeName priceTy)
                          "unwrap")
                        [ Solidity.Arg.positional
                            (Solidity.Expr.binary
                              Solidity.BinaryOp.add
                              (Solidity.Expr.ident "a")
                              (Solidity.Expr.ident "b")) ])
                  , Solidity.TupleItem.value
                      (Solidity.Expr.binary
                        Solidity.BinaryOp.lt
                        (Solidity.Expr.ident "a")
                        (Solidity.Expr.ident "b"))
                  , Solidity.TupleItem.value
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.typeName priceTy)
                          "unwrap")
                        [ Solidity.Arg.positional
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.neg
                              (Solidity.Expr.ident "a")) ])
                  , Solidity.TupleItem.value
                      (Solidity.Expr.call
                        (Solidity.Expr.member
                          (Solidity.Expr.typeName priceTy)
                          "unwrap")
                        [ Solidity.Arg.positional
                            (Solidity.Expr.unary
                              Solidity.UnaryOp.bitNot
                              (Solidity.Expr.ident "a")) ]) ])) ]) }

def globalUsingPriceOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorLtFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorNegFunction
      , Solidity.SourceItem.freeFunction
          priceOperatorBitNotFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [ { function := { segments := ["priceAdd"] }
                  operator? := some
                    (Solidity.UsingOperator.binary
                      Solidity.BinaryOp.add) }
              , { function := { segments := ["priceLt"] }
                  operator? := some
                    (Solidity.UsingOperator.binary
                      Solidity.BinaryOp.lt) }
              , { function := { segments := ["priceNeg"] }
                  operator? := some
                    (Solidity.UsingOperator.unary
                      Solidity.UnaryOp.neg) }
              , { function := { segments := ["priceBitNot"] }
                  operator? := some
                    (Solidity.UsingOperator.unary
                      Solidity.UnaryOp.bitNot) } ]
            target := some priceTy
            global := true }
      , Solidity.SourceItem.contract
          { name := "GlobalUsingPriceOperator"
            items :=
              [ Solidity.ContractItem.function
                  globalUsingPriceOperatorFunction ] } ] }

def globalUsingPriceOperatorAccepted : Bool :=
  sourceUnitAccepted? globalUsingPriceOperatorSource

def contractUsingOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction
          priceOperatorAddFunction
      , Solidity.SourceItem.contract
          { name := "BadContractUsingOperator"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := { segments := [] }
                    functions :=
                      [{ function := { segments := ["priceAdd"] }
                         operator? := some
                          (Solidity.UsingOperator.binary
                            Solidity.BinaryOp.add) }]
                    target := some priceTy } ] } ] }

def contractUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check contractUsingOperatorSource)

def nonPurePriceOperatorAddFunction :
    Solidity.FunctionDecl :=
  { priceOperatorAddFunction with
    mutability := Solidity.StateMutability.view }

def nonPureUsingOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction
          nonPurePriceOperatorAddFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAdd"] }
                 operator? := some
                  (Solidity.UsingOperator.binary
                    Solidity.BinaryOp.add) }]
            target := some priceTy
            global := true } ] }

def nonPureUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check nonPureUsingOperatorSource)

def contractGlobalUsingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.contract priceMathLibrary
      , Solidity.SourceItem.contract
          { name := "BadContractGlobalUsing"
            items :=
              [ Solidity.ContractItem.usingDecl
                  { library := userPath "PriceMath"
                    target := some priceTy
                    global := true } ] } ] }

def contractGlobalUsingRejected : Bool :=
  Result.isError (SourceUnit.check contractGlobalUsingSource)

def globalUsingNonUserValueSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.contract priceMathLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "PriceMath"
            target := some uint256
            global := true } ] }

def globalUsingNonUserValueRejected : Bool :=
  Result.isError (SourceUnit.check globalUsingNonUserValueSource)

/-! ### UF1/UF2/UF3 — `using ... for T global` legality on non-UDVT targets,
operator-binding parameter shape, and duplicate operator bindings.

UF1: a file-level `global` using directive admits ANY same-source-unit
user-defined type (struct / enum / UDVT), not only a UDVT. The UDVT-only
restriction is kept for OPERATOR bindings and for built-in / cross-file targets.
UF2: an operator function must have every parameter exactly the target type.
UF3: binding the same operator for the same type twice is a directive-level
error. All boundaries confirmed against pinned solc 0.8.35. -/

def globalStructTy : Ty :=
  Solidity.Ty.user (userPath "Amount")

def globalStructDecl : Solidity.StructDecl :=
  { name := "Amount"
    fields := [{ name := "value", ty := uint256 }] }

def globalStructDoubledFunction : Solidity.FunctionDecl :=
  { name := some "doubled"
    params :=
      [{ name := some "a", ty := globalStructTy,
         location := some Solidity.DataLocation.memory }]
    returns := [{ name := none, ty := uint256, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary Solidity.BinaryOp.mul
              (Solidity.Expr.member (Solidity.Expr.ident "a") "value")
              (numberExpr "2")))) }

-- UF1: `using {f} for S global` on a STRUCT — accepted (solc accepts).
def globalUsingStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct globalStructDecl
      , Solidity.SourceItem.freeFunction globalStructDoubledFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions := [{ function := { segments := ["doubled"] } }]
            target := some globalStructTy
            global := true } ] }

def globalUsingStructAccepted : Bool :=
  sourceUnitAccepted? globalUsingStructSource

def globalStructLibrary : Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "AmountLib"
    items :=
      [ Solidity.ContractItem.function
          { globalStructDoubledFunction with
            name := some "tripled"
            visibility := some Solidity.Visibility.internal_
            body :=
              some
                (Solidity.Stmt.returnValues
                  (some
                    (Solidity.Expr.binary Solidity.BinaryOp.mul
                      (Solidity.Expr.member (Solidity.Expr.ident "a") "value")
                      (numberExpr "3")))) } ] }

-- UF1: library-form `using L for S global` on a STRUCT — accepted.
def globalUsingStructLibrarySource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct globalStructDecl
      , Solidity.SourceItem.contract globalStructLibrary
      , Solidity.SourceItem.usingDecl
          { library := userPath "AmountLib"
            target := some globalStructTy
            global := true } ] }

def globalUsingStructLibraryAccepted : Bool :=
  sourceUnitAccepted? globalUsingStructLibrarySource

def globalEnumTy : Ty :=
  Solidity.Ty.user (userPath "Color")

def globalEnumDecl : Solidity.EnumDecl :=
  { name := "Color", cases := ["Red", "Green", "Blue"] }

def globalEnumRankFunction : Solidity.FunctionDecl :=
  { name := some "rank"
    params := [{ name := some "c", ty := globalEnumTy, location := none }]
    returns := [{ name := none, ty := uint256, location := none }]
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.binary Solidity.BinaryOp.add
              (Solidity.Expr.call
                (Solidity.Expr.typeName uint256)
                [Solidity.Arg.positional (Solidity.Expr.ident "c")])
              (numberExpr "1")))) }

-- UF1: `using {f} for E global` on an ENUM — accepted.
def globalUsingEnumSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeEnum globalEnumDecl
      , Solidity.SourceItem.freeFunction globalEnumRankFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions := [{ function := { segments := ["rank"] } }]
            target := some globalEnumTy
            global := true } ] }

def globalUsingEnumAccepted : Bool :=
  sourceUnitAccepted? globalUsingEnumSource

def globalStructOperatorAddFunction : Solidity.FunctionDecl :=
  { name := some "amountAdd"
    params :=
      [ { name := some "a", ty := globalStructTy,
          location := some Solidity.DataLocation.memory }
      , { name := some "b", ty := globalStructTy,
          location := some Solidity.DataLocation.memory } ]
    returns :=
      [{ name := none, ty := globalStructTy,
         location := some Solidity.DataLocation.memory }]
    mutability := Solidity.StateMutability.pure
    body := some (Solidity.Stmt.returnValues (some (Solidity.Expr.ident "a"))) }

-- UF1 reject neighbor: an OPERATOR binding still requires a UDVT target; a
-- struct operator binding must stay rejected.
def globalUsingStructOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeStruct globalStructDecl
      , Solidity.SourceItem.freeFunction globalStructOperatorAddFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["amountAdd"] }
                 operator? := some
                  (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }]
            target := some globalStructTy
            global := true } ] }

def globalUsingStructOperatorRejected : Bool :=
  Result.isError (SourceUnit.check globalUsingStructOperatorSource)

-- UF2: operator binding whose parameters are not BOTH the target type.
def priceOperatorAddMixedFunction : Solidity.FunctionDecl :=
  { name := some "priceAddMixed"
    params :=
      [ { name := some "left", ty := priceTy, location := none }
      , { name := some "right", ty := uint256, location := none } ]
    returns := [{ name := some "out", ty := priceTy, location := none }]
    mutability := Solidity.StateMutability.pure
    body := some (Solidity.Stmt.returnValues (some (Solidity.Expr.ident "left"))) }

def badMixedParamUsingOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction priceOperatorAddMixedFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAddMixed"] }
                 operator? := some
                  (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }]
            target := some priceTy
            global := true } ] }

def badMixedParamUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check badMixedParamUsingOperatorSource)

-- UF2: first parameter not the target type either.
def priceOperatorAddFirstMixedFunction : Solidity.FunctionDecl :=
  { priceOperatorAddMixedFunction with
    name := some "priceAddFirstMixed"
    params :=
      [ { name := some "left", ty := uint256, location := none }
      , { name := some "right", ty := priceTy, location := none } ]
    body := some (Solidity.Stmt.returnValues (some (Solidity.Expr.ident "right"))) }

def badFirstParamUsingOperatorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction priceOperatorAddFirstMixedFunction
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAddFirstMixed"] }
                 operator? := some
                  (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }]
            target := some priceTy
            global := true } ] }

def badFirstParamUsingOperatorRejected : Bool :=
  Result.isError (SourceUnit.check badFirstParamUsingOperatorSource)

-- UF3: two bindings of the same operator for the same type in one directive.
def priceOperatorAdd2Function : Solidity.FunctionDecl :=
  { priceOperatorAddFunction with name := some "priceAdd2" }

def duplicateOperatorBindingSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction priceOperatorAddFunction
      , Solidity.SourceItem.freeFunction priceOperatorAdd2Function
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [ { function := { segments := ["priceAdd"] }
                  operator? := some
                    (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }
              , { function := { segments := ["priceAdd2"] }
                  operator? := some
                    (Solidity.UsingOperator.binary Solidity.BinaryOp.add) } ]
            target := some priceTy
            global := true } ] }

def duplicateOperatorBindingRejected : Bool :=
  Result.isError (SourceUnit.check duplicateOperatorBindingSource)

-- UF3: same operator+type duplicated across two SEPARATE directives.
def duplicateOperatorBindingSplitSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.freeUserValueType priceDecl
      , Solidity.SourceItem.freeFunction priceOperatorAddFunction
      , Solidity.SourceItem.freeFunction priceOperatorAdd2Function
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAdd"] }
                 operator? := some
                  (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }]
            target := some priceTy
            global := true }
      , Solidity.SourceItem.usingDecl
          { library := { segments := [] }
            functions :=
              [{ function := { segments := ["priceAdd2"] }
                 operator? := some
                  (Solidity.UsingOperator.binary Solidity.BinaryOp.add) }]
            target := some priceTy
            global := true } ] }

def duplicateOperatorBindingSplitRejected : Bool :=
  Result.isError (SourceUnit.check duplicateOperatorBindingSplitSource)

/-- Aggregated UF1/UF2/UF3 discipline: non-UDVT user-defined `global` targets
are accepted (UF1); operator bindings on non-UDVT targets, built-in targets,
mixed-parameter operator functions (UF2), and duplicate operator bindings (UF3)
are all rejected; and the correct UDVT operator bindings stay accepted. -/
def usingForGlobalNonUdvtDisciplineMatches : Bool :=
  -- UF1: struct / enum / library-form global targets accepted.
  globalUsingStructAccepted &&
    globalUsingStructLibraryAccepted &&
    globalUsingEnumAccepted &&
    -- UF1 must-hold neighbors: operator-on-struct and built-in global rejected.
    globalUsingStructOperatorRejected &&
    globalUsingNonUserValueRejected &&
    -- UF2: correct UDVT operator bindings stay accepted; mixed params rejected.
    globalUsingPriceOperatorAccepted &&
    badMixedParamUsingOperatorRejected &&
    badFirstParamUsingOperatorRejected &&
    -- UF3: duplicate operator bindings rejected at the directive.
    duplicateOperatorBindingRejected &&
    duplicateOperatorBindingSplitRejected

def bytesReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    returns :=
      [ { name := none
          ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ] }

def abiEncodeExternalFunctionPointerFunction :
    Solidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some "packExternalFunction"
    params :=
      [ { name := some "getter"
          ty := externalPureUintFunctionTy
          location := none } ]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "abi")
                "encode")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "getter")]))) }

def abiEncodeExternalFunctionPointerSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiEncodeExternalFunctionPointer"
            items :=
              [Solidity.ContractItem.function
                abiEncodeExternalFunctionPointerFunction] } ] }

def abiEncodeExternalFunctionPointerAccepted : Bool :=
  sourceUnitAccepted? abiEncodeExternalFunctionPointerSource

def abiEncodeInternalFunctionPointerFunction :
    Solidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some "packInternalFunction"
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "abi")
                "encode")
              [Solidity.Arg.positional
                (Solidity.Expr.ident "internalTarget")]))) }

def abiEncodeInternalFunctionPointerSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeInternalFunctionPointer"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "internalTarget"
                    visibility :=
                      some Solidity.Visibility.internal_ }
              , Solidity.ContractItem.function
                  abiEncodeInternalFunctionPointerFunction ] } ] }

def abiEncodeInternalFunctionPointerRejected : Bool :=
  Result.isError
    (SourceUnit.check abiEncodeInternalFunctionPointerSource)

def abiDecodeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiDecode"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "decode"
                    params :=
                      [ { name := some "data"
                          ty := Solidity.Ty.bytes
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "decode")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident "data")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.typeName
                                    uint256) ]))) } ] } ] }

def abiDecodeAccepted : Bool :=
  sourceUnitAccepted? abiDecodeSource

def badAbiDecodeSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiDecode"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "decode"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "decode")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bool true))
                              , Solidity.Arg.positional
                                  (Solidity.Expr.typeName
                                    uint256) ]))) } ] } ] }

def badAbiDecodeRejected : Bool :=
  Result.isError (SourceUnit.check badAbiDecodeSource)

def badAbiEncodeWithSelectorSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeWithSelector"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "encode"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeWithSelector")
                              [ Solidity.Arg.positional oneExpr
                              , Solidity.Arg.positional
                                  zeroExpr ]))) } ] } ] }

def badAbiEncodeWithSelectorRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeWithSelectorSource)

def badAbiEncodeWithSignatureSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeWithSignature"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "encode"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeWithSignature")
                              [ Solidity.Arg.positional oneExpr
                              , Solidity.Arg.positional
                                  zeroExpr ]))) } ] } ] }

def badAbiEncodeWithSignatureRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeWithSignatureSource)

def abiSelectorSignatureDisciplineMatches : Bool :=
  badAbiEncodeWithSelectorRejected &&
    badAbiEncodeWithSignatureRejected

def badAbiEncodePackedStructSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodePackedStruct"
            items :=
              [ Solidity.ContractItem.structDecl
                  { name := "PackedStruct"
                    fields := [{ name := "x", ty := uint256 }] }
              , Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "packStruct"
                    params :=
                      [ { name := some "item"
                          ty :=
                            Solidity.Ty.user
                              (userPath "PackedStruct")
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodePacked")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "item")]))) } ] } ] }

def badAbiEncodePackedStructRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodePackedStructSource)

def badAbiEncodePackedNestedArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodePackedNestedArray"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "packNestedArray"
                    params :=
                      [ { name := some "matrix"
                          ty :=
                            Solidity.Ty.array
                              (Solidity.Ty.array uint256 none)
                              none
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodePacked")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "matrix")]))) } ] } ] }

def badAbiEncodePackedNestedArrayRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodePackedNestedArraySource)

def abiEncodePackedStaticElementArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiEncodePackedStaticElementArray"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "packArray"
                    params :=
                      [ { name := some "items"
                          ty :=
                            Solidity.Ty.array
                              (Solidity.Ty.uint 8) none
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodePacked")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "items")]))) } ] } ] }

def abiEncodePackedStaticElementArrayAccepted : Bool :=
  sourceUnitAccepted? abiEncodePackedStaticElementArraySource

-- PK1: solc ACCEPTS packed encoding of a nested STATIC array whose ultimate
-- element is a static value type (`uint8[2][2]`). Mirrors the solc-accepting
-- Forge lane `packed-nested-static-array`; the doubly-dynamic case above stays
-- rejected.
def abiEncodePackedNestedStaticArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiEncodePackedNestedStaticArray"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "packMatrix"
                    params :=
                      [ { name := some "matrix"
                          ty :=
                            Solidity.Ty.array
                              (Solidity.Ty.array (Solidity.Ty.uint 8) (some 2))
                              (some 2)
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodePacked")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "matrix")]))) } ] } ] }

def abiEncodePackedNestedStaticArrayAccepted : Bool :=
  sourceUnitAccepted? abiEncodePackedNestedStaticArraySource

-- PK1 guard: a nested array whose inner dimension is DYNAMIC (`uint8[][3]`)
-- stays rejected, matching solc error 9578.
def abiEncodePackedDynamicInnerArraySource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiEncodePackedDynamicInnerArray"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "packGrid"
                    params :=
                      [ { name := some "grid"
                          ty :=
                            Solidity.Ty.array
                              (Solidity.Ty.array (Solidity.Ty.uint 8) none)
                              (some 3)
                          location :=
                            some Solidity.DataLocation.memory } ]
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodePacked")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "grid")]))) } ] } ] }

def abiEncodePackedDynamicInnerArrayRejected : Bool :=
  Result.isError (SourceUnit.check abiEncodePackedDynamicInnerArraySource)

-- PK1 value pin: the interpreter's packed encoder emits each innermost element
-- padded to a 32-byte word, in-place — so `uint8[2][2] = [[1,2],[3,4]]` packs to
-- word(1)‖word(2)‖word(3)‖word(4) (128 bytes). This is the exact layout the
-- Forge lane confirms against solc's own `abi.encodePacked`.
def abiEncodePackedNestedStaticArrayValueMatches : Bool :=
  (SolidCore.Solidity.Source.abiEncodePackedValue?
      (SolidCore.Solidity.Source.Ty.fixedArray 2
        (SolidCore.Solidity.Source.Ty.fixedArray 2
          SolidCore.Solidity.Source.Ty.uint256))
      (SolidCore.Solidity.Source.Value.fixedArray
        [ SolidCore.Solidity.Source.Value.fixedArray
            [SolidCore.Solidity.Source.Value.word 1,
              SolidCore.Solidity.Source.Value.word 2]
        , SolidCore.Solidity.Source.Value.fixedArray
            [SolidCore.Solidity.Source.Value.word 3,
              SolidCore.Solidity.Source.Value.word 4] ]))
    ==
      some
        (SolidCore.Solidity.Source.ABI.encodeWord 1 ++
          SolidCore.Solidity.Source.ABI.encodeWord 2 ++
          SolidCore.Solidity.Source.ABI.encodeWord 3 ++
          SolidCore.Solidity.Source.ABI.encodeWord 4)

-- PK1 value pin (dynamic outer, static inner): `uint8[2][] = [[9,8],[7,6]]`
-- packs to the same 128-byte padded layout.
def abiEncodePackedDynamicOuterStaticInnerValueMatches : Bool :=
  (SolidCore.Solidity.Source.abiEncodePackedValue?
      (SolidCore.Solidity.Source.Ty.dynamicArray
        (SolidCore.Solidity.Source.Ty.fixedArray 2
          SolidCore.Solidity.Source.Ty.uint256))
      (SolidCore.Solidity.Source.Value.dynamicArray
        [ SolidCore.Solidity.Source.Value.fixedArray
            [SolidCore.Solidity.Source.Value.word 9,
              SolidCore.Solidity.Source.Value.word 8]
        , SolidCore.Solidity.Source.Value.fixedArray
            [SolidCore.Solidity.Source.Value.word 7,
              SolidCore.Solidity.Source.Value.word 6] ]))
    ==
      some
        (SolidCore.Solidity.Source.ABI.encodeWord 9 ++
          SolidCore.Solidity.Source.ABI.encodeWord 8 ++
          SolidCore.Solidity.Source.ABI.encodeWord 7 ++
          SolidCore.Solidity.Source.ABI.encodeWord 6)

def bytesConcatSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BytesConcat"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes [1]))
                              , Solidity.Arg.positional
                                  (Solidity.Expr.call
                                    (Solidity.Expr.typeName bytes4)
                                    [Solidity.Arg.positional
                                      zeroExpr]) ]))) } ] } ] }

def bytesConcatAccepted : Bool :=
  sourceUnitAccepted? bytesConcatSource

def badBytesConcatSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBytesConcat"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [Solidity.Arg.positional
                                oneExpr]))) } ] } ] }

def badBytesConcatRejected : Bool :=
  Result.isError (SourceUnit.check badBytesConcatSource)

def badBytesConcatNamedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBytesConcatNamed"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [ Solidity.Arg.named "x"
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1])) ]))) } ] } ] }

def badBytesConcatNamedRejected : Bool :=
  Result.isError (SourceUnit.check badBytesConcatNamedSource)

-- SB1 pin: `bytes.concat` accepts string *literals* (solc's StringLiteralType is
-- implicitly convertible to both `bytes32` and `bytes memory`) but REJECTS
-- `string`-typed *values*.  Pinned solc 0.8.35 rejects `bytes.concat(<string
-- variable>)` with Error 8015 ("bytes or fixed bytes type is required, but string
-- memory provided").  This frontend types both forms as `Ty.string`, so the gate
-- must inspect the argument expression's literal-ness.

def bytesConcatStringLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BytesConcatStringLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.string "abc"))
                              , Solidity.Arg.positional
                                  (Solidity.Expr.call
                                    (Solidity.Expr.typeName bytes4)
                                    [Solidity.Arg.positional
                                      zeroExpr]) ]))) } ] } ] }

def bytesConcatStringLiteralAccepted : Bool :=
  sourceUnitAccepted? bytesConcatStringLiteralSource

def bytesConcatUnicodeLiteralSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BytesConcatUnicodeLiteral"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.unicodeString "é")) ]))) }
              ] } ] }

def bytesConcatUnicodeLiteralAccepted : Bool :=
  sourceUnitAccepted? bytesConcatUnicodeLiteralSource

def stringParamBytesReturnFunction : Solidity.FunctionDecl :=
  { bytesReturnFunction with
    params :=
      [ { name := some "s"
          ty := Solidity.Ty.string
          location := some Solidity.DataLocation.memory } ] }

def badBytesConcatStringVarSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBytesConcatStringVar"
            items :=
              [ Solidity.ContractItem.function
                  { stringParamBytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident "s")]))) } ] } ] }

def badBytesConcatStringVarRejected : Bool :=
  Result.isError (SourceUnit.check badBytesConcatStringVarSource)

def badBytesConcatMixedStringVarSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadBytesConcatMixedStringVar"
            items :=
              [ Solidity.ContractItem.function
                  { stringParamBytesReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "bytes")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.string "abc"))
                              , Solidity.Arg.positional
                                  (Solidity.Expr.ident "s") ]))) } ] } ] }

def badBytesConcatMixedStringVarRejected : Bool :=
  Result.isError (SourceUnit.check badBytesConcatMixedStringVarSource)

def bytesConcatStringArgDisciplineMatches : Bool :=
  bytesConcatStringLiteralAccepted &&
    bytesConcatUnicodeLiteralAccepted &&
    badBytesConcatStringVarRejected &&
    badBytesConcatMixedStringVarRejected

def stringReturnFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    returns :=
      [ { name := none
          ty := Solidity.Ty.string
          location := some Solidity.DataLocation.memory } ] }

def stringConcatSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "StringConcat"
            items :=
              [ Solidity.ContractItem.function
                  { stringReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "string")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.string "a"))
                              , Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.unicodeString
                                      "é")) ]))) } ] } ] }

def stringConcatAccepted : Bool :=
  sourceUnitAccepted? stringConcatSource

def badStringConcatBytesSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStringConcatBytes"
            items :=
              [ Solidity.ContractItem.function
                  { stringReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "string")
                                "concat")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.bytes
                                      [1])) ]))) } ] } ] }

def badStringConcatBytesRejected : Bool :=
  Result.isError (SourceUnit.check badStringConcatBytesSource)

def badStringConcatNamedSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadStringConcatNamed"
            items :=
              [ Solidity.ContractItem.function
                  { stringReturnFunction with
                    name := some "join"
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "string")
                                "concat")
                              [ Solidity.Arg.named "x"
                                  (Solidity.Expr.literal
                                    (Solidity.Literal.string
                                      "a")) ]))) } ] } ] }

def badStringConcatNamedRejected : Bool :=
  Result.isError (SourceUnit.check badStringConcatNamedSource)

def concatBuiltinDisciplineMatches : Bool :=
  bytesConcatAccepted &&
    stringConcatAccepted &&
    badBytesConcatRejected &&
    badBytesConcatNamedRejected &&
    badStringConcatBytesRejected &&
    badStringConcatNamedRejected

def encodeCallTargetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "set"
    params := [{ name := some "value", ty := uint256, location := none }]
    returns := []
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.nonpayable
    body := some Solidity.Stmt.empty }

def abiEncodeCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "AbiEncodeCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident "target")
                                    "set")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallSource

def abiEncodeCallWithPointer
    (functionPointer : Solidity.Expr) :
    Solidity.Expr :=
  Solidity.Expr.call
    (Solidity.Expr.member
      (Solidity.Expr.ident "abi") "encodeCall")
    [ Solidity.Arg.positional functionPointer
    , Solidity.Arg.positional
        (Solidity.Expr.tuple
          [Solidity.TupleItem.value oneExpr]) ]

def abiEncodeCallPointerPayloadFunction
    (name : Name) (mutability : Solidity.StateMutability)
    (params : List Solidity.Parameter)
    (functionPointer : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some name
    params := params
    mutability := mutability
    body :=
      some
        (Solidity.Stmt.returnValues
          (some (abiEncodeCallWithPointer functionPointer))) }

def abiEncodeCallNewTargetSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "AbiEncodeCallNewTarget"
            items :=
              [ Solidity.ContractItem.function
                  (abiEncodeCallPointerPayloadFunction
                    "payload"
                    Solidity.StateMutability.nonpayable
                    []
                    (Solidity.Expr.member
                      (Solidity.Expr.newExpr
                        (Solidity.Ty.user
                          (userPath "EncodeCallTarget")) [])
                      "set")) ] } ] }

def abiEncodeCallNewTargetAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallNewTargetSource

def badAbiEncodeCallNewTargetViewSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallNewTargetView"
            items :=
              [ Solidity.ContractItem.function
                  (abiEncodeCallPointerPayloadFunction
                    "payload"
                    Solidity.StateMutability.view
                    []
                    (Solidity.Expr.member
                      (Solidity.Expr.newExpr
                        (Solidity.Ty.user
                          (userPath "EncodeCallTarget")) [])
                      "set")) ] } ] }

def badAbiEncodeCallNewTargetViewRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallNewTargetViewSource)

def abiEncodeCallConversionTargetSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "AbiEncodeCallConversionTarget"
            items :=
              [ Solidity.ContractItem.function
                  (abiEncodeCallPointerPayloadFunction
                    "payload"
                    Solidity.StateMutability.pure
                    [ { name := some "targetAddr"
                        ty := addressTy
                        location := none } ]
                    (Solidity.Expr.member
                      (Solidity.Expr.call
                        (Solidity.Expr.typeName
                          (Solidity.Ty.user
                            (userPath "EncodeCallTarget")))
                        [Solidity.Arg.positional
                          (Solidity.Expr.ident "targetAddr")])
                      "set")) ] } ] }

def abiEncodeCallConversionTargetAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallConversionTargetSource

def badAbiEncodeCallTernaryTargetConditionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallTernaryTargetCondition"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , Solidity.ContractItem.function
                  (abiEncodeCallPointerPayloadFunction
                    "payload"
                    Solidity.StateMutability.view
                    []
                    (Solidity.Expr.member
                      (Solidity.Expr.ternary
                        (Solidity.Expr.call
                          (Solidity.Expr.typeName uint256)
                          [Solidity.Arg.positional oneExpr])
                        (Solidity.Expr.ident "target")
                        (Solidity.Expr.ident "target"))
                      "set")) ] } ] }

def badAbiEncodeCallTernaryTargetConditionRejected : Bool :=
  Result.isError
    (SourceUnit.check badAbiEncodeCallTernaryTargetConditionSource)

def otherEncodeCallTargetFunction : Solidity.FunctionDecl :=
  { encodeCallTargetFunction with name := some "set" }

def badAbiEncodeCallTernaryTargetBranchSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "OtherEncodeCallTarget"
            items := [Solidity.ContractItem.function
              otherEncodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallTernaryTargetBranch"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , Solidity.ContractItem.stateVar
                  { name := "other"
                    ty := Solidity.Ty.user
                      (userPath "OtherEncodeCallTarget") }
              , Solidity.ContractItem.function
                  (abiEncodeCallPointerPayloadFunction
                    "payload"
                    Solidity.StateMutability.view
                    [{ name := some "flag"
                       ty := Solidity.Ty.bool
                       location := none }]
                    (Solidity.Expr.member
                      (Solidity.Expr.ternary
                        (Solidity.Expr.ident "flag")
                        (Solidity.Expr.ident "target")
                        (Solidity.Expr.ident "other"))
                      "set")) ] } ] }

def badAbiEncodeCallTernaryTargetBranchRejected : Bool :=
  Result.isError
    (SourceUnit.check badAbiEncodeCallTernaryTargetBranchSource)

def badAbiEncodeCallSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "BadAbiEncodeCall"
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallTarget") }
              , Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := Solidity.StateMutability.view
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident "target")
                                    "set")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      (Solidity.Expr.literal
                                        (Solidity.Literal.bool
                                          true))]) ]))) } ] } ] }

def badAbiEncodeCallRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallSource)

def encodeCallArrayTargetFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "takeArray"
    params :=
      [{ name := some "xs"
         ty := contextualNarrowArrayTy
         location := some Solidity.DataLocation.memory }]
    returns := [{ name := none, ty := uint8, location := none }]
    visibility := some Solidity.Visibility.external_
    mutability := Solidity.StateMutability.pure
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "xs")
              (numberExpr "0")))) }

def abiEncodeCallArrayPayloadFunction
    (name : Name) (params : List Solidity.Parameter)
    (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { bytesReturnFunction with
    name := some name
    params := params
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "abi") "encodeCall")
              [ Solidity.Arg.positional
                  (Solidity.Expr.member
                    (Solidity.Expr.ident "target") "takeArray")
              , Solidity.Arg.positional
                  (Solidity.Expr.tuple
                    [Solidity.TupleItem.value arg]) ]))) }

def abiEncodeCallArraySource
    (contractName : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallArrayTarget"
            items :=
              [Solidity.ContractItem.function
                encodeCallArrayTargetFunction] }
      , Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallArrayTarget") }
              , Solidity.ContractItem.function fn ] } ] }

def contextualArrayAbiEncodeCallSource :
    Solidity.SourceUnit :=
  abiEncodeCallArraySource "ContextualArrayAbiEncodeCall"
    (abiEncodeCallArrayPayloadFunction
      "payload" [] contextualNarrowArrayExpr)

def contextualArrayAbiEncodeCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayAbiEncodeCallSource

def contextualArrayAbiEncodeCallOverflowSource :
    Solidity.SourceUnit :=
  abiEncodeCallArraySource "ContextualArrayAbiEncodeCallOverflow"
    (abiEncodeCallArrayPayloadFunction
      "payloadOverflow" [] contextualNarrowArrayOverflowExpr)

def contextualArrayAbiEncodeCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayAbiEncodeCallOverflowSource)

def contextualArrayTernaryAbiEncodeCallSource :
    Solidity.SourceUnit :=
  abiEncodeCallArraySource "ContextualArrayTernaryAbiEncodeCall"
    (abiEncodeCallArrayPayloadFunction
      "payloadTernary"
      [contextualArrayTernaryFlagParam]
      (contextualArrayTernaryExpr contextualNarrowArrayExpr))

def contextualArrayTernaryAbiEncodeCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTernaryAbiEncodeCallSource

def contextualArrayTernaryAbiEncodeCallOverflowSource :
    Solidity.SourceUnit :=
  abiEncodeCallArraySource "ContextualArrayTernaryAbiEncodeCallOverflow"
    (abiEncodeCallArrayPayloadFunction
      "payloadTernaryOverflow"
      [contextualArrayTernaryFlagParam]
      (contextualArrayTernaryExpr contextualNarrowArrayOverflowExpr))

def contextualArrayTernaryAbiEncodeCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTernaryAbiEncodeCallOverflowSource)

def contextualArrayExternalMemberCallFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "takeArray")
              [Solidity.Arg.positional arg]))) }

def contextualArrayExternalMemberCallWithOptionsFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.callWithOptions
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "takeArray")
              [Solidity.CallOption.named "gas" (numberExpr "100000")]
              [Solidity.Arg.positional arg]))) }

def contextualArrayTryExternalMemberCallFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.member
              (Solidity.Expr.ident "target") "takeArray")
            [Solidity.Arg.positional arg])
          [{ name := some "value", ty := uint8, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def contextualArrayExternalMemberSource
    (contractName : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallArrayTarget"
            items :=
              [Solidity.ContractItem.function
                encodeCallArrayTargetFunction] }
      , Solidity.SourceItem.contract
          { name := contractName
            items :=
              [ Solidity.ContractItem.stateVar
                  { name := "target"
                    ty := Solidity.Ty.user
                      (userPath "EncodeCallArrayTarget") }
              , Solidity.ContractItem.function fn ] } ] }

def contextualArrayExternalMemberCallSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource "ContextualArrayExternalMemberCall"
    (contextualArrayExternalMemberCallFunction
      "callArray" contextualNarrowArrayExpr)

def contextualArrayExternalMemberCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExternalMemberCallSource

def contextualArrayExternalMemberCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource
    "ContextualArrayExternalMemberCallOverflow"
    (contextualArrayExternalMemberCallFunction
      "callArrayOverflow" contextualNarrowArrayOverflowExpr)

def contextualArrayExternalMemberCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayExternalMemberCallOverflowSource)

def contextualArrayExternalMemberCallWithOptionsSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource
    "ContextualArrayExternalMemberCallWithOptions"
    (contextualArrayExternalMemberCallWithOptionsFunction
      "callArrayWithOptions" contextualNarrowArrayExpr)

def contextualArrayExternalMemberCallWithOptionsAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExternalMemberCallWithOptionsSource

def contextualArrayExternalMemberNamedCallFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "target") "takeArray")
              [arg]))) }

def contextualArrayExternalMemberNamedCallSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource "ContextualArrayExternalMemberNamedCall"
    (contextualArrayExternalMemberNamedCallFunction
      "callNamedArray"
      (Solidity.Arg.named "xs" contextualNarrowArrayExpr))

def contextualArrayExternalMemberNamedCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExternalMemberNamedCallSource

def contextualArrayExternalMemberNamedCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource
    "ContextualArrayExternalMemberNamedCallOverflow"
    (contextualArrayExternalMemberNamedCallFunction
      "callNamedArrayOverflow"
      (Solidity.Arg.named "xs"
        contextualNarrowArrayOverflowExpr))

def contextualArrayExternalMemberNamedCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayExternalMemberNamedCallOverflowSource)

def contextualArrayTryExternalMemberCallSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource "ContextualArrayTryExternalMemberCall"
    (contextualArrayTryExternalMemberCallFunction
      "tryArray" contextualNarrowArrayExpr)

def contextualArrayTryExternalMemberCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTryExternalMemberCallSource

def contextualArrayTryExternalMemberCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayExternalMemberSource
    "ContextualArrayTryExternalMemberCallOverflow"
    (contextualArrayTryExternalMemberCallFunction
      "tryArrayOverflow" contextualNarrowArrayOverflowExpr)

def contextualArrayTryExternalMemberCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTryExternalMemberCallOverflowSource)

def contextualArrayExternalFunctionValueTy : Ty :=
  Solidity.Ty.functionWithLocations
    [contextualNarrowArrayTy]
    [some Solidity.DataLocation.memory]
    [uint8] [none]
    Solidity.StateMutability.view
    Solidity.Visibility.external_

def contextualArrayExternalFunctionValueCallFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    params :=
      [{ name := some "getter"
         ty := contextualArrayExternalFunctionValueTy
         location := none }]
    mutability := Solidity.StateMutability.view
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.ident "getter")
              [Solidity.Arg.positional arg]))) }

def contextualArrayExternalFunctionValueCallWithOptionsFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { contextualArrayExternalFunctionValueCallFunction name arg with
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.callWithOptions
              (Solidity.Expr.ident "getter")
              [Solidity.CallOption.named "gas" (numberExpr "100000")]
              [Solidity.Arg.positional arg]))) }

def contextualArrayTryExternalFunctionValueCallFunction
    (name : Name) (arg : Solidity.Expr) :
    Solidity.FunctionDecl :=
  { contextualArrayExternalFunctionValueCallFunction name arg with
    body :=
      some
        (Solidity.Stmt.tryCatchReturns
          (Solidity.Expr.call
            (Solidity.Expr.ident "getter")
            [Solidity.Arg.positional arg])
          [{ name := some "value", ty := uint8, location := none }]
          (Solidity.Stmt.returnValues
            (some (Solidity.Expr.ident "value")))
          [tryCatchZeroClause]) }

def contextualArrayExternalFunctionValueSource
    (contractName : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := contractName
            items := [Solidity.ContractItem.function fn] } ] }

def contextualArrayExternalFunctionValueCallSource :
    Solidity.SourceUnit :=
  contextualArrayExternalFunctionValueSource
    "ContextualArrayExternalFunctionValueCall"
    (contextualArrayExternalFunctionValueCallFunction
      "callArray" contextualNarrowArrayExpr)

def contextualArrayExternalFunctionValueCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExternalFunctionValueCallSource

def contextualArrayExternalFunctionValueCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayExternalFunctionValueSource
    "ContextualArrayExternalFunctionValueCallOverflow"
    (contextualArrayExternalFunctionValueCallFunction
      "callArrayOverflow" contextualNarrowArrayOverflowExpr)

def contextualArrayExternalFunctionValueCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayExternalFunctionValueCallOverflowSource)

def contextualArrayExternalFunctionValueCallWithOptionsSource :
    Solidity.SourceUnit :=
  contextualArrayExternalFunctionValueSource
    "ContextualArrayExternalFunctionValueCallWithOptions"
    (contextualArrayExternalFunctionValueCallWithOptionsFunction
      "callArrayWithOptions" contextualNarrowArrayExpr)

def contextualArrayExternalFunctionValueCallWithOptionsAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExternalFunctionValueCallWithOptionsSource

def contextualArrayTryExternalFunctionValueCallSource :
    Solidity.SourceUnit :=
  contextualArrayExternalFunctionValueSource
    "ContextualArrayTryExternalFunctionValueCall"
    (contextualArrayTryExternalFunctionValueCallFunction
      "tryArray" contextualNarrowArrayExpr)

def contextualArrayTryExternalFunctionValueCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayTryExternalFunctionValueCallSource

def contextualArrayTryExternalFunctionValueCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayExternalFunctionValueSource
    "ContextualArrayTryExternalFunctionValueCallOverflow"
    (contextualArrayTryExternalFunctionValueCallFunction
      "tryArrayOverflow" contextualNarrowArrayOverflowExpr)

def contextualArrayTryExternalFunctionValueCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayTryExternalFunctionValueCallOverflowSource)

def contextualArrayDirectLibraryFunction :
    Solidity.FunctionDecl :=
  { encodeCallArrayTargetFunction with
    visibility := some Solidity.Visibility.public_ }

def contextualArrayDirectLibraryContract :
    Solidity.ContractDecl :=
  { kind := Solidity.ContractKind.library
    name := "ContextualArrayDirectLib"
    items :=
      [Solidity.ContractItem.function
        contextualArrayDirectLibraryFunction] }

def contextualArrayDirectLibraryCallFunction
    (name : Name) (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member
                (Solidity.Expr.ident "ContextualArrayDirectLib")
                "takeArray")
              [arg]))) }

def contextualArrayDirectLibrarySource
    (contractName : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayDirectLibraryContract
      , Solidity.SourceItem.contract
          { name := contractName
            items := [Solidity.ContractItem.function fn] } ] }

def contextualArrayDirectLibraryCallSource :
    Solidity.SourceUnit :=
  contextualArrayDirectLibrarySource "ContextualArrayDirectLibraryCall"
    (contextualArrayDirectLibraryCallFunction
      "callArray"
      (Solidity.Arg.positional contextualNarrowArrayExpr))

def contextualArrayDirectLibraryCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayDirectLibraryCallSource

def contextualArrayDirectLibraryCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayDirectLibrarySource
    "ContextualArrayDirectLibraryCallOverflow"
    (contextualArrayDirectLibraryCallFunction
      "callArrayOverflow"
      (Solidity.Arg.positional
        contextualNarrowArrayOverflowExpr))

def contextualArrayDirectLibraryCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayDirectLibraryCallOverflowSource)

def contextualArrayDirectLibraryNamedCallSource :
    Solidity.SourceUnit :=
  contextualArrayDirectLibrarySource "ContextualArrayDirectLibraryNamedCall"
    (contextualArrayDirectLibraryCallFunction
      "callNamedArray"
      (Solidity.Arg.named "xs" contextualNarrowArrayExpr))

def contextualArrayDirectLibraryNamedCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayDirectLibraryNamedCallSource

def contextualArrayDirectLibraryNamedCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayDirectLibrarySource
    "ContextualArrayDirectLibraryNamedCallOverflow"
    (contextualArrayDirectLibraryCallFunction
      "callNamedArrayOverflow"
      (Solidity.Arg.named "xs"
        contextualNarrowArrayOverflowExpr))

def contextualArrayDirectLibraryNamedCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayDirectLibraryNamedCallOverflowSource)

def contextualArrayBaseMemberFunction :
    Solidity.FunctionDecl :=
  { encodeCallArrayTargetFunction with
    visibility := some Solidity.Visibility.public_
    virtual := true }

def contextualArrayBaseOverrideFunction :
    Solidity.FunctionDecl :=
  { contextualArrayBaseMemberFunction with
    override? := some {}
    virtual := false
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.index
              (Solidity.Expr.ident "xs")
              (numberExpr "1")))) }

def contextualArrayBaseMemberBaseContract :
    Solidity.ContractDecl :=
  { name := "ContextualArrayMemberBase"
    items :=
      [Solidity.ContractItem.function
        contextualArrayBaseMemberFunction] }

def contextualArrayInheritedMemberCallFunction
    (name : Name) (target : Solidity.Expr)
    (arg : Solidity.Arg) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    returns := [{ name := none, ty := uint8, location := none }]
    body :=
      some
        (Solidity.Stmt.returnValues
          (some
            (Solidity.Expr.call
              (Solidity.Expr.member target "takeArray")
              [arg]))) }

def contextualArrayInheritedMemberSource
    (contractName : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          contextualArrayBaseMemberBaseContract
      , Solidity.SourceItem.contract
          { name := contractName
            bases := [{ base := userPath "ContextualArrayMemberBase" }]
            items :=
              [ Solidity.ContractItem.function
                  contextualArrayBaseOverrideFunction
              , Solidity.ContractItem.function fn ] } ] }

def contextualArrayExplicitBaseCallSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArrayExplicitBaseCall"
    (contextualArrayInheritedMemberCallFunction
      "callBaseArray"
      (Solidity.Expr.ident "ContextualArrayMemberBase")
      (Solidity.Arg.positional contextualNarrowArrayExpr))

def contextualArrayExplicitBaseCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExplicitBaseCallSource

def contextualArrayExplicitBaseCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource
    "ContextualArrayExplicitBaseCallOverflow"
    (contextualArrayInheritedMemberCallFunction
      "callBaseArrayOverflow"
      (Solidity.Expr.ident "ContextualArrayMemberBase")
      (Solidity.Arg.positional
        contextualNarrowArrayOverflowExpr))

def contextualArrayExplicitBaseCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayExplicitBaseCallOverflowSource)

def contextualArrayExplicitBaseNamedCallSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArrayExplicitBaseNamedCall"
    (contextualArrayInheritedMemberCallFunction
      "callNamedBaseArray"
      (Solidity.Expr.ident "ContextualArrayMemberBase")
      (Solidity.Arg.named "xs" contextualNarrowArrayExpr))

def contextualArrayExplicitBaseNamedCallAccepted : Bool :=
  sourceUnitAccepted? contextualArrayExplicitBaseNamedCallSource

def contextualArrayExplicitBaseNamedCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource
    "ContextualArrayExplicitBaseNamedCallOverflow"
    (contextualArrayInheritedMemberCallFunction
      "callNamedBaseArrayOverflow"
      (Solidity.Expr.ident "ContextualArrayMemberBase")
      (Solidity.Arg.named "xs"
        contextualNarrowArrayOverflowExpr))

def contextualArrayExplicitBaseNamedCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArrayExplicitBaseNamedCallOverflowSource)

def contextualArraySuperCallSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArraySuperCall"
    (contextualArrayInheritedMemberCallFunction
      "callSuperArray"
      (Solidity.Expr.ident "super")
      (Solidity.Arg.positional contextualNarrowArrayExpr))

def contextualArraySuperCallAccepted : Bool :=
  sourceUnitAccepted? contextualArraySuperCallSource

def contextualArraySuperCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArraySuperCallOverflow"
    (contextualArrayInheritedMemberCallFunction
      "callSuperArrayOverflow"
      (Solidity.Expr.ident "super")
      (Solidity.Arg.positional
        contextualNarrowArrayOverflowExpr))

def contextualArraySuperCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArraySuperCallOverflowSource)

def contextualArraySuperNamedCallSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArraySuperNamedCall"
    (contextualArrayInheritedMemberCallFunction
      "callNamedSuperArray"
      (Solidity.Expr.ident "super")
      (Solidity.Arg.named "xs" contextualNarrowArrayExpr))

def contextualArraySuperNamedCallAccepted : Bool :=
  sourceUnitAccepted? contextualArraySuperNamedCallSource

def contextualArraySuperNamedCallOverflowSource :
    Solidity.SourceUnit :=
  contextualArrayInheritedMemberSource "ContextualArraySuperNamedCallOverflow"
    (contextualArrayInheritedMemberCallFunction
      "callNamedSuperArrayOverflow"
      (Solidity.Expr.ident "super")
      (Solidity.Arg.named "xs"
        contextualNarrowArrayOverflowExpr))

def contextualArraySuperNamedCallOverflowRejected : Bool :=
  Result.isError (SourceUnit.check
    contextualArraySuperNamedCallOverflowSource)

def abiEncodeCallTypeNameSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "EncodeCallTarget"
            items := [Solidity.ContractItem.function
              encodeCallTargetFunction] }
      , Solidity.SourceItem.contract
          { name := "AbiEncodeCallTypeName"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.member
                                    (Solidity.Expr.typeName
                                      (Solidity.Ty.user
                                        (userPath "EncodeCallTarget")))
                                    "set")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallTypeNameAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallTypeNameSource

def externalUintSetterFunctionTy : Ty :=
  Solidity.Ty.function [uint256] []
    Solidity.StateMutability.nonpayable
    Solidity.Visibility.external_

def internalUintSetterFunctionTy : Ty :=
  Solidity.Ty.function [uint256] []
    Solidity.StateMutability.nonpayable
    Solidity.Visibility.internal_

def abiEncodeCallExternalFunctionPointerSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "AbiEncodeCallExternalPointer"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    params :=
                      [ { name := some "setter"
                          ty := externalUintSetterFunctionTy
                          location := none } ]
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident "setter")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def abiEncodeCallExternalFunctionPointerAccepted : Bool :=
  sourceUnitAccepted? abiEncodeCallExternalFunctionPointerSource

def externalFunctionPointerMembersSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "ExternalFunctionPointerMembers"
            items :=
              [ Solidity.ContractItem.function
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
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.tuple
                              [ Solidity.TupleItem.value
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident
                                      "setter")
                                    "selector")
                              , Solidity.TupleItem.value
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident
                                      "setter")
                                    "address") ]))) } ] } ] }

def externalFunctionPointerMembersAccepted : Bool :=
  sourceUnitAccepted? externalFunctionPointerMembersSource

def badInternalFunctionPointerSelectorSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadInternalFunctionPointerSelector"
            items :=
              [ Solidity.ContractItem.function
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
                      some Solidity.Visibility.internal_
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.member
                              (Solidity.Expr.ident "setter")
                              "selector"))) } ] } ] }

def badInternalFunctionPointerSelectorRejected : Bool :=
  Result.isError
    (SourceUnit.check badInternalFunctionPointerSelectorSource)

def badAbiEncodeCallInternalFunctionPointerSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallInternalPointer"
            items :=
              [ Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    params :=
                      [ { name := some "setter"
                          ty := internalUintSetterFunctionTy
                          location := none } ]
                    visibility :=
                      some Solidity.Visibility.internal_
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident "setter")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallInternalFunctionPointerRejected : Bool :=
  Result.isError
    (SourceUnit.check badAbiEncodeCallInternalFunctionPointerSource)

def badAbiEncodeCallBareFunctionSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallBareFunction"
            items :=
              [ Solidity.ContractItem.function
                  encodeCallTargetFunction
              , Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.ident "set")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallBareFunctionRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallBareFunctionSource)

def badAbiEncodeCallThisInPureSource :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadAbiEncodeCallThisInPure"
            items :=
              [ Solidity.ContractItem.function
                  encodeCallTargetFunction
              , Solidity.ContractItem.function
                  { bytesReturnFunction with
                    name := some "payload"
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.member
                                (Solidity.Expr.ident "abi")
                                "encodeCall")
                              [ Solidity.Arg.positional
                                  (Solidity.Expr.member
                                    (Solidity.Expr.ident "this")
                                    "set")
                              , Solidity.Arg.positional
                                  (Solidity.Expr.tuple
                                    [Solidity.TupleItem.value
                                      oneExpr]) ]))) } ] } ] }

def badAbiEncodeCallThisInPureRejected : Bool :=
  Result.isError (SourceUnit.check badAbiEncodeCallThisInPureSource)

def badPureAddressThisSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract
          { name := "BadPureAddressThis"
            items :=
              [ Solidity.ContractItem.function
                  { simpleReturnFunction with
                    name := some "self"
                    returns :=
                      [ { name := none
                          ty := addressTy
                          location := none } ]
                    mutability := Solidity.StateMutability.pure
                    body :=
                      some
                        (Solidity.Stmt.returnValues
                          (some
                            (Solidity.Expr.call
                              (Solidity.Expr.typeName addressTy)
                              [Solidity.Arg.positional
                                (Solidity.Expr.ident
                                  "this")]))) } ] } ] }

def badPureAddressThisRejected : Bool :=
  Result.isError (SourceUnit.check badPureAddressThisSource)

def localPointerBinding (name : Name)
    (location : Solidity.DataLocation) :
    Solidity.VarBinding :=
  { name := some name
    ty := some Solidity.Ty.bytes
    location := some location }

def localPointerAssign (name source : Name) : Solidity.Stmt :=
  Solidity.Stmt.expr
    (Solidity.Expr.assign
      (Solidity.Expr.ident name)
      Solidity.AssignOp.assign
      (Solidity.Expr.ident source))

def localPointerLengthReturn (name : Name) : Solidity.Stmt :=
  Solidity.Stmt.returnValues
    (some
      (Solidity.Expr.member
        (Solidity.Expr.ident name) "length"))

def localPointerFunction (name : Name)
    (mutability : Solidity.StateMutability)
    (params : List Solidity.Parameter)
    (body : List Solidity.Stmt) :
    Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some name
    visibility := some Solidity.Visibility.external_
    mutability := mutability
    params := params
    returns := [{ name := none, ty := uint256 }]
    body := some (Solidity.Stmt.block body) }

def localPointerStateVar (name : Name) :
    Solidity.StateVarDecl :=
  { name := name
    ty := Solidity.Ty.bytes
    visibility := some Solidity.Visibility.private_ }

def localPointerSource (name : Name)
    (items : List Solidity.ContractItem) :
    Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := name, items := items }] }

def delayedStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "DelayedStorageLocal"
    [ Solidity.ContractItem.stateVar
        (localPointerStateVar "value")
    , Solidity.ContractItem.function
        (localPointerFunction "read" Solidity.StateMutability.view []
          [ Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.storage] none
          , localPointerAssign "pointer" "value"
          , localPointerLengthReturn "pointer" ]) ]

def branchedStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "BranchedStorageLocal"
    [ Solidity.ContractItem.stateVar
        (localPointerStateVar "left")
    , Solidity.ContractItem.stateVar
        (localPointerStateVar "right")
    , Solidity.ContractItem.function
        (localPointerFunction "read" Solidity.StateMutability.view
          [{ name := some "choose", ty := Solidity.Ty.bool }]
          [ Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.storage] none
          , Solidity.Stmt.ifElse
              (Solidity.Expr.ident "choose")
              (localPointerAssign "pointer" "left")
              (some (localPointerAssign "pointer" "right"))
          , localPointerLengthReturn "pointer" ]) ]

def delayedCalldataLocalSource : Solidity.SourceUnit :=
  localPointerSource "DelayedCalldataLocal"
    [Solidity.ContractItem.function
      (localPointerFunction "read" Solidity.StateMutability.pure
        [ { name := some "input"
            ty := Solidity.Ty.bytes
            location := some Solidity.DataLocation.calldata } ]
        [ Solidity.Stmt.varDecl
            [localPointerBinding "pointer"
              Solidity.DataLocation.calldata] none
        , localPointerAssign "pointer" "input"
        , localPointerLengthReturn "pointer" ])]

def unusedPointerLocalsSource : Solidity.SourceUnit :=
  localPointerSource "UnusedPointerLocals"
    [Solidity.ContractItem.function
      { simpleReturnFunction with
        name := some "unused"
        visibility := some Solidity.Visibility.external_
        mutability := Solidity.StateMutability.pure
        body :=
          some
            (Solidity.Stmt.block
              [ Solidity.Stmt.varDecl
                  [localPointerBinding "storagePointer"
                    Solidity.DataLocation.storage] none
              , Solidity.Stmt.varDecl
                  [localPointerBinding "calldataPointer"
                    Solidity.DataLocation.calldata] none ]) }]

def shadowedPointerLocalSource : Solidity.SourceUnit :=
  localPointerSource "ShadowedPointerLocal"
    [Solidity.ContractItem.function
      (localPointerFunction "read" Solidity.StateMutability.pure
        [ { name := some "input"
            ty := Solidity.Ty.bytes
            location := some Solidity.DataLocation.calldata } ]
        [ Solidity.Stmt.varDecl
            [localPointerBinding "pointer"
              Solidity.DataLocation.calldata]
            (some (Solidity.Expr.ident "input"))
        , Solidity.Stmt.block
            [Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.calldata] none]
        , localPointerLengthReturn "pointer" ])]

def doWhileAssignedStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "DoWhileAssignedStorageLocal"
    [ Solidity.ContractItem.stateVar
        (localPointerStateVar "value")
    , Solidity.ContractItem.function
        (localPointerFunction "read" Solidity.StateMutability.view []
          [ Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.storage] none
          , Solidity.Stmt.doWhile
              (localPointerAssign "pointer" "value")
              (Solidity.Expr.literal
                (Solidity.Literal.bool false))
          , localPointerLengthReturn "pointer" ]) ]

def unsafeStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "UnsafeStorageLocal"
    [Solidity.ContractItem.function
      (localPointerFunction "bad" Solidity.StateMutability.pure []
        [ Solidity.Stmt.varDecl
            [localPointerBinding "pointer"
              Solidity.DataLocation.storage] none
        , localPointerLengthReturn "pointer" ])]

def unsafeCalldataLocalSource : Solidity.SourceUnit :=
  localPointerSource "UnsafeCalldataLocal"
    [Solidity.ContractItem.function
      (localPointerFunction "bad" Solidity.StateMutability.pure []
        [ Solidity.Stmt.varDecl
            [localPointerBinding "pointer"
              Solidity.DataLocation.calldata] none
        , localPointerLengthReturn "pointer" ])]

def partialStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "PartialStorageLocal"
    [ Solidity.ContractItem.stateVar
        (localPointerStateVar "value")
    , Solidity.ContractItem.function
        (localPointerFunction "bad" Solidity.StateMutability.view
          [{ name := some "choose", ty := Solidity.Ty.bool }]
          [ Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.storage] none
          , Solidity.Stmt.ifElse
              (Solidity.Expr.ident "choose")
              (localPointerAssign "pointer" "value") none
          , localPointerLengthReturn "pointer" ]) ]

def loopAssignedStorageLocalSource : Solidity.SourceUnit :=
  localPointerSource "LoopAssignedStorageLocal"
    [ Solidity.ContractItem.stateVar
        (localPointerStateVar "value")
    , Solidity.ContractItem.function
        (localPointerFunction "bad" Solidity.StateMutability.view []
          [ Solidity.Stmt.varDecl
              [localPointerBinding "pointer"
                Solidity.DataLocation.storage] none
          , Solidity.Stmt.whileLoop
              (Solidity.Expr.literal
                (Solidity.Literal.bool true))
              (Solidity.Stmt.block
                [ localPointerAssign "pointer" "value"
                , Solidity.Stmt.break ])
          , localPointerLengthReturn "pointer" ]) ]

def localPointerDefiniteAssignmentDisciplineMatches : Bool :=
  sourceUnitAccepted? delayedStorageLocalSource &&
    sourceUnitAccepted? branchedStorageLocalSource &&
    sourceUnitAccepted? delayedCalldataLocalSource &&
    sourceUnitAccepted? unusedPointerLocalsSource &&
    sourceUnitAccepted? shadowedPointerLocalSource &&
    sourceUnitAccepted? doWhileAssignedStorageLocalSource &&
    Result.isError (SourceUnit.check unsafeStorageLocalSource) &&
    Result.isError (SourceUnit.check unsafeCalldataLocalSource) &&
    Result.isError (SourceUnit.check partialStorageLocalSource) &&
    Result.isError (SourceUnit.check loopAssignedStorageLocalSource)

def nominalAliasPairStructDecl : Solidity.StructDecl :=
  { name := "Pair"
    fields :=
      [ { name := "a", ty := Solidity.Ty.uint 256 } ] }

def nominalAliasOtherContract : Solidity.ContractDecl :=
  { name := "Other"
    items :=
      [ Solidity.ContractItem.structDecl
          nominalAliasPairStructDecl ] }

def nominalAliasCurrentTypes : TypeContext :=
  (TypeContext.empty.withSourceTypes
    [nominalAliasOtherContract] [] [] []).withContractTypes
      "Current" [nominalAliasPairStructDecl] [] []

def nominalLocalUserAliasDisciplineMatches : Bool :=
  TypeContext.canImplicitlyConvert nominalAliasCurrentTypes
    (Solidity.Ty.user
      (TypeContext.qualifiedPath "Current" "Pair"))
    (Solidity.Ty.user (TypeContext.pathOfName "Pair")) &&
  TypeContext.canImplicitlyConvert nominalAliasCurrentTypes
    (Solidity.Ty.user (TypeContext.pathOfName "Pair"))
    (Solidity.Ty.user
      (TypeContext.qualifiedPath "Current" "Pair")) &&
  !TypeContext.canImplicitlyConvert nominalAliasCurrentTypes
    (Solidity.Ty.user
      (TypeContext.qualifiedPath "Other" "Pair"))
    (Solidity.Ty.user (TypeContext.pathOfName "Pair"))

-- ===========================================================================
-- Acceptance-soundness tightening (2026-07-08): signed/unsigned integer and
-- contract-hierarchy conversion boundaries. Each Ax mirrors a solc-REJECT
-- fixture under tests/forge-harness/signed-unsigned-contract-conversions/
-- plus a still-accepted neighbor. See docs/DECISIONS.md.
-- ===========================================================================

def su_uint8 : Ty := Solidity.Ty.uint 8
def su_uint16 : Ty := Solidity.Ty.uint 16
def su_uint256 : Ty := Solidity.Ty.uint 256
def su_int16 : Ty := Solidity.Ty.int 16
def su_int256 : Ty := Solidity.Ty.int 256
def su_bytes32 : Ty := Solidity.Ty.bytesN 32

def su_singleContract (name : Name) (fn : Solidity.FunctionDecl) :
    Solidity.SourceUnit :=
  { items :=
      [Solidity.SourceItem.contract
        { name := name
          items := [Solidity.ContractItem.function fn] }] }

def su_castExpr (ty : Ty) (arg : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.call (Solidity.Expr.typeName ty)
    [Solidity.Arg.positional arg]

-- A1: implicit uint8 -> int16 (return position) is REJECTED.
def a1ImplicitUintToIntFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := su_uint8, location := none }]
    returns := [{ name := none, ty := su_int16, location := none }]
    body :=
      some (Solidity.Stmt.returnValues (some (Solidity.Expr.ident "a"))) }

def a1ImplicitUintToIntRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "A1ImplicitUintToInt" a1ImplicitUintToIntFunction))

-- A1 neighbor: explicit int16(uint16(a)) STILL ACCEPTED.
def a1ExplicitCastFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := su_uint8, location := none }]
    returns := [{ name := none, ty := su_int16, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr su_int16 (su_castExpr su_uint16
          (Solidity.Expr.ident "a"))))) }

def a1ExplicitCastAccepted : Bool :=
  sourceUnitAccepted?
    (su_singleContract "A1ExplicitCast" a1ExplicitCastFunction)

-- A2: uint8 + int16 with both operands non-literal is REJECTED (no common type).
def a2MixedSignAddFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "a", ty := su_uint8, location := none }
      , { name := some "b", ty := su_int16, location := none } ]
    returns := [{ name := none, ty := su_int16, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.binary Solidity.BinaryOp.add
          (Solidity.Expr.ident "a") (Solidity.Expr.ident "b")))) }

def a2MixedSignAddRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "A2MixedSignAdd" a2MixedSignAddFunction))

-- A2 neighbor: a number literal takes the other operand's type; uint8(x) + 2
-- and 1 + int16(x) STILL ACCEPTED.
def a2UintPlusLiteralFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "a", ty := su_uint8, location := none }]
    returns := [{ name := none, ty := su_uint8, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.binary Solidity.BinaryOp.add
          (Solidity.Expr.ident "a") (numberExpr "2")))) }

def a2LiteralPlusIntFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    params := [{ name := some "b", ty := su_int16, location := none }]
    returns := [{ name := none, ty := su_int16, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.binary Solidity.BinaryOp.add
          (numberExpr "1") (Solidity.Expr.ident "b")))) }

def a2LiteralMixedAccepted : Bool :=
  sourceUnitAccepted?
      (su_singleContract "A2UintPlusLiteral" a2UintPlusLiteralFunction) &&
    sourceUnitAccepted?
      (su_singleContract "A2LiteralPlusInt" a2LiteralPlusIntFunction)

-- A3: bytes32 -> int256 and int256 -> bytes32 explicit casts are REJECTED.
def a3BytesToSignedIntFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "x", ty := su_bytes32, location := none }]
    returns := [{ name := none, ty := su_int256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr su_int256 (Solidity.Expr.ident "x")))) }

def a3SignedIntToBytesFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "x", ty := su_int256, location := none }]
    returns := [{ name := none, ty := su_bytes32, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr su_bytes32 (Solidity.Expr.ident "x")))) }

def a3SignedBytesConversionsRejected : Bool :=
  Result.isError
      (SourceUnit.check
        (su_singleContract "A3BytesToSignedInt" a3BytesToSignedIntFunction)) &&
    Result.isError
      (SourceUnit.check
        (su_singleContract "A3SignedIntToBytes" a3SignedIntToBytesFunction))

-- A3 neighbor: same-width UNSIGNED casts uint256(bytes32) and bytes32(uint256)
-- STILL ACCEPTED.
def a3BytesToUnsignedIntFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "x", ty := su_bytes32, location := none }]
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr su_uint256 (Solidity.Expr.ident "x")))) }

def a3UnsignedIntToBytesFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    params := [{ name := some "x", ty := su_uint256, location := none }]
    returns := [{ name := none, ty := su_bytes32, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr su_bytes32 (Solidity.Expr.ident "x")))) }

def a3UnsignedBytesConversionsAccepted : Bool :=
  sourceUnitAccepted?
      (su_singleContract "A3BytesToUnsignedInt" a3BytesToUnsignedIntFunction) &&
    sourceUnitAccepted?
      (su_singleContract "A3UnsignedIntToBytes" a3UnsignedIntToBytesFunction)

-- A4: base->derived (down-cast) explicit contract conversion is REJECTED.
def a4BaseContract : Solidity.ContractDecl :=
  { name := "Base", items := [] }

def a4DerivedContract : Solidity.ContractDecl :=
  { name := "Derived"
    bases := [{ base := userPath "Base" }]
    items := [] }

def a4BaseTy : Ty := Solidity.Ty.user (userPath "Base")
def a4DerivedTy : Ty := Solidity.Ty.user (userPath "Derived")

def a4DownCastFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "b", ty := a4BaseTy, location := none }]
    returns := [{ name := none, ty := a4DerivedTy, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr a4DerivedTy (Solidity.Expr.ident "b")))) }

def a4DownCastSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract a4BaseContract
      , Solidity.SourceItem.contract a4DerivedContract
      , Solidity.SourceItem.contract
          { name := "A4BaseToDerived"
            items := [Solidity.ContractItem.function a4DownCastFunction] } ] }

def a4DownCastRejected : Bool :=
  Result.isError (SourceUnit.check a4DownCastSource)

-- A4 neighbor: derived->base (up-cast) STILL ACCEPTED.
def a4UpCastFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params := [{ name := some "d", ty := a4DerivedTy, location := none }]
    returns := [{ name := none, ty := a4BaseTy, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (su_castExpr a4BaseTy (Solidity.Expr.ident "d")))) }

def a4UpCastSource : Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract a4BaseContract
      , Solidity.SourceItem.contract a4DerivedContract
      , Solidity.SourceItem.contract
          { name := "A4DerivedToBase"
            items := [Solidity.ContractItem.function a4UpCastFunction] } ] }

def a4UpCastAccepted : Bool :=
  sourceUnitAccepted? a4UpCastSource

-- ---------------------------------------------------------------------------
-- Completeness boundaries C1–C4 (2026-07-08). solc v0.8.35 citations in each
-- block; each pins the now-correct reject/accept boundary plus a still-valid
-- neighbor. C1/C2(creationCode)/C3 gates predated this work; C2-interfaceId
-- (abstract) and C4 (negative-operand constant `%`) are the genuine fixes.
-- ---------------------------------------------------------------------------

-- C1: `string.length` REJECTED. solc `ArrayType::nativeMembers` (Types.cpp)
-- adds `length` only when `!isString()`; a `string` has no `.length` — the
-- program must write `bytes(s).length`.
def c1StringLengthFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "s", ty := Solidity.Ty.string
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.member (Solidity.Expr.ident "s") "length"))) }

def c1StringLengthRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "C1StringLength" c1StringLengthFunction))

-- C1 neighbor #1: `bytes(s).length` STILL ACCEPTED.
def c1BytesLengthFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "f"
    params :=
      [ { name := some "s", ty := Solidity.Ty.string
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.member
          (su_castExpr Solidity.Ty.bytes (Solidity.Expr.ident "s"))
          "length"))) }

-- C1 neighbor #2: dynamic `uint[]` `.length` STILL ACCEPTED.
def c1ArrayLengthFunction : Solidity.FunctionDecl :=
  { simpleReturnFunction with
    name := some "g"
    params :=
      [ { name := some "a"
          ty := Solidity.Ty.array su_uint256 none
          location := some Solidity.DataLocation.memory } ]
    returns := [{ name := none, ty := su_uint256, location := none }]
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.member (Solidity.Expr.ident "a") "length"))) }

def c1LengthNeighborsAccepted : Bool :=
  sourceUnitAccepted?
      (su_singleContract "C1BytesLength" c1BytesLengthFunction) &&
    sourceUnitAccepted?
      (su_singleContract "C1ArrayLength" c1ArrayLengthFunction)

-- C2: `type(C).interfaceId` gated on deployability. solc Types.cpp:4271-4285 —
-- a NON-deployable contract (interface OR abstract) exposes `interfaceId`; a
-- deployable concrete contract does NOT.
def interfaceIdReturnFunction (target : Name) : Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some "f"
    returns :=
      [ { name := none, ty := Solidity.Ty.bytesN 4, location := none } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.member
          (Solidity.Expr.typeName
            (Solidity.Ty.user (userPath target)))
          "interfaceId"))) }

def c2InterfaceIdSource (target : Solidity.ContractDecl) (reader : Name) :
    Solidity.SourceUnit :=
  { items :=
      [ Solidity.SourceItem.contract target
      , Solidity.SourceItem.contract
          { name := reader
            items :=
              [ Solidity.ContractItem.function
                  (interfaceIdReturnFunction target.name) ] } ] }

def c2ConcreteInterfaceIdSource : Solidity.SourceUnit :=
  c2InterfaceIdSource { name := "C2Concrete" } "C2ConcreteReader"

def c2InterfaceInterfaceIdSource : Solidity.SourceUnit :=
  c2InterfaceIdSource
    { kind := Solidity.ContractKind.interface, name := "C2Interface" }
    "C2InterfaceReader"

def c2AbstractInterfaceIdSource : Solidity.SourceUnit :=
  c2InterfaceIdSource
    { name := "C2Abstract", abstract := true } "C2AbstractReader"

-- concrete contract `type(D).interfaceId` REJECTED …
def c2ConcreteInterfaceIdRejected : Bool :=
  Result.isError (SourceUnit.check c2ConcreteInterfaceIdSource)

-- … while interface and abstract `type(T).interfaceId` STAY ACCEPTED.
def c2NonDeployableInterfaceIdAccepted : Bool :=
  sourceUnitAccepted? c2InterfaceInterfaceIdSource &&
    sourceUnitAccepted? c2AbstractInterfaceIdSource

-- C3: `abi.encodePacked` of an array whose element is dynamically sized
-- (`bytes[]`, `string[]`, `T[][]`) is REJECTED in packed mode; an array of
-- static-width elements (`uint[]`) is ACCEPTED.
def c3PackedFunction (elementTy : Ty) (fnName : Name) :
    Solidity.FunctionDecl :=
  { kind := Solidity.FunctionKind.function
    name := some fnName
    params :=
      [ { name := some "a"
          ty := Solidity.Ty.array elementTy none
          location := some Solidity.DataLocation.memory } ]
    returns :=
      [ { name := none, ty := Solidity.Ty.bytes
          location := some Solidity.DataLocation.memory } ]
    visibility := some Solidity.Visibility.public_
    mutability := Solidity.StateMutability.pure
    body :=
      some (Solidity.Stmt.returnValues
        (some (Solidity.Expr.call
          (Solidity.Expr.member (Solidity.Expr.ident "abi") "encodePacked")
          [Solidity.Arg.positional (Solidity.Expr.ident "a")]))) }

def c3PackedBytesArrayRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "C3PackedBytesArray"
        (c3PackedFunction Solidity.Ty.bytes "f")))

def c3PackedStringArrayRejected : Bool :=
  Result.isError
    (SourceUnit.check
      (su_singleContract "C3PackedStringArray"
        (c3PackedFunction Solidity.Ty.string "f")))

def c3PackedDynamicArraysRejected : Bool :=
  c3PackedBytesArrayRejected && c3PackedStringArrayRejected

-- C3 neighbor: `abi.encodePacked(uint[])` (static-width elements) ACCEPTED.
def c3PackedUintArrayAccepted : Bool :=
  sourceUnitAccepted?
    (su_singleContract "C3PackedUintArray"
      (c3PackedFunction su_uint256 "f"))

-- C4: constant `%` with a negative operand is VALID and folds to the truncated
-- remainder (sign of the dividend). solc constant-expression evaluation;
-- confirmed via pinned solc `int constant x = (-7) % 3` == -1.
private def c4Neg (e : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.unary Solidity.UnaryOp.neg e
private def c4Mod (x y : Solidity.Expr) : Solidity.Expr :=
  Solidity.Expr.binary Solidity.BinaryOp.mod x y

-- (-7) % 3 == -1 ; 7 % (-3) == 1 ; (-7) % (-3) == -1  (all truncated).
def c4NegativeModFolds : Bool :=
  Solidity.Executable.Expr.numberLiteralInt?
      (c4Mod (c4Neg (numberExpr "7")) (numberExpr "3")) == some (-1) &&
    Solidity.Executable.Expr.numberLiteralInt?
      (c4Mod (numberExpr "7") (c4Neg (numberExpr "3"))) == some 1 &&
    Solidity.Executable.Expr.numberLiteralInt?
      (c4Mod (c4Neg (numberExpr "7")) (c4Neg (numberExpr "3"))) == some (-1)

-- … and each is accepted into int256 (was over-rejected before the fix).
def c4NegativeModAcceptedInt256 : Bool :=
  (Solidity.Executable.Expr.toCoreNumericLiteralAs? (Solidity.Ty.int 256)
    (c4Mod (c4Neg (numberExpr "7")) (numberExpr "3"))).isSome

-- C4 neighbor: positive constant `%` still folds and is accepted.
def c4PositiveModAccepted : Bool :=
  Solidity.Executable.Expr.numberLiteralInt?
      (c4Mod (numberExpr "7") (numberExpr "3")) == some 1 &&
    (Solidity.Executable.Expr.toCoreNumericLiteralAs? (Solidity.Ty.uint 256)
      (c4Mod (numberExpr "7") (numberExpr "3"))).isSome

end Examples

end TypeCheck
end Solidity
end SolidCore

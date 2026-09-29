import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace BaseQualifiedFunctionStateVariable

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [] [] [Ty.uint 256] [none]
    StateMutability.nonpayable Visibility.internal_

private def gFn : ContractItem := ContractItem.function
  { name := some "g"
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block []) }

private def hFn : ContractItem := ContractItem.function
  { name := some "h"
    visibility := some Visibility.public_
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some
      (Stmt.returnValues
        (some
          (Expr.call
            (Expr.member
              (Expr.typeName (Ty.user { segments := ["C"] })) "x") []))) }

def sourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "C"
            items :=
              [ ContractItem.stateVar
                  { name := "x"
                    ty := fnPtrTy
                    visibility := some Visibility.internal_ }
              , gFn
              , hFn ] } ] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

def gReturnsZero : Except TypeError Bool :=
  Examples.checkedCallWordMatches 256 sourceUnit "C" "g" State.empty [] 0

#eval accepted
#eval gReturnsZero

theorem accepted_eq_true : accepted = true := by native_decide

def gReturnsZeroOk : Bool :=
  match gReturnsZero with
  | Except.ok true => true
  | _ => false

theorem gReturnsZeroOk_eq_true : gReturnsZeroOk = true := by native_decide

private def pureFnPtrTy : Ty :=
  Ty.functionWithLocations [] [] [Ty.uint 256] [none]
    StateMutability.pure Visibility.internal_

private def returningFn (name : Name) (visibility : Visibility)
    (value : String) : ContractItem := ContractItem.function
  { name := some name
    visibility := some visibility
    mutability := StateMutability.pure
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some
      (Stmt.returnValues (some (Expr.literal (Literal.number value)))) }

private def qualifiedBaseCallWithLocalShadow : ContractItem :=
  ContractItem.function
    { name := some "shadowed"
      visibility := some Visibility.public_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := Ty.uint 256 }]
      body := some (Stmt.block
        [ Stmt.varDecl
            [{ name := some "f", ty := pureFnPtrTy }]
            (some (Expr.ident "alt"))
        , Stmt.returnValues
            (some
              (Expr.call
                (Expr.member
                  (Expr.typeName (Ty.user { segments := ["Base"] })) "f")
                [])) ]) }

def localShadowSourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "Base"
            items := [returningFn "f" Visibility.internal_ "7"] }
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "Derived"
            bases := [{ base := { segments := ["Base"] } }]
            items :=
              [ returningFn "alt" Visibility.internal_ "2"
              , qualifiedBaseCallWithLocalShadow ] } ] }

def localShadowAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit localShadowSourceUnit)

def qualifiedBaseCallIgnoresLocalShadow : Except TypeError Bool :=
  Examples.checkedCallWordMatches 256 localShadowSourceUnit "Derived"
    "shadowed" State.empty [] 7

#eval localShadowAccepted
#eval qualifiedBaseCallIgnoresLocalShadow

theorem localShadowAccepted_eq_true : localShadowAccepted = true := by
  native_decide

def qualifiedBaseCallIgnoresLocalShadowOk : Bool :=
  match qualifiedBaseCallIgnoresLocalShadow with
  | Except.ok true => true
  | _ => false

theorem qualifiedBaseCallIgnoresLocalShadowOk_eq_true :
    qualifiedBaseCallIgnoresLocalShadowOk = true := by native_decide

def inheritedThroughNamedContractRejected : Bool :=
  TypeCheck.sourceUnitAccepted?
    { items :=
        [ SourceItem.pragma "solidity" "0.8.35"
        , SourceItem.contract
            { kind := ContractKind.contract
              name := "A"
              items :=
                [ ContractItem.stateVar
                    { name := "x"
                      ty := fnPtrTy
                      visibility := some Visibility.internal_ } ] }
        , SourceItem.contract
            { kind := ContractKind.contract
              name := "B"
              bases := [{ base := { segments := ["A"] } }] }
        , SourceItem.contract
            { kind := ContractKind.contract
              name := "D"
              bases := [{ base := { segments := ["B"] } }]
              items :=
                [ ContractItem.function
                    { name := some "bad"
                      visibility := some Visibility.public_
                      returns := [{ name := none, ty := Ty.uint 256 }]
                      body := some
                        (Stmt.returnValues
                          (some
                            (Expr.call
                              (Expr.member
                                (Expr.typeName
                                  (Ty.user { segments := ["B"] })) "x")
                              []))) } ] } ] } == false

#eval inheritedThroughNamedContractRejected

theorem inheritedThroughNamedContractRejected_eq_true :
    inheritedThroughNamedContractRejected = true := by native_decide

end BaseQualifiedFunctionStateVariable
end Witness
end Solidity
end SolidCore

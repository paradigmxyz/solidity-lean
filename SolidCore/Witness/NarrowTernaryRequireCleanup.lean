import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
Narrow checked arithmetic must keep its operand-width cleanup when it appears
under a conditional used by an ABI/builtin argument, and in a call-free custom
error argument to `require`.  These were missed by the earlier env-aware
argument reroutes.
-/

namespace SolidCore.Solidity.Witness.NarrowTernaryRequireCleanup

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u8 (name : String) : Parameter :=
  { name := some name, ty := Ty.uint 8, location := none }

private def addAB : Expr :=
  Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")

private def gt (lhs : Expr) (n : String) : Expr :=
  Expr.binary BinaryOp.gt lhs (Expr.literal (Literal.number n))

private def fn (name : String) (returnTy : Ty) (body : Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := [u8 "a", u8 "b"]
      returns :=
        [{ name := none
           ty := returnTy
           location := if returnTy == Ty.bytes then some DataLocation.memory else none }]
      virtual := false
      override? := none
      modifiers := []
      body := some body }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "NarrowTernaryRequireCleanup"
    abstract := false
    bases := []
    items :=
      [ ContractItem.errorDecl
          { name := "E"
            params :=
              [{ name := some "v", ty := Ty.bool, location := none }] }
      , fn "ternaryEncode" Ty.bytes
          (Stmt.block
            [Stmt.returnValues
              (some
                (Expr.call (Expr.member (Expr.ident "abi") "encode")
                  [Arg.positional
                    (Expr.ternary
                      (gt (Expr.ident "b") "0") addAB (Expr.ident "a"))]))])
      , fn "requireCustom" (Ty.uint 8)
          (Stmt.block
            [ Stmt.expr
                (Expr.call (Expr.ident "require")
                  [ Arg.positional (Expr.literal (Literal.bool false))
                  , Arg.positional
                      (Expr.call (Expr.ident "E")
                        [Arg.positional (gt addAB "5")]) ])
            , Stmt.returnValues (some (Expr.literal (Literal.number "1"))) ])
      , fn "requireCustomSafe" (Ty.uint 8)
          (Stmt.block
            [ Stmt.expr
                (Expr.call (Expr.ident "require")
                  [ Arg.positional (Expr.literal (Literal.bool true))
                  , Arg.positional
                      (Expr.call (Expr.ident "E")
                        [Arg.positional (gt addAB "5")]) ])
            , Stmt.returnValues (some (Expr.literal (Literal.number "1"))) ])
      , fn "addmodTernary" (Ty.uint 256)
          (Stmt.block
            [Stmt.returnValues
              (some
                (Expr.call (Expr.ident "addmod")
                  [ Arg.positional
                      (Expr.ternary (gt addAB "5")
                        (Expr.literal (Literal.number "7"))
                        (Expr.literal (Literal.number "3")))
                  , Arg.positional (Expr.literal (Literal.number "1"))
                  , Arg.positional (Expr.literal (Literal.number "5")) ]))]) ] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit
      ({ items :=
          [ SourceItem.pragma "solidity" "^0.8.35"
          , SourceItem.contract contract ] } : SourceUnit))

private def abOverflow : List Value := [Value.word 200, Value.word 100]
private def abSafe : List Value := [Value.word 3, Value.word 4]

def ternaryEncode_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "ternaryEncode"
    State.empty abOverflow 17

def requireCustom_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "requireCustom"
    State.empty abOverflow 17

def addmodTernary_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "addmodTernary"
    State.empty abOverflow 17

def requireCustomSafe_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "requireCustomSafe"
    State.empty abSafe 1

def addmodTernarySafe_is_3 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "addmodTernary"
    State.empty abSafe 3

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue ternaryEncode_panics
#guard isOkTrue requireCustom_panics
#guard isOkTrue addmodTernary_panics
#guard isOkTrue requireCustomSafe_is_1
#guard isOkTrue addmodTernarySafe_is_3

end SolidCore.Solidity.Witness.NarrowTernaryRequireCleanup

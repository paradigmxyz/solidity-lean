import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
`abi.decode(abi.encode(x + y), (int8))` must evaluate the checked `int8`
addition before decoding. A variable initializer previously missed the
env-aware route through `abi.decode`, folded typed casts as bare constants,
and returned an empty ABI-validation revert instead of Panic(0x11).
-/

namespace SolidCore.Solidity.Witness.AbiDecodeNestedCheckedAdd

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def number (n : String) : Expr := Expr.literal (Literal.number n)
private def cast (ty : Ty) (expr : Expr) : Expr :=
  Expr.call (Expr.typeName ty) [Arg.positional expr]
private def narrowed410 : Expr :=
  cast (Ty.int 8) (cast (Ty.int 256) (cast (Ty.uint 256) (number "410")))
private def checkedAdd : Expr :=
  Expr.binary BinaryOp.add narrowed410 narrowed410
private def decoded (expr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "decode")
    [ Arg.positional
        (Expr.call (Expr.member (Expr.ident "abi") "encode")
          [Arg.positional expr])
    , Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.int 8))]) ]

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.int 8 }]
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "local", ty := some (Ty.int 8) }]
          (some (decoded checkedAdd))
      , Stmt.expr (Expr.assign (Expr.ident "value") AssignOp.assign
          (Expr.ident "local"))
      , Stmt.returnValues (some (Expr.ident "local")) ]) }

private def safeFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "safe"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := Ty.int 8 }]
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "local", ty := some (Ty.int 8) }]
          (some (decoded
            (Expr.binary BinaryOp.add
              (cast (Ty.int 8) (number "2"))
              (cast (Ty.int 8) (number "3")))))
      , Stmt.returnValues (some (Expr.ident "local")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar { name := "value", ty := Ty.int 8 }
      , ContractItem.function runFn
      , ContractItem.function safeFn ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def overflowPanics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 4096 contract "run" State.empty [] 0x11

def safeReturnsFive : Except TypeError Bool :=
  Examples.checkedOwnCallIntMatches 4096 contract "safe" State.empty [] 5

#guard accepted
#guard isOkTrue overflowPanics
#guard isOkTrue safeReturnsFive

end SolidCore.Solidity.Witness.AbiDecodeNestedCheckedAdd

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A redundant UDVT conversion around an ABI-decoded value is a valid Solidity
conversion. The executable lowerer must erase this conversion to the UDVT's
underlying type before it tries to lower the call.
-/

namespace SolidCore.Solidity.Witness.RedundantUdvtDecodeConversion

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def wordTy : Ty := Ty.user { segments := ["Word"] }
private def uint32 (expr : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional expr]
private def wrap (expr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.typeName wordTy) "wrap") [Arg.positional expr]
private def unwrap (expr : Expr) : Expr :=
  Expr.call (Expr.member (Expr.typeName wordTy) "unwrap") [Arg.positional expr]

private def decoded : Expr :=
  Expr.call (Expr.member (Expr.ident "abi") "decode")
    [ Arg.positional
        (Expr.call (Expr.member (Expr.ident "abi") "encode")
          [Arg.positional (wrap (uint32 (Expr.literal (Literal.number "279"))))])
    , Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName wordTy)]) ]

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    returns := [{ name := none, ty := Ty.uint 32 }]
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "value", ty := some wordTy }]
          (some (Expr.call (Expr.typeName wordTy) [Arg.positional decoded]))
      , Stmt.returnValues (some (unwrap (Expr.ident "value"))) ]) }

private def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items := [ContractItem.function runFn] }

def sourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.freeUserValueType { name := "Word", underlying := Ty.uint 32 }
      , SourceItem.contract contract ] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returns279 : Except TypeError Bool :=
  TypeCheck.Examples.checkedCallWordMatches 4096 sourceUnit "C" "run"
    State.empty [] 279

#guard accepted
#guard isOkTrue returns279

end SolidCore.Solidity.Witness.RedundantUdvtDecodeConversion

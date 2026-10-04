import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
The operand of a uint256 bitwise complement still evaluates checked
arithmetic. Lowering `~(a - b)` through the env-less path used to discard
the underflow check and return a wrapped value instead of Panic(0x11).
-/

namespace SolidCore.Solidity.Witness.BitNotWideCheckedSub

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def arg (name : String) : Expr := Expr.ident name

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    params := [{ name := some "a", ty := Ty.uint 256 },
               { name := some "b", ty := Ty.uint 256 }]
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [Stmt.returnValues (some (Expr.unary UnaryOp.bitNot
        (Expr.binary BinaryOp.sub (arg "a") (arg "b"))))]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items := [ContractItem.function runFn] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def underflowPanics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 contract "run" State.empty
    [Value.word 128, Value.word 5648574872042607240] 0x11

def safeComplement : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 contract "run" State.empty
    [Value.word 10, Value.word 3] (2 ^ 256 - 8)

#guard accepted
#guard isOkTrue underflowPanics
#guard isOkTrue safeComplement

end SolidCore.Solidity.Witness.BitNotWideCheckedSub

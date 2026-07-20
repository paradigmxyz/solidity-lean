import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
FNPTR-ARRAY-INDEX-CALL (regression): calling through an element of a fixed array
of internal function pointers — `arr[i](x)` where the callee is an `IndexAccess`
(`function(uint256) internal pure returns (uint256)[2] memory arr = [a1, a2];
return arr[1](x) * 100 + arr[0](x);`).

Two gaps were closed:
  * the solc-AST importer left `IndexAccess.argumentTypes.typeIdentifier` /
    `.typeString` UNCLASSIFIED (the `argumentTypes` callee-context fields were
    only classified for the `Identifier`/`MemberAccess`/… callee shapes), so an
    in-scope, solc-accepted program failed closed at import; and
  * the executable lowering keyed every internal call on a callee NAME, so a
    call through a non-identifier function-pointer expression (an array element)
    was declined (`checked executable checked contract`) even though the
    interpreter already supports `Stmt.internalCallPtr` with an arbitrary fn
    expression. `Expr.abiTyWithInternalFunctionsEnv?` and
    `internalExprSingleReturnUseCore?` now handle the non-identifier
    function-pointer callee via `ptrBoundaryCallExprParts?`.

Real solc 0.8.35 + EVM ground truth for `run(3)`: `arr[1](3)=a2(3)=6`,
`arr[0](3)=a1(3)=4`, so `6*100 + 4 = 604` (0x25c).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FnPtrArrayIndexCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [Ty.uint 256] [none] [Ty.uint 256] [none]
    StateMutability.pure Visibility.internal_

private def unaryFn (name : Name) (body : Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      params := [{ name := some "v", ty := Ty.uint 256, location := none }]
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some body }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ -- a1(v) = v + 1
      unaryFn "a1"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.add (Expr.ident "v")
              (Expr.literal (Literal.number "1"))))])
      -- a2(v) = v * 2
    , unaryFn "a2"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.mul (Expr.ident "v")
              (Expr.literal (Literal.number "2"))))])
      -- run(x): arr = [a1, a2]; return arr[1](x) * 100 + arr[0](x);
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.varDecl
                [{ name := some "arr", ty := Ty.array fnPtrTy (some 2),
                   location := some DataLocation.memory }]
                (some (Expr.array [Expr.ident "a1", Expr.ident "a2"]))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.binary BinaryOp.mul
                    (Expr.call
                      (Expr.index (Expr.ident "arr")
                        (Expr.literal (Literal.number "1")))
                      [Arg.positional (Expr.ident "x")])
                    (Expr.literal (Literal.number "100")))
                  (Expr.call
                    (Expr.index (Expr.ident "arr")
                      (Expr.literal (Literal.number "0")))
                    [Arg.positional (Expr.ident "x")]))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- `run(3) = a2(3)*100 + a1(3) = 6*100 + 4 = 604`.
def run_3_is_604 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 604

-- `run(5) = a2(5)*100 + a1(5) = 10*100 + 6 = 1006`.
def run_5_is_1006 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 5] 1006

-- `run(0) = a2(0)*100 + a1(0) = 0*100 + 1 = 1`.
def run_0_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 0] 1

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_604
#guard isOkTrue run_5_is_1006
#guard isOkTrue run_0_is_1

end FnPtrArrayIndexCall
end Witness
end Solidity
end SolidCore

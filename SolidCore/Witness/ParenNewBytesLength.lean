import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
PAREN-NEW-BYTES-LENGTH (coverage gap): a parenthesized `new` callee —

  contract T {
    function run() public returns (uint256) {
      bytes memory b = ((new bytes))(4);
      return b.length;
    }
  }

Real solc 0.8.35 accepts this in-scope program: `((new bytes))(4)` is just
`new bytes(4)` with grouping parentheses (Solidity has no 1-tuples), so it
allocates a 4-byte memory array and `run()` returns 4.

The bug lived in the solc-AST importer (`scripts/solc_ast_to_lean_source.py`):
the `FunctionCall` dispatch matched a `NewExpression` callee only when it was the
DIRECT `expression` node. A parenthesized `new bytes` reaches the importer as a
single-element `TupleExpression` wrapping the `NewExpression`, so it missed the
`newExpr` branch and fell through to the generic `Expr.call`, where the tuple
collapse re-exposed a bare `NewExpression` — unsupported as an ordinary
expression. The importer failed closed (`unsupported expression node
'NewExpression'`) on a program solc accepts. The fix peels single-element
grouping tuples off the callee before dispatching, so `((new bytes))(4)` lowers
to exactly the same `Expr.newExpr (Ty.bytes) [Arg.positional 4]` as bare
`new bytes(4)`.

This witness pins the target Lean semantics for the imported program: the
contract is accepted and `run()` returns 4.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace ParenNewBytesLength

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "run"
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "b", ty := Ty.bytes, location := some DataLocation.memory }]
          (some (Expr.newExpr (Ty.bytes) [Arg.positional (Expr.literal (Literal.number "4"))]))
      , Stmt.returnValues (some (Expr.member (Expr.ident "b") "length")) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "T", abstract := false, bases := []
  items := [ ContractItem.function runFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_is_4 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 4

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_is_4

end ParenNewBytesLength
end Witness
end Solidity
end SolidCore

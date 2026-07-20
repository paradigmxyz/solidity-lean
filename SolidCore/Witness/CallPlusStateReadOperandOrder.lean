import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
CALL-PLUS-STATEREAD-OPERAND-ORDER (regression): an ordinary binary operator whose
LEFT operand carries a side-effecting internal call and whose RIGHT operand is a
pure storage read that the call MUTATES —

    function g() internal returns (uint256) { t += 105; return t; }
    function run() external returns (uint256) { return g() * 100000 + t; }

Neither operand of the outer `+` is a *direct* call (the left is `g() * 100000`,
a nested binary; the right is the bare state read `t`), so lowering routes the
whole binary through `FunctionDecl.internalBinarySingleReturnUseCore?`'s
`none, none` branch. Hoisting the RIGHT operand finds no call there, so control
reaches the `| none =>` (pure-RHS) sub-case. That sub-case used to lower the pure
RHS in place and hoist the LEFT call around it, evaluating `g()` (which does
`t += 105`) BEFORE the residual binary reads `t`. solc 0.8.35 legacy codegen
evaluates the RIGHT operand FIRST (`libsolidity/codegen/ExpressionCompiler.cpp:
614-615`; see [[EVAL_ORDER_DESIGN]]), reading `t` while it is still 0. The wrong
order changed the RETURN value (storage `t` ends at 105 either way).

Real solc 0.8.35 + EVM ground truth (`t = 0` at entry, right-operand-first):

  run(): read `t` = 0;  g(): t = 105, ret 105;  105 * 100000 = 10500000;
         10500000 + 0 = 10500000  →  return 10500000, final t = 105.

The buggy left-first order gave 10500000 + 105 = 10500105.

The fix parks the RIGHT operand's value in a `_sol_bin_<tag>_rhs` temp, evaluates
the LEFT call second, and combines from the temp.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace CallPlusStateReadOperandOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def numL (s : String) : Expr := Expr.literal (Literal.number s)

private def callG : Expr := Expr.call (Expr.ident "g") []

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "B"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "t"
          ty := Ty.uint 256
          visibility := some Visibility.public_
          mutability := VarMutability.mutable
          override? := none
          init := none }
      -- g(): t += 105; return t;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "g"
          visibility := some Visibility.internal_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr
                (Expr.assign (Expr.ident "t") AssignOp.addAssign (numL "105"))
            , Stmt.returnValues (some (Expr.ident "t")) ]) }
      -- run(): return g() * 100000 + t;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.binary BinaryOp.mul callG (numL "100000"))
                  (Expr.ident "t"))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_is_10500000 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [] 10500000

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def finalTMatches (expected : Word) : Bool :=
  match Examples.checkedOwnCallState 256 runContract "run" State.empty [] with
  | Except.ok state => SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expected
  | _ => false

#guard accepted
#guard isOkTrue run_is_10500000
#guard finalTMatches 105

end CallPlusStateReadOperandOrder
end Witness
end Solidity
end SolidCore

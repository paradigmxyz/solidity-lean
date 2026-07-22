import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
BINARY-TERNARY-OPERAND-ORDER (regression): the two operands of an ordinary
binary operator are ternaries whose branches are side-effecting internal calls —
`(x < 5 ? s(1) : s(2)) + (x > 1 ? s(3) : s(4))`. Neither operand is a *direct*
call, so the executable lowering routes the whole binary through
`FunctionDecl.internalBinarySingleReturnUseCore?`'s `none, none` branch. Its
`_, none` sub-case (both operands non-core-lowerable, each carrying a nested
call) used to evaluate the LEFT operand FIRST, contradicting solc 0.8.35 legacy
codegen, which evaluates the RIGHT operand FIRST
(`libsolidity/codegen/ExpressionCompiler.cpp:614-615`; see [[EVAL_ORDER_DESIGN]]
and the `binaryOrder` control in `EvalOrderIntrinsic`). The wrong order changed
both the RETURN value and final STORAGE. The fix parks the RIGHT operand's value
in a temp, evaluates the LEFT operand second, and leaves the residual binary for
the right-then-left runtime arm.

Real solc 0.8.35 + EVM ground truth (`s(k){ t = t*10 + k; return k; }`,
`t = 0`, right-operand-first):

  run(3): x<5 ✓, x>1 ✓ →  RHS s(3): t=3, ret 3;  LHS s(1): t=31, ret 1;
          q = 1 + 3 = 4  →  return 4*1000 + 31 = 4031 (0xfbf), final t = 31.
  run(0): x<5 ✓, x>1 ✗ →  RHS s(4): t=4, ret 4;  LHS s(1): t=41, ret 1;
          q = 1 + 4 = 5  →  return 5*1000 + 41 = 5041, final t = 41.
  run(7): x<5 ✗, x>1 ✓ →  RHS s(3): t=3, ret 3;  LHS s(2): t=32, ret 2;
          q = 2 + 3 = 5  →  return 5*1000 + 32 = 5032, final t = 32.

The buggy left-first order gave run(3) → 4013, final t = 13.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace BinaryTernaryOperandOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def numL (s : String) : Expr := Expr.literal (Literal.number s)

private def callS (arg : String) : Expr :=
  Expr.call (Expr.ident "s") [Arg.positional (numL arg)]

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
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
      -- s(k): t = t * 10 + k; return k;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "s"
          visibility := some Visibility.internal_
          mutability := StateMutability.nonpayable
          params := [{ name := some "k", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr
                (Expr.assign (Expr.ident "t") AssignOp.assign
                  (Expr.binary BinaryOp.add
                    (Expr.binary BinaryOp.mul (Expr.ident "t") (numL "10"))
                    (Expr.ident "k")))
            , Stmt.returnValues (some (Expr.ident "k")) ]) }
      -- run(x): q = (x<5 ? s(1):s(2)) + (x>1 ? s(3):s(4)); return q*1000 + t;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.varDecl
                [{ name := some "q", ty := Ty.uint 256, location := none }]
                (some (Expr.binary BinaryOp.add
                  (Expr.ternary
                    (Expr.binary BinaryOp.lt (Expr.ident "x") (numL "5"))
                    (callS "1") (callS "2"))
                  (Expr.ternary
                    (Expr.binary BinaryOp.gt (Expr.ident "x") (numL "1"))
                    (callS "3") (callS "4"))))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.binary BinaryOp.mul (Expr.ident "q") (numL "1000"))
                  (Expr.ident "t"))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_3_is_4031 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 4031

def run_0_is_5041 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 0] 5041

def run_7_is_5032 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 7] 5032

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def finalTMatches (arg expected : Word) : Bool :=
  match Examples.checkedOwnCallState 256 runContract "run" State.empty
      [Value.word arg] with
  | Except.ok state => SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expected
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_4031
#guard isOkTrue run_0_is_5041
#guard isOkTrue run_7_is_5032
#guard finalTMatches 3 31
#guard finalTMatches 0 41
#guard finalTMatches 7 32

end BinaryTernaryOperandOrder
end Witness
end Solidity
end SolidCore

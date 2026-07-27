import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
DECL-BINARY-CALL-NESTED-CALL (soundness gap): a local variable DECLARATION whose
initializer is an ordinary binary whose LEFT operand is a DIRECT internal
single-return call and whose RIGHT operand carries its OWN nested call —

    function bump() internal returns (uint256) { n += 1; return n; }
    function f() external returns (uint256) {
      uint256 a = bump() + bump() * 10;   // right operand `bump() * 10` is nested
      return a;
    }

Lowering routes the initializer's binary through
`FunctionDecl.internalBinarySingleReturnUseCore?`'s `some (name,args,convert),
none` branch (LHS is a direct call; RHS `bump() * 10` is NOT a direct call). The
RHS carries a call so `Expr.toCore?` returns `none`, reaching the `| none =>`
sub-case, which only handled the short-circuiting `&&`/`||`; for an ordinary `+`
it fell to `| _ => none` and over-rejected the whole declaration → Panic(0). The
SAME expression in a bare `return` lowers fine (it agrees with EVM), so the gap
was declaration-specific.

Real solc 0.8.35 + EVM ground truth (`n = 0` at entry, RIGHT operand first —
`libsolidity/codegen/ExpressionCompiler.cpp:614-615`; see [[EVAL_ORDER_DESIGN]]):

  f(): eval RHS `bump() * 10` first → bump(): n = 1, ret 1; 1 * 10 = 10;
       eval LHS `bump()` → n = 2, ret 2;  2 + 10 = 12  →  return 12, final n = 2.

The fix lowers the RIGHT operand's expression into a temp first, then runs the
LEFT call and forms the residual binary reading the temp (right-operand-first).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace DeclBinaryCallNestedCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def numL (s : String) : Expr := Expr.literal (Literal.number s)

private def callBump : Expr := Expr.call (Expr.ident "bump") []

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "T"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "n"
          ty := Ty.uint 256
          visibility := none
          mutability := VarMutability.mutable
          override? := none
          init := none }
      -- bump(): n += 1; return n;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "bump"
          visibility := some Visibility.internal_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr
                (Expr.assign (Expr.ident "n") AssignOp.addAssign (numL "1"))
            , Stmt.returnValues (some (Expr.ident "n")) ]) }
      -- f(): uint256 a = bump() + bump() * 10; return a;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "f"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          params := []
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.varDecl
                [ { name := some "a", ty := some (Ty.uint 256), location := none } ]
                (some (Expr.binary BinaryOp.add
                  callBump
                  (Expr.binary BinaryOp.mul callBump (numL "10"))))
            , Stmt.returnValues (some (Expr.ident "a")) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def f_is_12 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "f" State.empty [] 12

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def finalNMatches (expected : Word) : Bool :=
  match Examples.checkedOwnCallState 256 runContract "f" State.empty [] with
  | Except.ok state => SolidCore.Solidity.Source.wordEq (state.loadSlot 0) expected
  | _ => false

#guard accepted
#guard isOkTrue f_is_12
#guard finalNMatches 2

end DeclBinaryCallNestedCall
end Witness
end Solidity
end SolidCore

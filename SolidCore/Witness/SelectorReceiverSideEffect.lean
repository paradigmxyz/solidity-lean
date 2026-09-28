import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
A discarded function selector still evaluates its receiver expression.

The selector pass used to replace `h().f.selector` with a literal before
lowering, erasing the call to `h` and any state change it performs. In an
expression statement the selector value itself is discarded, so the resolved
statement must retain the receiver call.

Pinned solc 0.8.35 and Forge ground truth live in
`tests/forge-harness/selector-receiver-side-effect`.
-/

open SolidCore.Solidity

namespace SolidCore
namespace Solidity
namespace Witness
namespace SelectorReceiverSideEffect

def receiverCall : Expr := Expr.call (Expr.ident "h") []

def discardedSelector : Stmt :=
  Stmt.expr (Expr.member (Expr.member receiverCall "f") "selector")

def selectorEnv : Executable.SelectorEnv :=
  [("f", SolidCore.Solidity.Source.ABI.selectorFromSignature "f()")]

def resolved : Stmt :=
  Executable.Stmt.resolveSelectors selectorEnv discardedSelector

def preservesReceiverCall : Bool :=
  match resolved with
  | Stmt.expr (Expr.call (Expr.ident "h") []) => true
  | _ => false

def returnedSelector : Stmt :=
  Stmt.returnValues
    (some
      (Expr.call (Expr.typeName (Ty.uint 32))
        [Arg.positional
          (Expr.member (Expr.member receiverCall "f") "selector")]))

def resolvedReturn : Stmt :=
  Executable.Stmt.resolveSelectors selectorEnv returnedSelector

def preservesReturnReceiverCall : Bool :=
  match resolvedReturn with
  | Stmt.block
      [Stmt.expr (Expr.call (Expr.ident "h") []),
       Stmt.returnValues (some _)] => true
  | _ => false

#guard preservesReceiverCall
#guard preservesReturnReceiverCall

end SelectorReceiverSideEffect
end Witness
end Solidity
end SolidCore

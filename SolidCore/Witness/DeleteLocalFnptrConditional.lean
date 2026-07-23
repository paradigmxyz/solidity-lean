/-
DELETE-LOCAL-FNPTR-CONDITIONAL (soundness regression): a local internal
function pointer that is deleted inside a CONDITIONAL branch and then called
must dispatch on the RUNTIME pointer value — panicking 0x51 when the branch
that deleted it was taken — not be statically resolved to its original target.

```solidity
contract C {
  function a(uint256 x) internal pure returns (uint256) { return x + 1; }
  function run(uint256 x) external pure returns (uint256) {
    function(uint256) internal pure returns (uint256) f = a;
    if (x > 2) { delete f; }
    return f(x);
  }
}
```

Real solc 0.8.35 + EVM ground truth:
  * `run(3)`: `x > 2` holds, `delete f` runs, `f(3)` calls a zero-initialized
    internal function pointer -> `Panic(0x51)` (revert).
  * `run(2)`: `x > 2` is false, `f` still points at `a`, `f(2) = a(2) = 3`.

Gap closed: the internal-function-pointer static alias-inlining pre-pass
(`Stmt.inlineInternalFunctionAliasSeqFuel`) established `f -> a` at the
`f = a` var declaration and elided the declaration, then processed the
`if`-branch with the alias environment's post-state DISCARDED (`.fst`). The
conditional `delete f` therefore never invalidated the alias, so the trailing
`f(x)` was statically inlined to a direct `a(x)` call — success `w:4` instead
of the required `Panic(0x51)`. The fix declines the static alias whenever the
alias name is reassigned or deleted anywhere inside a nested control-flow
construct, keeping `f` a genuine runtime function-pointer local so the call
lowers to `Stmt.internalCallPtr` and dispatches on the real (possibly zeroed)
dispatch ID.
-/
import SolidCore.Solidity.Interface

namespace SolidCore
namespace Solidity
namespace Witness
namespace DeleteLocalFnptrConditional

open SolidCore.Solidity.Source
open SolidCore.Solidity.Executable

def runContract : ContractDecl :=
  { name := "C"
    items :=
      [ ContractItem.function
          { name := some "a"
            visibility := some Visibility.internal_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.pure
            body :=
              some
                (Stmt.returnValues
                  (some
                    (Expr.binary BinaryOp.add
                      (Expr.ident "x")
                      (Expr.literal (Literal.number "1"))))) }
      , ContractItem.function
          { name := some "run"
            visibility := some Visibility.external_
            params := [{ name := some "x", ty := Ty.uint 256 }]
            returns := [{ name := some "out", ty := Ty.uint 256 }]
            mutability := StateMutability.pure
            body :=
              some
                (Stmt.block
                  [ Stmt.varDecl
                      [ { name := some "f"
                          ty :=
                            some
                              (Ty.function [Ty.uint 256] [Ty.uint 256]
                                StateMutability.pure
                                Visibility.internal_) } ]
                      (some (Expr.ident "a"))
                  , Stmt.ifElse
                      (Expr.binary BinaryOp.gt
                        (Expr.ident "x")
                        (Expr.literal (Literal.number "2")))
                      (Stmt.block
                        [ Stmt.expr
                            (Expr.unary UnaryOp.delete (Expr.ident "f")) ])
                      none
                  , Stmt.returnValues
                      (some
                        (Expr.call (Expr.ident "f")
                          [Arg.positional (Expr.ident "x")])) ]) } ] }

def callRun (x : Word) : Option CallResult :=
  ContractDecl.call? 64 runContract
    (SolidCore.Solidity.Source.CallTarget.name "run")
    SolidCore.Solidity.Source.State.empty
    [SolidCore.Solidity.Source.Value.word x]

-- `run(3)`: the branch deletes `f`, so the call must Panic(0x51).
def run_3_panics : Option Bool := do
  let result ← callRun 3
  match result with
  | SolidCore.Solidity.Source.CallResult.reverted _
      (SolidCore.Solidity.Source.RevertData.panic code) =>
      some (SolidCore.Solidity.Source.wordEq code 0x51)
  | _ => some false

-- `run(2)`: the branch is skipped, so `f` still points at `a`; `a(2) = 3`.
def run_2_is_3 : Option Bool := do
  let result ← callRun 2
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _
      [SolidCore.Solidity.Source.Value.word w] =>
      some (SolidCore.Solidity.Source.wordEq w 3)
  | _ => some false

#guard run_3_panics == some true
#guard run_2_is_3 == some true

end DeleteLocalFnptrConditional
end Witness
end Solidity
end SolidCore

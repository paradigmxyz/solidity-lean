import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
ABI-STRAY-VALUE (C, abi-functions-member-access) — a bare reference to a builtin
`abi.*` function used as a discarded expression statement.

```solidity
contract C {
    function f() public pure {
        abi.decode;
    }
}
```

`abi.decode;` names a builtin `abi.*` function as a VALUE and immediately discards
it (an expression statement). solc ACCEPTS this (with a "statement has no effect"
warning): the member access yields the function's type, but nothing converts it,
so f runs to the end returning empty (`0x`). Naming an `abi.*` function as a bare,
discarded reference is legal; only a genuine CONVERSION of it to a function pointer
(assignment/argument/return) is forbidden.

solidity-lean over-rejected: `checkExpr`'s generic `Expr.member base member` arm
recurses into the base `abi`, which resolves as an ordinary identifier and fails
closed with `unknownIdentifier "abi"` — a FAIL-CLOSED typecheck reject on a
solc-accepted program.

Fix: accept `abi.<fn>;` (a builtin `abi.*` member) as a discarded no-op expression
STATEMENT at both the typecheck gate (statement position only, and only when `abi`
is the builtin — not a shadowing local) and the executable lowering (the value has
no side effects and is discarded, so it lowers to nothing). An `abi.<fn>` reference
in a CONVERSION position stays rejected — `checkExpr` is unchanged.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiStrayValue

open SolidCore.Solidity.Source

-- contract C { function f() public pure { abi.decode; } }
private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.public_, mutability := StateMutability.pure,
    params := [], returns := [],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [Stmt.expr (Expr.member (Expr.ident "abi") "decode")]) }

def testDecl : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [], items := [fFn] }

def importedContract : ContractDecl := testDecl

def importedContracts : List ContractDecl := [testDecl]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract testDecl] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiStrayValue
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiStrayValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.AbiStrayValue.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

abbrev srcUnit := SolidCore.Solidity.SolcAstImport.AbiStrayValue.importedSourceUnit

-- `f()`: the stray `abi.decode;` is a discarded no-op; f runs to the end returning
-- empty (matching solc+EVM `0x`), NOT a FAIL-CLOSED reject.
def f_returns_empty : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 256 srcUnit "C"
      (SolidCore.Solidity.Source.CallTarget.name "f")
      State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ [] => Except.ok true
  | _ => Except.ok false

#guard accepted
#guard isOkTrue f_returns_empty

end AbiStrayValue
end Witness
end Solidity
end SolidCore

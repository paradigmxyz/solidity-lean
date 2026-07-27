import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
UDVT-STRAY-VALUE (C, wrap-unwrap) — a bare reference to a user-value-type builtin
(`MyAddress.wrap`) used as a discarded expression statement.

```solidity
type MyAddress is address;
contract C {
    function f() pure public {
        MyAddress.wrap;
    }
}
```

`MyAddress.wrap;` names the user-value-type builtin `wrap` as a VALUE and
immediately discards it (an expression statement). solc ACCEPTS this (with a
"statement has no effect" warning): the member access yields the builtin's
function type, but nothing converts it, so f runs to the end returning empty
(`0x`). Naming `T.wrap` / `T.unwrap` as a bare, discarded reference is legal; only
a genuine CONVERSION of it to a function pointer (assignment/argument/return) is
forbidden.

solidity-lean over-rejected: the stray statement matches the same
`Stmt.expr (Expr.member (Expr.typeName (Ty.user path)) member)` shape as the
`Lib.m;` LIBRARY-STRAY-VALUE arc, but the type name is not a library, so the arm
fell through to `checkExpr`, whose meta-member table has no `wrap`/`unwrap` rows
for a UDVT — a FAIL-CLOSED `unsupported "member wrap"` reject on a solc-accepted
program.

Fix (mirrors the `Lib.m;` / `abi.decode;` arcs): accept `T.wrap;` / `T.unwrap;` as
a discarded no-op expression STATEMENT at both the typecheck gate (statement
position only, and only when the type name is genuinely a user value type) and the
executable lowering (a bare member-value statement has no side effects and is
discarded, so it lowers to nothing). The same member in a CONVERSION position stays
rejected — `checkExpr` is unchanged.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace UdvtWrapStrayValue

open SolidCore.Solidity.Source

private def myAddrTy : Ty := Ty.user { segments := ["MyAddress"] }

-- contract C { function f() pure public { MyAddress.wrap; } }
private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.public_, mutability := StateMutability.pure,
    params := [], returns := [],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [Stmt.expr (Expr.member (Expr.typeName myAddrTy) "wrap")]) }

def testDecl : ContractDecl :=
  { kind := ContractKind.contract, name := "C",
    abstract := false, bases := [], items := [fFn] }

def importedContract : ContractDecl := testDecl

def importedContracts : List ContractDecl := [testDecl]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.freeUserValueType
                { name := "MyAddress", underlying := Ty.address false },
              SourceItem.contract testDecl] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end UdvtWrapStrayValue
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace UdvtWrapStrayValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.UdvtWrapStrayValue.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

abbrev srcUnit := SolidCore.Solidity.SolcAstImport.UdvtWrapStrayValue.importedSourceUnit

-- `f()`: the stray `MyAddress.wrap;` is a discarded no-op; f runs to the end
-- returning empty (matching solc+EVM `0x`), NOT a FAIL-CLOSED reject.
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

end UdvtWrapStrayValue
end Witness
end Solidity
end SolidCore

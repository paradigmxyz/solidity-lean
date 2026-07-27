import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
LIBRARY-STRAY-VALUE (C, library-stray-values) — a bare reference to a PUBLIC
library function used as a discarded expression statement.

```solidity
library Lib { function m(uint x, uint y) public returns (uint) { return x * y; } }
contract Test {
    function f(uint x) public returns (uint) { Lib.m; }
}
```

`Lib.m;` names a public library function as a VALUE and immediately discards it
(an expression statement). solc ACCEPTS this (with a "statement has no effect"
warning): the member access yields the function's type, but nothing converts it,
so f falls off the end returning the default `0`. The restriction "public/external
library functions cannot be converted to a function type" only fires on a genuine
CONVERSION (assignment to a function pointer, an argument, a return) — never on a
bare, discarded reference.

solidity-lean over-rejected: `checkExpr`'s `Expr.member (Expr.typeName ty) member`
arm resolves an internal-function VALUE only for `internal` library functions
(`resolveInternalFunctionValueMember?` gates on `internal_`), so a public library
member fell through `builtinMetaMemberTy?` to `unsupported "member m"` — a
FAIL-CLOSED typecheck reject on a solc-accepted program.

Fix: accept `Lib.m;` (a public/external library function member) as a discarded
no-op expression STATEMENT at both the typecheck gate and the executable lowering
(the value has no side effects and is discarded, so it lowers to nothing). A
public library member in a CONVERSION position stays rejected — `checkExpr` is
unchanged.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LibraryStrayValue

open SolidCore.Solidity.Source

private def uintParam (nm : String) : Parameter :=
  { name := some nm, ty := Ty.uint 256, location := none }

-- library Lib { function m(uint x, uint y) public returns (uint) { return x*y; } }
private def mFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "m",
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable,
    params := [uintParam "x", uintParam "y"],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some
      (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.ident "y")))]) }

def libDecl : ContractDecl :=
  { kind := ContractKind.library, name := "Lib",
    abstract := false, bases := [], items := [mFn] }

-- contract Test { function f(uint x) public returns (uint) { Lib.m; } }
private def fFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function, name := some "f",
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable,
    params := [uintParam "x"],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false, override? := none, modifiers := [],
    body := some (Stmt.block
      [Stmt.expr (Expr.member (Expr.typeName (Ty.user { segments := ["Lib"] })) "m")]) }

def testDecl : ContractDecl :=
  { kind := ContractKind.contract, name := "Test",
    abstract := false, bases := [], items := [fFn] }

def importedContract : ContractDecl := testDecl

def importedContracts : List ContractDecl := [libDecl, testDecl]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract libDecl,
              SourceItem.contract testDecl] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LibraryStrayValue
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LibraryStrayValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.LibraryStrayValue.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

abbrev srcUnit := SolidCore.Solidity.SolcAstImport.LibraryStrayValue.importedSourceUnit

-- `f(33)`: the stray `Lib.m;` is a discarded no-op; f falls off the end returning
-- the default `0` (matching solc+EVM `0x00..00`), NOT a FAIL-CLOSED reject.
def f_returns_zero : Except TypeError Bool :=
  Examples.checkedCallWordMatches 256 srcUnit "Test" "f" State.empty [Value.word 33] 0

#guard accepted
#guard isOkTrue f_returns_zero

end LibraryStrayValue
end Witness
end Solidity
end SolidCore

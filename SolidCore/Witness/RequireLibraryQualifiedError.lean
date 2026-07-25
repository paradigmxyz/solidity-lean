import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
REQUIRE-LIBRARY-QUALIFIED-ERROR — the require-with-custom-error second argument
may name a LIBRARY-declared error (`require(cond, L.Bad(a))`).

```solidity
library EL { error Bad(uint256 x); }
interface EI { }
contract T {
    function run() public returns (uint256) {
        uint256 a = 5;
        require(a > 0, EL.Bad(a));
        return a;
    }
}
```

solc 0.8.35 accepts this in-scope program and, since `a > 0` holds, the EVM runs
`run()` to SUCCESS returning `5` (the custom error is never triggered).

solidity-lean formerly FAILED CLOSED at typecheck with
`TypeError.unknownFunction "Bad"`: the require-with-member-error checker arm
resolved the error callee's UNQUALIFIED name against the contract's flattened
`env.errors` (via `checkCustomErrorArgs`), which does not carry a library error,
and its fallback re-checked the whole `require(...)` as an ordinary expression —
where `EL.Bad(a)` resolves as a member function call and is rejected as
`unknownFunction "Bad"`.

The fix mirrors `checkRevertCall`'s library arm (already handling `revert
L.Bad(a)`): when the member callee's base is a `typeName (Ty.user path)`, resolve
the error against that named type's error table (`contractErrorSig?`) BEFORE the
flattened-scope fallback. The executable lowering already lowers the member
require-custom to `requireCustom` by the bare name, and the library qualifier is
not part of the error selector, so the selector is soundly encoded.

Real-EVM ground truth (adjudicated divergence): `run()` => `ok|w:5`.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RequireLibraryQualifiedError

open SolidCore.Solidity.Source

-- `library EL { error Bad(uint256 x); }`
private def libraryEL : ContractDecl :=
  { kind := ContractKind.library, name := "EL",
    abstract := false, bases := [],
    items := [ ContractItem.errorDecl
      { name := "Bad",
        params := [{ name := some "x", ty := Ty.uint 256, location := none }] } ] }

-- `interface EI { }`
private def interfaceEI : ContractDecl :=
  { kind := ContractKind.interface, name := "EI",
    abstract := false, bases := [], items := [] }

-- `function run() public returns (uint256) {
--    uint256 a = 5; require(a > 0, EL.Bad(a)); return a; }`
private def runFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "run",
      visibility := some Visibility.public_,
      mutability := StateMutability.nonpayable,
      params := [], returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false, override? := none, modifiers := [],
      body := some (Stmt.block
        [ Stmt.varDecl [{ name := some "a", ty := some (Ty.uint 256), location := none }]
            (some (Expr.literal (Literal.number "5")))
        , Stmt.expr
            (Expr.call (Expr.ident "require")
              [ Arg.positional
                  (Expr.binary BinaryOp.gt (Expr.ident "a")
                    (Expr.literal (Literal.number "0")))
              , Arg.positional
                  (Expr.call
                    (Expr.member (Expr.typeName (Ty.user { segments := ["EL"] })) "Bad")
                    [Arg.positional (Expr.ident "a")]) ])
        , Stmt.returnValues (some (Expr.ident "a")) ]) }

def importedContractDecl : ContractDecl :=
  { kind := ContractKind.contract, name := "T",
    abstract := false, bases := [], items := [runFn] }

def importedContract : ContractDecl := importedContractDecl

def importedSourceUnit : SourceUnit :=
  { items := [ SourceItem.pragma "solidity" "^0.8.35",
               SourceItem.contract libraryEL,
               SourceItem.contract interfaceEI,
               SourceItem.contract importedContractDecl ] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RequireLibraryQualifiedError
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace RequireLibraryQualifiedError

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Unit_ := SolidCore.Solidity.SolcAstImport.RequireLibraryQualifiedError.importedSourceUnit

-- The whole unit (library EL + interface EI + contract T) is ACCEPTED (pre-fix
-- this failed closed at typecheck with `unknownFunction "Bad"`).
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.RequireLibraryQualifiedError.importedContractAccepted

-- The divergence witness: `run()` runs to SUCCESS returning the uint256 `5`
-- (the passing require never triggers the library error).
def run_returns_5 : Option Bool :=
  match CheckedInput.callContract 64 Unit_ "T"
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty [] with
  | Except.ok (SolidCore.Solidity.Source.CallResult.returned _ [Value.word v]) =>
      some (v == 5)
  | _ => some false

#guard accepted
#guard run_returns_5 == some true

end RequireLibraryQualifiedError
end Witness
end Solidity
end SolidCore

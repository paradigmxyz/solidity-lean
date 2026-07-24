import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NARROW-ADD-NESTED-MAPPING-KEY (S, narrow-add-nested-mapping-read-key) — a NARROW
checked-arithmetic OUTER mapping key of a NESTED mapping read must evaluate at
its own operand width, so the overflow Panic 0x11 fires BEFORE the lookup.

```solidity
contract C {
    mapping(uint8 => mapping(uint8 => uint256)) m;
    function f(uint8 a, uint8 b) external view returns (uint256) {
        return m[a + b][0];
    }
}
```

`f(200,100)`: solc computes `a + b` at uint8 (the common type of the two uint8
operands), so the checked add overflows (300 > 255) and reverts Panic 0x11 while
computing the OUTER mapping key, before the nested lookup. solidity-lean lowered
the nested read `m[a + b][0]` env-aware at the OUTER index, but built the base
`m[a + b]` via the env-LESS `Expr.indexReadCoreBuilder?` (`Expr.toCore?`), so the
inner narrow key `a + b` ran at 256 bits (= 300, no overflow) and the call read
`m[300][0] = 0` and returned 0 — a revert-vs-success soundness gap.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NarrowAddNestedMappingKey

open SolidCore.Solidity.Source

private def nestedM : Ty :=
  Ty.mapping (Ty.uint 8) (Ty.mapping (Ty.uint 8) (Ty.uint 256))

-- m[a + b][0]
private def readExpr : Expr :=
  Expr.index
    (Expr.index (Expr.ident "m")
      (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))
    (Expr.literal (Literal.number "0"))

private def fFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some "f",
      visibility := some Visibility.external_,
      mutability := StateMutability.view,
      params := [{ name := some "a", ty := Ty.uint 8, location := none },
                 { name := some "b", ty := Ty.uint 8, location := none }],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false,
      override? := none,
      modifiers := [],
      body := some (Stmt.block [Stmt.returnValues (some readExpr)]) }

-- CONTROL: single-level mapping with the same narrow key already Panics.
private def readExpr1 : Expr :=
  Expr.index (Expr.ident "n")
    (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))

private def gFn : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function,
      name := some "g",
      visibility := some Visibility.external_,
      mutability := StateMutability.view,
      params := [{ name := some "a", ty := Ty.uint 8, location := none },
                 { name := some "b", ty := Ty.uint 8, location := none }],
      returns := [{ name := none, ty := Ty.uint 256, location := none }],
      virtual := false,
      override? := none,
      modifiers := [],
      body := some (Stmt.block [Stmt.returnValues (some readExpr1)]) }

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [ ContractItem.stateVar { name := "m", ty := nestedM }
           , ContractItem.stateVar { name := "n", ty := Ty.mapping (Ty.uint 8) (Ty.uint 256) }
           , fFn
           , gFn ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]
def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NarrowAddNestedMappingKey
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowAddNestedMappingKey

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NarrowAddNestedMappingKey.importedContract

-- The source unit type-checks (accepted).
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NarrowAddNestedMappingKey.importedContractAccepted

-- f(200,100): outer key a + b = 300 overflows uint8 -> Panic 0x11 (was
-- success reading m[300][0] = 0).
def f_200_100_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 100] 17

-- f(200,56): a + b = 256 overflows uint8 -> Panic 0x11 (boundary).
def f_200_56_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 56] 17

-- f(200,55): a + b = 255 fits uint8 -> reads m[255][0] = 0 (safe boundary).
def f_200_55_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 55] 0

-- f(100,100): a + b = 200 fits uint8 -> reads m[200][0] = 0 (safe).
def f_100_100_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 100, Value.word 100] 0

-- SINGLE-LEVEL CONTROL: g(200,100) = n[a + b] already Panicked.
def g_200_100_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "g" State.empty
    [Value.word 200, Value.word 100] 17

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue f_200_100_panics
#guard isOkTrue f_200_56_panics
#guard isOkTrue f_200_55_is_0
#guard isOkTrue f_100_100_is_0
#guard isOkTrue g_200_100_panics

end NarrowAddNestedMappingKey
end Witness
end Solidity
end SolidCore

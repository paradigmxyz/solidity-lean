import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
NARROW-ADD-WIDE-CAST-RETURN (S, narrow-add-widening-cast-return) — a WORD-width
(`uint256`) explicit cast of a NARROW checked-arithmetic sub-expression must
still evaluate that sub-expression at ITS OWN operand width, so the narrow
overflow Panic 0x11 fires BEFORE the widening conversion.

`f(uint8 a, uint8 b) returns (uint256) { return uint256(a + b); }` with
`f(200,100)`: solc computes `a + b` at uint8 (the common type of the two uint8
operands), so the checked add overflows (300 > 255) and reverts Panic 0x11
BEFORE the `uint256(...)` widening (which never runs). solidity-lean formerly
routed the WIDE (`uint256`) cast through the env-less Direct path (the
`Ty.wordIntCastTarget?` arm of `Expr.toCoreAsWithEnvFuel?` only handled the
signed-literal-operand-mix reroute), so `a + b` ran at 256 bits (= 300, no
overflow) and the call returned 300 successfully — a revert-vs-success
soundness gap.

The narrow-cast H2 arm already checked `uint8(a + b)` at the operand width; the
fix broadens the WIDE-cast arm's reroute gate so `uint256(a + b)` over NARROW
arithmetic likewise lowers the binary through `binaryToCoreWithEnvTypedFuel?`
(operand-width checked cleanup) before the 256-bit widening. Explicitly-widened
operands (`uint256(a) + uint256(b)`) keep their 256-bit (non-panicking)
semantics — the peeled binary's operand common type is word, so the reroute
does not fire.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NarrowAddWideCastReturnWitness

def importedSourceName : String :=
  "probes/narrow-add-wide-cast-return/NarrowAddWideCastReturn.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "a")]) (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "b")])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NarrowAddWideCastReturnWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowAddWideCastReturn

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NarrowAddWideCastReturnWitness.importedContract

-- The source unit type-checks (accepted).
def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NarrowAddWideCastReturnWitness.importedContractAccepted

-- f(200,100): a + b = 300 overflows uint8 -> Panic 0x11 (was 300 success).
def f_200_100_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 100] 17

-- f(200,56): a + b = 256 overflows uint8 -> Panic 0x11 (boundary).
def f_200_56_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 56] 17

-- f(200,55): a + b = 255 fits uint8 -> returns 255, no panic.
def f_200_55_is_255 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 200, Value.word 55] 255

-- f(100,100): a + b = 200 fits uint8 -> returns 200.
def f_100_100_is_200 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "f" State.empty
    [Value.word 100, Value.word 100] 200

-- CONTROL (minimality): g(200,100) with explicitly-widened operands
-- `uint256(a) + uint256(b)` runs at 256 bits -> 300, no panic.
def g_200_100_is_300 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 Fam "g" State.empty
    [Value.word 200, Value.word 100] 300

-- NARROW CONTROL: h(200,100) = uint8(a+b) narrow cast return already Panics.
def h_200_100_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 256 Fam "h" State.empty
    [Value.word 200, Value.word 100] 17

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard isOkTrue h_200_100_panics
#guard accepted
#guard isOkTrue f_200_100_panics
#guard isOkTrue f_200_56_panics
#guard isOkTrue f_200_55_is_255
#guard isOkTrue f_100_100_is_200
#guard isOkTrue g_200_100_is_300

end NarrowAddWideCastReturn
end Witness
end Solidity
end SolidCore

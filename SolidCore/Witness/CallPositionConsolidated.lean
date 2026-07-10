import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
CALL-POSITION CONSOLIDATED (#147-#151) — value-returning calls in argument-like
positions now lower and evaluate correctly.

A call `f()` whose result is consumed by a surrounding construct is a STATEMENT
in the Executable core, so it must be hoisted into a prefix eval-temp before the
construct is lowered. Several argument-like positions never routed through that
hoisting, so a call there made the whole contract unlowerable (over-reject),
though solc accepts every one:

  * #147 CALL-IN-MODIFIER-ARG   — `f() public m(g())`            (already lowered;
                                   audit was a false positive, pinned here)
  * #148 CALL-IN-ARRAY-LITERAL  — `[g(), h()]`
  * #149 CALL-IN-STRUCT-CTOR    — `S(g(), h())`
  * #150 CALL-IN-NEW-ARG        — `new T(g())`, `new uint256[](g())`,
                                   `new bytes(g() + 2)`
  * #151 CALL-IN-NESTED-ARG     — `h(g() + 1)`, `h(arr[g()])`

The fix adds a generic argument-position peel (`Expr.findArgPosInnerCall?` +
`Expr.argPositionHoistPrefix?` / `Stmt.argPositionHoist?`): the leftmost, in
evaluation order, strictly-nested internal single-return call is hoisted into an
ordered prefix temp and the surrounding construct is re-lowered against it.
Variable declarations splice the temps as SIBLINGS at the statement-list level
so the declared local stays in scope; short-circuit right operands and ternary
branches are never hoisted (a conditionally-skipped call must not run).

These witnesses drive the imported source through the source semantics; `#guard`
pins each observable value. Real solc-0.8.35 / EVM ground truth (identical
values) lives in `tests/forge-harness/call-position-consolidated`:
  modifierArg 3, modifierNestedArg 4, arrayLit 34 (order 12), structArg 34
  (order 12), newArrayArg 3, newBytesArg 5, newContractArg 3, nestedArg 5,
  nestedIndexArg 10; call-free controls 12 / 12 / 4.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace CallPositionConsolidated

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/repro/fix/CallPositionConsolidated.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "CallposConsolidatedT"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "v",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "v") AssignOp.assign (Expr.ident "x"))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "CallPositionConsolidatedHarnessTarget"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "x", ty := Ty.uint 256 }, { name := "y", ty := Ty.uint 256 }] }), (ContractItem.stateVar
  { name := "z",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "ord",
    ty := Ty.uint 256,
    visibility := some Visibility.private_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "a",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "ord") AssignOp.assign (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "ord") (Expr.literal (Literal.number "10"))) (Expr.literal (Literal.number "1")))), Stmt.returnValues (some (Expr.literal (Literal.number "3")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "b",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "ord") AssignOp.assign (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "ord") (Expr.literal (Literal.number "10"))) (Expr.literal (Literal.number "2")))), Stmt.returnValues (some (Expr.literal (Literal.number "4")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inc",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "1"))))]) }), ContractItem.modifierDecl
  { name := "setZ"
    params := [{ name := some "v_", ty := Ty.uint 256, location := none }]
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "z") AssignOp.assign (Expr.ident "v_")), Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.function,
    name := some "modifierArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["setZ"] }, args := [Arg.positional (Expr.call (Expr.ident "a") [])], hasArgList := true }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "z"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "modifierNestedArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["setZ"] }, args := [Arg.positional (Expr.binary BinaryOp.add (Expr.call (Expr.ident "a") []) (Expr.literal (Literal.number "1")))], hasArgList := true }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "z"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arrayLit",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.ident "a") [], Expr.call (Expr.ident "b") []])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "10"))) (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arrayLitOrder",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "ord") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.ident "a") [], Expr.call (Expr.ident "b") []])), Stmt.ifElse (Expr.binary BinaryOp.eq (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "10"))) (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))) (Expr.literal (Literal.number "34"))) (Stmt.block [Stmt.returnValues (some (Expr.ident "ord"))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "999")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.call (Expr.ident "a") []), Arg.positional (Expr.call (Expr.ident "b") [])])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "s") "x") (Expr.literal (Literal.number "10"))) (Expr.member (Expr.ident "s") "y")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structArgOrder",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "ord") AssignOp.assign (Expr.literal (Literal.number "0"))), Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.call (Expr.ident "a") []), Arg.positional (Expr.call (Expr.ident "b") [])])), Stmt.ifElse (Expr.binary BinaryOp.eq (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "s") "x") (Expr.literal (Literal.number "10"))) (Expr.member (Expr.ident "s") "y")) (Expr.literal (Literal.number "34"))) (Stmt.block [Stmt.returnValues (some (Expr.ident "ord"))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "999")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "newArrayArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.call (Expr.ident "a") [])])), Stmt.returnValues (some (Expr.member (Expr.ident "arr") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "newBytesArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "bb", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.newExpr (Ty.bytes) [Arg.positional (Expr.binary BinaryOp.add (Expr.call (Expr.ident "a") []) (Expr.literal (Literal.number "2")))])), Stmt.returnValues (some (Expr.member (Expr.ident "bb") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "newContractArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "t", ty := Ty.user ({ segments := ["CallposConsolidatedT"] }), location := none }] (some (Expr.newExpr (Ty.user ({ segments := ["CallposConsolidatedT"] })) [Arg.positional (Expr.call (Expr.ident "a") [])])), Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "t") "v") []))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestedArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "inc") [Arg.positional (Expr.binary BinaryOp.add (Expr.call (Expr.ident "a") []) (Expr.literal (Literal.number "1")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestedIndexArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 3), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))], Expr.literal (Literal.number "8"), Expr.literal (Literal.number "9")])), Stmt.returnValues (some (Expr.call (Expr.ident "inc") [Arg.positional (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.sub (Expr.call (Expr.ident "a") []) (Expr.literal (Literal.number "1"))))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlArray",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "1"))], Expr.literal (Literal.number "2")])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "10"))) (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlStruct",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.literal (Literal.number "2"))])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.member (Expr.ident "s") "x") (Expr.literal (Literal.number "10"))) (Expr.member (Expr.ident "s") "y")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlNewArray",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.literal (Literal.number "4"))])), Stmt.returnValues (some (Expr.member (Expr.ident "arr") "length"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end CallPositionConsolidated
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace CallPositionConsolidated

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Call the no-argument public function `fn` on a freshly deployed instance and
    check its single `uint256` return equals `expect`. Contract creation inside a
    function body (`newContractArg`) is not driven here; its acceptance is pinned
    by `importedContractAccepted` and its value by the Forge lane. -/
private def callEq (fn : Name) (expect : Nat) : Bool :=
  (do
    let program ← CheckedInput.program importedSourceUnit
    let c ← CheckedProgram.contract program
      "CallPositionConsolidatedHarnessTarget"
    let cd ← CheckedContract.functionCalldata c fn []
    let r ← CheckedContract.callCalldata 300 c State.empty cd
    Except.ok
      (r.success &&
        r.output == wordToBytesBE wordBytes (expect : Word))).toOption.getD false

-- Whole contract (all five loci, including the external-creation #150) lowers.
#guard importedContractAccepted

-- #147 — modifier-invocation argument (bare and nested).
#guard callEq "modifierArg" 3
#guard callEq "modifierNestedArg" 4
-- #148 — array-literal element calls, and their left-to-right eval order.
#guard callEq "arrayLit" 34
#guard callEq "arrayLitOrder" 12
-- #149 — struct-constructor argument calls, and their eval order.
#guard callEq "structArg" 34
#guard callEq "structArgOrder" 12
-- #150 — `new` dynamic-array / `new bytes` length arguments.
#guard callEq "newArrayArg" 3
#guard callEq "newBytesArg" 5
-- #151 — calls nested (non-bare) inside function-call arguments.
#guard callEq "nestedArg" 5
#guard callEq "nestedIndexArg" 10
-- Controls — call-free argument positions keep their prior lowering/values.
#guard callEq "ctrlArray" 12
#guard callEq "ctrlStruct" 12
#guard callEq "ctrlNewArray" 4

end CallPositionConsolidated
end SolcAstImport
end Solidity
end SolidCore

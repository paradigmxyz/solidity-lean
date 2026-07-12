import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
NARROW-CLEANUP FAMILY (#182 / #183 / #184) — env-less value lowering formerly
dropped the operand-width checked-overflow cleanup (`uintCleanup`/`intCleanup`)
for a narrow (`uintN`/`intN`, N<256) value computed by checked arithmetic in
three leak positions, so the add/sub/mul silently ran at 256 bits and did NOT
Panic 0x11 on overflow:

  #182  for-init loop counter    `for (uint8 i = 250; i < 300; i++) { s++; }`
  #183  array `.push(...)`       `uint8[] arr; arr.push(a + c);`  (a=200,c=100)
  #184  struct-ctor field        `S st; st = S(a + c, 0);`         on assign/vardecl

The fix routes each value through the env-aware `toCoreAsWithEnv?` with the
correct target type so the operand-width cleanup fires (Panic 0x11), while a
GENUINE explicit truncating cast (`uint8(w)`), a safe (no-overflow) value, and
an `unchecked` wrap are all preserved.

Real-EVM Forge ground truth: `tests/forge-harness/narrow-cleanup-family`
(11 tests PASS on solc 0.8.35 + the EVM: the overflow entries Panic 0x11, the
`*Cast` entries truncate to 44, the safe/wrap entries return their values).
`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace NarrowCleanupFamilyWitness

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/fix-wt-enumpacked/tests/forge-harness/narrow-cleanup-family/src/NarrowCleanupFamily.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "NarrowCleanupFamilyHarnessTarget"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "x", ty := Ty.uint 8 }, { name := "y", ty := Ty.uint 8 }] }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.uint 8) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr2d",
    ty := Ty.array (Ty.array (Ty.uint 8) (none)) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "st",
    ty := Ty.user ({ segments := ["S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "forCounterOverflow",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "s", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 8, location := none }] (some (Expr.literal (Literal.number "250"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.literal (Literal.number "300")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "s"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "forCounterSafe",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "s", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 8, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.literal (Literal.number "10")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "s"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "forCounterUncheckedWrap",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := some "s", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 8, location := none }] (some (Expr.literal (Literal.number "250"))))) (some (Expr.binary BinaryOp.ne (Expr.ident "i") (Expr.literal (Literal.number "5")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "s"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushAdd",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "c", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c"))]), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.sub (Expr.member (Expr.ident "arr") "length") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushCast",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "w", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "w")])]), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.sub (Expr.member (Expr.ident "arr") "length") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushSafe",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.ident "a")]), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.sub (Expr.member (Expr.ident "arr") "length") (Expr.literal (Literal.number "1")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "push2dAdd",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "c", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr2d") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "arr2d") (Expr.literal (Literal.number "0"))) "push") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c"))]), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "arr2d") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structAssignAdd",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "c", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "st") AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c")), Arg.positional (Expr.literal (Literal.number "0"))])), Stmt.returnValues (some (Expr.member (Expr.ident "st") "x"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structVarDeclAdd",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "c", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c")), Arg.positional (Expr.literal (Literal.number "0"))])), Stmt.returnValues (some (Expr.member (Expr.ident "s") "x"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structCast",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "w", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "st") AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "w")]), Arg.positional (Expr.literal (Literal.number "0"))])), Stmt.returnValues (some (Expr.member (Expr.ident "st") "x"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structReturnAdd",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "c", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c")), Arg.positional (Expr.literal (Literal.number "0"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end NarrowCleanupFamilyWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace NarrowCleanupFamily

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.NarrowCleanupFamilyWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.NarrowCleanupFamilyWitness.importedContractAccepted

-- #182 for-init narrow counter overflows -> Panic 0x11.
def forCounterOverflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 Fam "forCounterOverflow" State.empty [] 17
-- no-regression: safe counter counts to 10.
def forCounterSafe_is_10 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 Fam "forCounterSafe" State.empty [] 10
-- no-regression: unchecked narrow counter WRAPS 255->0, terminates at 11 iters.
def forCounterUncheckedWrap_is_11 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 Fam "forCounterUncheckedWrap" State.empty [] 11

-- #183 push of narrow checked arithmetic overflows -> Panic 0x11.
def pushAdd_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 Fam "pushAdd" State.empty
    [Value.word 200, Value.word 100] 17
-- no-regression: explicit truncating cast in push stays 44.
def pushCast_is_44 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 Fam "pushCast" State.empty [Value.word 300] 44
-- no-regression: safe push returns the value.
def pushSafe_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 Fam "pushSafe" State.empty [Value.word 7] 7
-- #183 nested 2d push overflows -> Panic 0x11.
def push2dAdd_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 Fam "push2dAdd" State.empty
    [Value.word 200, Value.word 100] 17

-- #184 struct-ctor field on assign overflows -> Panic 0x11.
def structAssignAdd_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 Fam "structAssignAdd" State.empty
    [Value.word 200, Value.word 100] 17
-- #184 struct-ctor field on vardecl overflows -> Panic 0x11.
def structVarDeclAdd_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 Fam "structVarDeclAdd" State.empty
    [Value.word 200, Value.word 100] 17
-- no-regression: explicit truncating cast in struct-ctor field stays 44.
def structCast_is_44 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 Fam "structCast" State.empty [Value.word 300] 44

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue forCounterOverflow_panics
#guard isOkTrue forCounterSafe_is_10
#guard isOkTrue forCounterUncheckedWrap_is_11
#guard isOkTrue pushAdd_panics
#guard isOkTrue pushCast_is_44
#guard isOkTrue pushSafe_is_7
#guard isOkTrue push2dAdd_panics
#guard isOkTrue structAssignAdd_panics
#guard isOkTrue structVarDeclAdd_panics
#guard isOkTrue structCast_is_44

end NarrowCleanupFamily
end Witness
end Solidity
end SolidCore

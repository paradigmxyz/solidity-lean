import SolidCore.Witness.Prepared
import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
ENV-LOWERING UNIFICATION (R2, rearchitecture phase 3) — the env-less shadow
lowering (`Expr.toCore?`) was the PRIMARY path for several statement/expression
positions, so a narrow (`uintN`/`intN`, N<256) checked arithmetic value in
those positions lost its operand-width cleanup (`uintCleanup`/`intCleanup`) —
no Panic 0x11 where solc 0.8.35 + the EVM Panic, and (in `unchecked`) a
256-bit value where the EVM wraps at the narrow width. Positions pinned here
(all real-EVM verified, `tests/forge-harness/cond-narrow-cleanup`, 22/22 PASS
on solc 0.8.35 + Forge):

  while / for / do-while CONDITIONS   `while ((a + b) < n)`     (uint8 a,b)
  assert condition                    `assert((a + b) < n)`
  discard-expression statement        `a + b;`
  `&&` / `!` wrapped comparisons      `(a + b) < n && …`, `!((a + b) < n)`
  narrow index keys                   `arr[a + b]`
  int8 loop condition                 `while ((a + b) > -100)`  (int8 a,b)

The fix (Stage B+C): ONE fuel-bounded env-aware recursion
(`Expr.toCoreAsWithEnvFuel?`) threads the type env through every child
(binary operands incl. `&&`/`||` at bool, `!` at bool, ternary branches, cast
arguments, narrow index keys), and every call-free condition / discard
statement routes through it (`Expr.conditionCoreWithEnv?`). Explicit casts
stay TRUNCATING, `unchecked` WRAPS at the narrow width, safe values are
untouched — pinned below alongside the panics.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EnvLoweringUnifyWitness

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/fix-wt-enumpacked/tests/forge-harness/cond-narrow-cleanup/src/CondNarrowCleanup.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "CondNarrowCleanupHarnessTarget"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "whileCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.whileLoop (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k")), Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "a"))]), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "forCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k")), Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "a")), Stmt.ifElse (Expr.binary BinaryOp.gt (Expr.ident "k") (Expr.literal (Literal.number "5"))) (Stmt.break) none]), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "doWhileCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.doWhile (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k"))]) (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Expr.binary BinaryOp.lt (Expr.ident "k") (Expr.literal (Literal.number "3")))), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "plainCmp",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ifCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.ifElse (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "2")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "requireCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))), Arg.positional (Expr.literal (Literal.string "nope"))]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assertCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250")))]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "exprStmt",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), Stmt.returnValues (some (Expr.literal (Literal.number "7")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "eqCmp",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.eq (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "44"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "whileCondSafe",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.whileLoop (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "10"))) (Expr.binary BinaryOp.lt (Expr.ident "k") (Expr.literal (Literal.number "4")))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k")), Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "a"))]), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "plainCmpSafe",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "10"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "uncheckedCmp",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "uncheckedWhile",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.unchecked (Stmt.block [Stmt.whileLoop (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Expr.binary BinaryOp.lt (Expr.ident "k") (Expr.literal (Literal.number "3")))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k"))])]), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "castCmp",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "w", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.lt (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.ident "w")]) (Expr.literal (Literal.number "250"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "intWhileCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.int 8, location := none }, { name := some "b", ty := Ty.int 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.whileLoop (Expr.binary BinaryOp.gt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "100")))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k")), Stmt.expr (Expr.unary UnaryOp.postDecrement (Expr.ident "a")), Stmt.ifElse (Expr.binary BinaryOp.gt (Expr.ident "k") (Expr.literal (Literal.number "3"))) (Stmt.returnValues (some (Expr.ident "k"))) none]), Stmt.returnValues (some (Expr.ident "k"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ifAndCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.ifElse (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Expr.binary BinaryOp.gt (Expr.ident "a") (Expr.literal (Literal.number "0")))) (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "2")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ifNotCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.ifElse (Expr.unary UnaryOp.logicalNot (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250")))) (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "2")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "idxKey",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "arr", ty := Ty.array (Ty.uint 256) (some 300), location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "44"))) AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inner",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callArg",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "inner") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "whileAndCond",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "k", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.whileLoop (Expr.binary BinaryOp.boolAnd (Expr.binary BinaryOp.lt (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "250"))) (Expr.binary BinaryOp.lt (Expr.ident "k") (Expr.literal (Literal.number "3")))) (Stmt.block [Stmt.expr (Expr.unary UnaryOp.postIncrement (Expr.ident "k"))]), Stmt.returnValues (some (Expr.ident "k"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EnvLoweringUnifyWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace EnvLoweringUnify

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.EnvLoweringUnifyWitness.importedContract

private def preparedC : Prepared.Contract :=
  CheckedInput.ownContract C

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.EnvLoweringUnifyWitness.importedContractAccepted

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def overflowArgs : List Value := [Value.word 200, Value.word 100]

-- while condition: narrow overflow -> Panic 0x11.
def whileCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "whileCond" State.empty overflowArgs 17
-- for condition.
def forCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "forCond" State.empty overflowArgs 17
-- do-while condition.
def doWhileCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "doWhileCond" State.empty overflowArgs 17
-- assert condition.
def assertCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "assertCond" State.empty overflowArgs 17
-- discard-expression statement `a + b;`.
def exprStmt_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "exprStmt" State.empty overflowArgs 17
-- int8 while condition (negative-side overflow).
def intWhileCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "intWhileCond" State.empty
    [Value.int (wordModulus - 100), Value.int (wordModulus - 50)] 17
-- `&&`-wrapped comparison in an if condition.
def ifAndCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "ifAndCond" State.empty overflowArgs 17
-- `!`-wrapped comparison in an if condition.
def ifNotCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "ifNotCond" State.empty overflowArgs 17
-- narrow index key.
def idxKey_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "idxKey" State.empty overflowArgs 17
-- `&&`-wrapped comparison in a while condition.
def whileAndCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "whileAndCond" State.empty overflowArgs 17

-- Already-correct positions (regression pins).
def plainCmp_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "plainCmp" State.empty overflowArgs 17
def ifCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "ifCond" State.empty overflowArgs 17
def requireCond_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "requireCond" State.empty overflowArgs 17
def eqCmp_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "eqCmp" State.empty overflowArgs 17
def callArg_panics : Except TypeError Bool :=
  Prepared.panicMatches 300 preparedC "callArg" State.empty overflowArgs 17

-- Safe / truncating / unchecked controls (three-way semantics preserved).
def whileCondSafe_is_3 : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "whileCondSafe" State.empty
    [Value.word 3, Value.word 4] 3
def plainCmpSafe_is_true : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "plainCmpSafe" State.empty
    [Value.word 3, Value.word 4] 1
-- unchecked comparison WRAPS at uint8 width: 200+100 -> 44 < 250 -> true.
def uncheckedCmp_wraps_true : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "uncheckedCmp" State.empty overflowArgs 1
-- unchecked while condition wraps and the loop runs (k = 3).
def uncheckedWhile_wraps_is_3 : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "uncheckedWhile" State.empty overflowArgs 3
-- explicit cast stays TRUNCATING: uint8(300) -> 44 < 250 -> true.
def castCmp_truncates_true : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "castCmp" State.empty [Value.word 300] 1
def idxKeySafe_is_9 : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "idxKey" State.empty
    [Value.word 40, Value.word 4] 9
def callArgSafe_is_44 : Except TypeError Bool :=
  Prepared.wordMatches 300 preparedC "callArg" State.empty
    [Value.word 40, Value.word 4] 44


#eval Prepared.assertChecks [
  ("EnvLoweringUnify:363", (
    accepted
  )),
  ("EnvLoweringUnify:364", (
    isOkTrue whileCond_panics
  )),
  ("EnvLoweringUnify:365", (
    isOkTrue forCond_panics
  )),
  ("EnvLoweringUnify:366", (
    isOkTrue doWhileCond_panics
  )),
  ("EnvLoweringUnify:367", (
    isOkTrue assertCond_panics
  )),
  ("EnvLoweringUnify:368", (
    isOkTrue exprStmt_panics
  )),
  ("EnvLoweringUnify:369", (
    isOkTrue intWhileCond_panics
  )),
  ("EnvLoweringUnify:370", (
    isOkTrue ifAndCond_panics
  )),
  ("EnvLoweringUnify:371", (
    isOkTrue ifNotCond_panics
  )),
  ("EnvLoweringUnify:372", (
    isOkTrue idxKey_panics
  )),
  ("EnvLoweringUnify:373", (
    isOkTrue whileAndCond_panics
  )),
  ("EnvLoweringUnify:374", (
    isOkTrue plainCmp_panics
  )),
  ("EnvLoweringUnify:375", (
    isOkTrue ifCond_panics
  )),
  ("EnvLoweringUnify:376", (
    isOkTrue requireCond_panics
  )),
  ("EnvLoweringUnify:377", (
    isOkTrue eqCmp_panics
  )),
  ("EnvLoweringUnify:378", (
    isOkTrue callArg_panics
  )),
  ("EnvLoweringUnify:379", (
    isOkTrue whileCondSafe_is_3
  )),
  ("EnvLoweringUnify:380", (
    isOkTrue plainCmpSafe_is_true
  )),
  ("EnvLoweringUnify:381", (
    isOkTrue uncheckedCmp_wraps_true
  )),
  ("EnvLoweringUnify:382", (
    isOkTrue uncheckedWhile_wraps_is_3
  )),
  ("EnvLoweringUnify:383", (
    isOkTrue castCmp_truncates_true
  )),
  ("EnvLoweringUnify:384", (
    isOkTrue idxKeySafe_is_9
  )),
  ("EnvLoweringUnify:385", (
    isOkTrue callArgSafe_is_44
  ))
]
end EnvLoweringUnify
end Witness
end Solidity
end SolidCore

import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
STAGE-D COMPLETION (#193 / #194 / #195) — three env-less-lowering gaps closed:

  #193  builtin/abi.encode* call ARGUMENTS skipped narrow checked arithmetic:
        `keccak256(abi.encodePacked(a + b))`, `abi.encode(a + b)`,
        `bytes.concat(bytes1(a + b))`, `abi.encodePacked(a * b)` (uint8),
        `abi.encode(-a)` (int8 -128) ran the operand at 256 bits instead of
        Panicking 0x11 at the operand width. Fixed by env-aware `abi.*`/hash/
        concat arms in `Expr.toCoreAsWithEnvFuel?` plus rerouting the flagged
        return shapes (`Expr.abiBuiltinArgsNeedEnvCleanup`) out of the env-less
        return dispatcher. LITERAL-only args still constant-fold
        (`abi.encode(2**112)`, uniswap-v2 UQ112x112 shape).

  #194  LVALUE index KEYS skipped narrow checked arithmetic: `arr[a+b] = v`,
        `mp[a+b] = v`, `arr2[1][a+b] = v`, `bs[a+b] = 0x41` (uint8 200+100)
        wrote at 300 with no Panic. Fixed by `Expr.toCoreLValueWithEnv?`
        (env-aware key lowering in `assignmentCoreWithEnv?`).

  #195  emit call-arg hoisting defeated solc's TWO-PHASE event-arg schedule
        (indexed args in REVERSE source order first, then data args forward —
        `ExpressionCompiler.cpp` `Kind::Event`): `emit E2(f(), g(), f())`
        (2nd indexed) must run g,f,f (trace 211, topic y=2, data 21,211);
        `emit E3(f(), g())` both-indexed must run g,f (trace 21, topics 21,2).
        Fixed by `emitTwoPhaseHoist?` binding hoist temps in schedule order
        (threaded via `EventIndexedEnv`), applied in `Stmt.anfPreprocess` even
        when the emit lowers directly. All-data emits stay L2R byte-identical.

Real-EVM Forge ground truth: `tests/forge-harness/stage-d-completion`
(18 tests PASS on solc 0.8.35 + the EVM). `#eval`-confirmed booleans pinned
with `#guard` (the project avoids `native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StageDCompletionWitness

def importedSourceName : String := "tests/forge-harness/stage-d-completion/src/StageDCompletion.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StageDCompletion"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.uint 256) (some 400),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr2",
    ty := Ty.array (Ty.array (Ty.uint 256) (some 400)) (some 2),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "mp",
    ty := Ty.mapping (Ty.uint 8) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "bs",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "trace",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.eventDecl
  { name := "E2",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }, { name := some "y", ty := Ty.uint 256, indexed := true }, { name := some "z", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "E3",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := true }, { name := some "y", ty := Ty.uint 256, indexed := true }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "ED",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }, { name := some "y", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h1",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h2",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h3",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.typeName (Ty.bytes)) "concat") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h4",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.ident "b"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h5",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.int 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.unary UnaryOp.neg (Expr.ident "a"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c1",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }] (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))), Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.ident "c")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c2",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c3",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.sub (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hSafe",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "w1",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "300"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "w2",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "mp") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.index (Expr.ident "mp") (Expr.literal (Literal.number "44"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "w3",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "arr2") (Expr.literal (Literal.number "1"))) (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.literal (Literal.number "3"))), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "arr2") (Expr.literal (Literal.number "1"))) (Expr.literal (Literal.number "300"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "w4",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "bs") AssignOp.assign (Expr.newExpr (Ty.bytes) [Arg.positional (Expr.literal (Literal.number "400"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "bs") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.literal (Literal.number "0x41"))), Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.index (Expr.ident "bs") (Expr.literal (Literal.number "300")))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "wSafe",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "rRead",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "trace") AssignOp.assign (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "trace") (Expr.literal (Literal.number "10"))) (Expr.literal (Literal.number "1")))), Stmt.returnValues (some (Expr.ident "trace"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "trace") AssignOp.assign (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "trace") (Expr.literal (Literal.number "10"))) (Expr.literal (Literal.number "2")))), Stmt.returnValues (some (Expr.ident "trace"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emit2",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "E2") [Arg.positional (Expr.call (Expr.ident "f") []), Arg.positional (Expr.call (Expr.ident "g") []), Arg.positional (Expr.call (Expr.ident "f") [])]), Stmt.returnValues (some (Expr.ident "trace"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emit3",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "E3") [Arg.positional (Expr.call (Expr.ident "f") []), Arg.positional (Expr.call (Expr.ident "g") [])]), Stmt.returnValues (some (Expr.ident "trace"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitData",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "ED") [Arg.positional (Expr.call (Expr.ident "f") []), Arg.positional (Expr.call (Expr.ident "g") [])]), Stmt.returnValues (some (Expr.ident "trace"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StageDCompletionWitness
end SolcAstImport
end Solidity
end SolidCore


namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StageDCompletionLitWitness

def importedSourceName : String := "inline: literal-fold control (abi.encode(2**112) / abi.encodePacked(uint8(3 + 4)))"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Lit"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "lit",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.exp (Expr.literal (Literal.number "2")) (Expr.literal (Literal.number "112")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "litPacked",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.binary BinaryOp.add (Expr.literal (Literal.number "3")) (Expr.literal (Literal.number "4")))])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StageDCompletionLitWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StageDCompletion

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.StageDCompletionWitness.importedContract
abbrev L := SolidCore.Solidity.SolcAstImport.StageDCompletionLitWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StageDCompletionWitness.importedContractAccepted
def litAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StageDCompletionLitWitness.importedContractAccepted

-- #193: narrow checked arithmetic in abi.encode*/keccak256/concat call
-- ARGUMENTS Panics 0x11 at the operand width (uint8 200+100 / 100*100, int8
-- -(-128)) instead of silently running at 256 bits.
def h1_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "h1" State.empty
    [Value.word 200, Value.word 100] 17
def h2_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "h2" State.empty
    [Value.word 200, Value.word 100] 17
def h3_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "h3" State.empty
    [Value.word 200, Value.word 100] 17
def h4_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "h4" State.empty
    [Value.word 100, Value.word 100] 17
def h5_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "h5" State.empty
    [Value.int (2 ^ 256 - 128)] 17
-- #193 controls: statement-level narrow assign then hash still panics; 256-bit
-- overflow/underflow still panic; safe values hash correctly
-- (keccak256(0x07) = 0xee2a4bc7…cebc, real-EVM `cast keccak 0x07`).
def c1_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "c1" State.empty
    [Value.word 200, Value.word 100] 17
def c2_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "c2" State.empty
    [Value.word (2 ^ 256 - 1), Value.word 5] 17
def c3_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "c3" State.empty
    [Value.word 3, Value.word 5] 17
def hSafe_matches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "hSafe" State.empty
    [Value.word 3, Value.word 4]
    0xee2a4bc7db81da2b7164e56b3649b1e2a09c58c455b15dabddd9146c7582cebc
-- #193 literal-fold control: literal-only args still constant-fold
-- (`abi.encode(2**112)` — the uniswap-v2 UQ112x112 shape — and
-- `abi.encodePacked(uint8(3 + 4))`).
def lit_encodes_2pow112 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 300 L "lit" State.empty []
    (wordToBytesBE wordBytes (2 ^ 112))
def litPacked_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 300 L "litPacked" State.empty [] [7]

-- #194: narrow checked arithmetic in an LVALUE index KEY Panics 0x11 (no
-- write) — fixed array, mapping, nested array, storage bytes.
def w1_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "w1" State.empty
    [Value.word 200, Value.word 100] 17
def w2_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "w2" State.empty
    [Value.word 200, Value.word 100] 17
def w3_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "w3" State.empty
    [Value.word 200, Value.word 100] 17
def w4_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "w4" State.empty
    [Value.word 200, Value.word 100] 17
-- #194 controls: safe key writes and reads back; read-side key still panics.
def wSafe_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "wSafe" State.empty
    [Value.word 3, Value.word 4] 7
def rRead_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "rRead" State.empty
    [Value.word 200, Value.word 100] 17

-- #195: emit call-arg evaluation follows solc's TWO-PHASE schedule (indexed
-- args in REVERSE source order first, then data args forward). Real-EVM Forge
-- ground truth: emit2 trace 211, topic y=2, data (21,211); emit3 trace 21,
-- topics (21,2); all-data control emitData stays L2R: trace 12, data (1,12).
def emit2_two_phase : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 300 C (CallTarget.name "emit2") State.empty []
  match result with
  | CallResult.returned state [Value.word 211] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "E2" &&
              event.topics ==
                [Keccak.digestWord "E2(uint256,uint256,uint256)", 2] &&
              event.dataBytes ==
                wordToBytesBE wordBytes 21 ++ wordToBytesBE wordBytes 211)
      | _ => Except.ok false
  | _ => Except.ok false
def emit3_two_phase : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 300 C (CallTarget.name "emit3") State.empty []
  match result with
  | CallResult.returned state [Value.word 21] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "E3" &&
              event.topics ==
                [Keccak.digestWord "E3(uint256,uint256)", 21, 2])
      | _ => Except.ok false
  | _ => Except.ok false
def emitData_l2r : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 300 C (CallTarget.name "emitData") State.empty []
  match result with
  | CallResult.returned state [Value.word 12] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "ED" &&
              event.topics == [Keccak.digestWord "ED(uint256,uint256)"] &&
              event.dataBytes ==
                wordToBytesBE wordBytes 1 ++ wordToBytesBE wordBytes 12)
      | _ => Except.ok false
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard litAccepted
#guard isOkTrue h1_panics
#guard isOkTrue h2_panics
#guard isOkTrue h3_panics
#guard isOkTrue h4_panics
#guard isOkTrue h5_panics
#guard isOkTrue c1_panics
#guard isOkTrue c2_panics
#guard isOkTrue c3_panics
#guard isOkTrue hSafe_matches
#guard isOkTrue lit_encodes_2pow112
#guard isOkTrue litPacked_is_7
#guard isOkTrue w1_panics
#guard isOkTrue w2_panics
#guard isOkTrue w3_panics
#guard isOkTrue w4_panics
#guard isOkTrue wSafe_is_7
#guard isOkTrue rRead_panics
#guard isOkTrue emit2_two_phase
#guard isOkTrue emit3_two_phase
#guard isOkTrue emitData_l2r

end StageDCompletion
end Witness
end Solidity
end SolidCore

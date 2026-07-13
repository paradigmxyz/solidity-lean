import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
#201 BUILTIN-ARG-NARROW-CLEANUP-RESIDUE — the positions the Stage-D
(#193/#194/#195) fix missed. Narrow (uint8) checked arithmetic inside an
abi/hash/concat builtin ARGUMENT must Panic 0x11 at the operand width in EVERY
statement position, not just RETURN/plain-assign:

  A. assignment RHS member-call builtin (`z = abi.encode(a + b)`,
     `z = bytes.concat(bytes1(a + b))`, `s = abi.encodePacked(a + b)`)
  B. vardecl init (`bytes memory z = abi.encode(a + b)`,
     `bytes32 h = keccak256(abi.encodePacked(a + b))`,
     `uint256 c = uint256(keccak256(abi.encode(a + b)))`)
  C. require `.length`-of-builtin condition
     (`require(abi.encode(a + b).length > 0)`)
  D. emit builtin/pure args (`emit EB(abi.encode(a + b))`,
     `emit EH(keccak256(…))`, `emit EMix(a + b, bump())` — the panic fires
     BEFORE `bump()` runs)
  E. revert custom-error arg (`revert Err(abi.encode(a + b))` — the wrong
     256-bit revert DATA becomes the Panic 0x11)
  F. nested builtin-in-builtin (`keccak256(bytes.concat(abi.encode(a + b)))`
     in RETURN position, `abi.encode(abi.encodePacked(a + b))`)
  G. compound-assign / delete lvalue keys (`arr[a + b] += 1`,
     `delete arr[a + b]` — no write, Panic 0x11)

Fixed by wiring the EXISTING env-aware helpers (`assignmentCoreWithEnv?`,
`varDeclCoreWithEnv?`, `toCoreLValueWithEnv?`, the env-aware `abi.*`/hash/
concat expression arms) into the residual dispatcher arms, plus one more
recursion level in `Expr.abiArgNeedsEnvCleanup?` (a builtin argument that is
itself a builtin call) and `.length`-of-builtin / cast-of-builtin arms in
`Expr.toCoreAsWithEnvFuel?`.

Real-EVM Forge ground truth: `tests/forge-harness/builtin-arg-residue`
(29 tests PASS on pinned solc 0.8.35). `#eval`-confirmed booleans pinned with
`#guard` (the project avoids `native_decide`).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LoweringUnifyWitness

def importedSourceName : String := "tests/forge-harness/builtin-arg-residue/src/BuiltinArgResidue.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "BuiltinArgResidue"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "EB",
    params := [{ name := some "d", ty := Ty.bytes, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "EH",
    params := [{ name := some "h", ty := Ty.bytesN 32, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "EMix",
    params := [{ name := some "x", ty := Ty.uint 8, indexed := false }, { name := some "y", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "Err",
    params := [{ name := some "d", ty := Ty.bytes, location := none }] }), (ContractItem.stateVar
  { name := "s",
    ty := Ty.bytes,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "cnt",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.uint 256) (none),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.mapping (Ty.uint 256) (Ty.uint 256)),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.array (Ty.uint 256) (none) }] }), (ContractItem.stateVar
  { name := "st",
    ty := Ty.user ({ segments := ["S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.literal (Literal.number "400")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.ident "i")])]), Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.literal (Literal.number "400")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.member (Expr.ident "st") "a") "push") [Arg.positional (Expr.ident "i")])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlReturn",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlStmt",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }] (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))), Stmt.returnValues (some (Expr.ident "c"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ctrlSafe",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "asgLocal",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "z", ty := Ty.bytes, location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.ident "z") AssignOp.assign (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "z") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "asgHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "h", ty := Ty.bytesN 32, location := none }] none, Stmt.expr (Expr.assign (Expr.ident "h") AssignOp.assign (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])), Stmt.returnValues (some (Expr.ident "h"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "asgConcat",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "z", ty := Ty.bytes, location := some DataLocation.memory }] none, Stmt.expr (Expr.assign (Expr.ident "z") AssignOp.assign (Expr.call (Expr.member (Expr.typeName (Ty.bytes)) "concat") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])), Stmt.returnValues (some (Expr.member (Expr.ident "z") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "asgStorage",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.assign (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "s") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "vdBytes",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "z", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "z") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "vdHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "h", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])), Stmt.returnValues (some (Expr.ident "h"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "vdNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])])), Stmt.returnValues (some (Expr.binary BinaryOp.mod (Expr.ident "c") (Expr.literal (Literal.number "7"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "reqHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }, { name := some "h", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]) (Expr.ident "h")), Arg.positional (Expr.literal (Literal.string "no"))]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "reqEnc",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.gt (Expr.member (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]) "length") (Expr.literal (Literal.number "0"))), Arg.positional (Expr.literal (Literal.string "no"))]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assertHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }, { name := some "h", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "assert") [Arg.positional (Expr.binary BinaryOp.ne (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]) (Expr.ident "h"))]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitEnc",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EB") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EH") [Arg.positional (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revErr",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Err") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sinkB",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "d", ty := Ty.bytes, location := some DataLocation.memory }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "d") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sinkH",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "h", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "h"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callEnc",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "sinkB") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "callHash",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "sinkH") [Arg.positional (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestConcat",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.typeName (Ty.bytes)) "concat") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "nestEnc",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "z", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])), Stmt.returnValues (some (Expr.member (Expr.ident "z") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "cnt") AssignOp.assign (Expr.binary BinaryOp.add (Expr.ident "cnt") (Expr.literal (Literal.number "1")))), Stmt.returnValues (some (Expr.ident "cnt"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitMix",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EMix") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), Arg.positional (Expr.call (Expr.ident "bump") [])]), Stmt.returnValues (some (Expr.ident "cnt"))]) }), (ContractItem.eventDecl
  { name := "EO",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := false }, { name := some "y", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitOrder",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EO") [Arg.positional (Expr.ident "cnt"), Arg.positional (Expr.call (Expr.ident "bump") [])]), Stmt.returnValues (some (Expr.ident "cnt"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lvStruct",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }, { name := some "v", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "st") "a") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.ident "v")), Stmt.returnValues (some (Expr.index (Expr.member (Expr.ident "st") "a") (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lvMapDeep",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }, { name := some "k1", ty := Ty.uint 256, location := none }, { name := some "v", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "m") (Expr.ident "k1")) (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.assign (Expr.ident "v")), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "m") (Expr.ident "k1")) (Expr.literal (Literal.number "300"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lvCompound",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))) AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "300"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "lvDelete",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))), Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "300"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LoweringUnifyWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace LoweringUnify

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C :=
  SolidCore.Solidity.SolcAstImport.LoweringUnifyWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.LoweringUnifyWitness.importedContractAccepted

def ab : List Value := [Value.word 200, Value.word 100]

-- A. assignment RHS member-call builtin (Panic 0x11 at uint8 width).
def asgLocal_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "asgLocal" State.empty ab 17
def asgHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "asgHash" State.empty ab 17
def asgConcat_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "asgConcat" State.empty ab 17
def asgStorage_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "asgStorage" State.empty ab 17

-- B. vardecl init (incl. the cast-of-builtin shape vdNested).
def vdBytes_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "vdBytes" State.empty ab 17
def vdHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "vdHash" State.empty ab 17
def vdNested_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "vdNested" State.empty ab 17

-- C. require/assert conditions (comparison operand + `.length`-of-builtin).
def reqHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "reqHash" State.empty
    (ab ++ [Value.word 0]) 17
def reqEnc_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "reqEnc" State.empty ab 17
def assertHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "assertHash" State.empty
    (ab ++ [Value.word 0]) 17

-- D. emit args (builtin arg; pure narrow-arith arg BEFORE a call arg).
def emitEnc_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "emitEnc" State.empty ab 17
def emitHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "emitHash" State.empty ab 17
def emitMix_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "emitMix" State.empty ab 17

-- E. revert custom-error arg: the arith evaluates (and Panics) BEFORE the
-- custom revert data is built — previously reverted `Err(encode(300))`.
def revErr_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "revErr" State.empty ab 17

-- F. nested builtin-in-builtin (incl. the RETURN-position miss nestConcat).
def nestConcat_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "nestConcat" State.empty ab 17
def nestEnc_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "nestEnc" State.empty ab 17

-- G. compound-assign / delete lvalue keys (Panic 0x11, no write).
def lvCompound_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "lvCompound" State.empty ab 17
def lvDelete_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "lvDelete" State.empty ab 17

-- CONTROLS (green before #201; must stay green).
def ctrlReturn_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "ctrlReturn" State.empty ab 17
def ctrlStmt_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "ctrlStmt" State.empty ab 17
def callEnc_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "callEnc" State.empty ab 17
def callHash_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "callHash" State.empty ab 17
def lvStruct_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "lvStruct" State.empty
    (ab ++ [Value.word 7]) 17
def lvMapDeep_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 C "lvMapDeep" State.empty
    (ab ++ [Value.word 1, Value.word 7]) 17
-- Safe values keep their exact real-EVM results.
def ctrlSafe_is_enc7 : Except TypeError Bool :=
  Examples.checkedOwnCallBytesMatches 300 C "ctrlSafe" State.empty
    [Value.word 3, Value.word 4] (wordToBytesBE wordBytes 7)
def vdBytes_safe_is_32 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "vdBytes" State.empty
    [Value.word 3, Value.word 4] 32
def asgStorage_safe_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "asgStorage" State.empty
    [Value.word 3, Value.word 4] 1
def nestEnc_safe_is_96 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "nestEnc" State.empty
    [Value.word 3, Value.word 4] 96
def emitMix_safe_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 C "emitMix" State.empty
    [Value.word 3, Value.word 4] 1
-- Two-phase emit control: `emit EO(cnt, bump())` still logs data [0, 1]
-- (the pure first arg reads cnt BEFORE bump()).
def emitOrder_logs_0_1 : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 300 C (CallTarget.name "emitOrder") State.empty []
  match result with
  | CallResult.returned state [Value.word 1] =>
      match state.events with
      | [event] =>
          Except.ok
            (event.name == "EO" &&
              event.topics == [Keccak.digestWord "EO(uint256,uint256)"] &&
              event.dataBytes ==
                wordToBytesBE wordBytes 0 ++ wordToBytesBE wordBytes 1)
      | _ => Except.ok false
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue asgLocal_panics
#guard isOkTrue asgHash_panics
#guard isOkTrue asgConcat_panics
#guard isOkTrue asgStorage_panics
#guard isOkTrue vdBytes_panics
#guard isOkTrue vdHash_panics
#guard isOkTrue vdNested_panics
#guard isOkTrue reqHash_panics
#guard isOkTrue reqEnc_panics
#guard isOkTrue assertHash_panics
#guard isOkTrue emitEnc_panics
#guard isOkTrue emitHash_panics
#guard isOkTrue emitMix_panics
#guard isOkTrue revErr_panics
#guard isOkTrue nestConcat_panics
#guard isOkTrue nestEnc_panics
#guard isOkTrue lvCompound_panics
#guard isOkTrue lvDelete_panics
#guard isOkTrue ctrlReturn_panics
#guard isOkTrue ctrlStmt_panics
#guard isOkTrue callEnc_panics
#guard isOkTrue callHash_panics
#guard isOkTrue lvStruct_panics
#guard isOkTrue lvMapDeep_panics
#guard isOkTrue ctrlSafe_is_enc7
#guard isOkTrue vdBytes_safe_is_32
#guard isOkTrue asgStorage_safe_is_1
#guard isOkTrue nestEnc_safe_is_96
#guard isOkTrue emitMix_safe_is_1
#guard isOkTrue emitOrder_logs_0_1

end LoweringUnify
end Witness
end Solidity
end SolidCore

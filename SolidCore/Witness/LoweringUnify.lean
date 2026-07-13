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

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace LoweringUnifyAuditWitness

def importedSourceName : String := "tests/forge-harness/lowering-unify-audit/src/AuditProbe.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L8"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "idm",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "v", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "y", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.ident "y") (Expr.literal (Literal.number "2"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "z", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "z") (Expr.literal (Literal.number "5"))))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "AuditProbe"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "EMix",
    params := [{ name := some "x", ty := Ty.uint 8, indexed := false }, { name := some "y", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "EI",
    params := [{ name := some "x", ty := Ty.uint 8, indexed := true }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "E2I",
    params := [{ name := some "x", ty := Ty.uint 256, indexed := true }, { name := some "y", ty := Ty.uint 256, indexed := true }],
    anonymous := false }), (ContractItem.errorDecl
  { name := "Err",
    params := [{ name := some "d", ty := Ty.bytes, location := none }] }), (ContractItem.structDecl
  { name := "P",
    fields := [{ name := "v", ty := Ty.uint 8 }] }), (ContractItem.stateVar
  { name := "cnt",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr8",
    ty := Ty.array (Ty.uint 8) (none),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m8",
    ty := Ty.mapping (Ty.uint 8) (Ty.uint 256),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.uint 256) (none),
    visibility := some Visibility.public_,
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
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.literal (Literal.number "400")))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.ident "i")])]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m8") (Expr.literal (Literal.number "44"))) AssignOp.assign (Expr.literal (Literal.number "7")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "cnt") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "cnt"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sink",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "v", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sinkI",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "v", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "v"))]) }), ContractItem.modifierDecl
  { name := "mm"
    params := [{ name := some "v", ty := Ty.uint 8, location := none }]
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitNamed",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EMix") [Arg.named "x" (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), Arg.named "y" (Expr.literal (Literal.number "1"))]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "revNamed",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.revertCall (Expr.call (Expr.ident "Err") [Arg.named "d" (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "arrLit",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "t", ty := Ty.array (Ty.uint 8) (some 2), location := some DataLocation.memory }] (some (Expr.array [Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"), Expr.literal (Literal.number "1")])), Stmt.returnValues (some (Expr.index (Expr.ident "t") (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structCtor",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["P"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["P"] }))) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "p") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "structNamed",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["P"] }), location := some DataLocation.memory }] (some (Expr.call (Expr.typeName (Ty.user ({ segments := ["P"] }))) [Arg.named "v" (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "p") "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "newSize",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "t", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.uint 256) (none)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))])), Stmt.returnValues (some (Expr.member (Expr.ident "t") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "tupleAssign",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.uint 8, location := none }] none, Stmt.varDecl [{ name := some "y", ty := Ty.uint 8, location := none }] none, Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "x"), TupleItem.value (Expr.ident "y")]) AssignOp.assign (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), TupleItem.value (Expr.ident "b")])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.binary BinaryOp.sub (Expr.ident "y") (Expr.ident "y"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "tupleDecl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }, { name := some "d", ty := Ty.uint 8, location := none }] (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), TupleItem.value (Expr.ident "b")])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "c") (Expr.binary BinaryOp.sub (Expr.ident "d") (Expr.ident "d"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "extArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "this") "sink") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "tryArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.tryCatchReturns (Expr.call (Expr.member (Expr.ident "this") "sink") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]) [{ name := some "v", ty := Ty.uint 8, location := none }] (Stmt.block [Stmt.returnValues (some (Expr.ident "v"))]) [CatchClause.clause none [] (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "99")))])]]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "libArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "idm") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "usingArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "f") [Arg.positional (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "g") [Arg.positional (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "h") [Arg.positional (Expr.ident "a")])])]) (Expr.binary BinaryOp.sub (Expr.ident "b") (Expr.ident "b"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "fnPtrArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "fp", ty := Ty.functionWithLocations [Ty.uint 8] [none] [Ty.uint 8] [none] StateMutability.pure Visibility.internal_, location := none }] (some (Expr.ident "sinkI")), Stmt.returnValues (some (Expr.call (Expr.ident "fp") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "modArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["mm"] }, args := [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))], hasArgList := true }],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "addmodArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.literal (Literal.number "7"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr8") "push") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]), Stmt.returnValues (some (Expr.member (Expr.ident "arr8") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "idxNested",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.index (Expr.ident "arr") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "forInit",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s_", ty := Ty.uint 8, location := none }] (some (Expr.literal (Literal.number "0"))), Stmt.forLoop (some (Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }] (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))))) (some (Expr.binary BinaryOp.gt (Expr.ident "c") (Expr.literal (Literal.number "0")))) (some (Expr.unary UnaryOp.postDecrement (Expr.ident "c"))) (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "s_") AssignOp.assign (Expr.literal (Literal.number "1"))), Stmt.break]), Stmt.returnValues (some (Expr.ident "s_"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "delMapKey",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.index (Expr.ident "m8") (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emitIndexed",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EI") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "unchkVd",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }] (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b"))), Stmt.returnValues (some (Expr.ident "c"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "unchkTuple",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.unchecked (Stmt.block [Stmt.varDecl [{ name := some "c", ty := Ty.uint 8, location := none }, { name := some "d", ty := Ty.uint 8, location := none }] (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")), TupleItem.value (Expr.ident "b")])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "c") (Expr.binary BinaryOp.sub (Expr.ident "d") (Expr.ident "d"))))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h196",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g196",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "y", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.mul (Expr.ident "y") (Expr.literal (Literal.number "2"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f196",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "z", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "z") (Expr.literal (Literal.number "5"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chain3",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "f196") [Arg.positional (Expr.call (Expr.ident "g196") [Arg.positional (Expr.call (Expr.ident "h196") [Arg.positional (Expr.ident "x")])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chain4",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "f196") [Arg.positional (Expr.call (Expr.ident "f196") [Arg.positional (Expr.call (Expr.ident "g196") [Arg.positional (Expr.call (Expr.ident "h196") [Arg.positional (Expr.ident "x")])])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chain3lib",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "f") [Arg.positional (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "g") [Arg.positional (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L8"] }))) "h") [Arg.positional (Expr.ident "x")])])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chain3vd",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "r", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "f196") [Arg.positional (Expr.call (Expr.ident "g196") [Arg.positional (Expr.call (Expr.ident "h196") [Arg.positional (Expr.ident "x")])])])), Stmt.returnValues (some (Expr.ident "r"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chain3emit",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "EI") [Arg.positional (Expr.call (Expr.ident "f196") [Arg.positional (Expr.call (Expr.ident "g196") [Arg.positional (Expr.call (Expr.ident "h196") [Arg.positional (Expr.ident "x")])])])]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "emit2Idx",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "E2I") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.call (Expr.ident "bump") [])]), Stmt.returnValues (some (Expr.ident "cnt"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end LoweringUnifyAuditWitness
end SolcAstImport
end Solidity
end SolidCore

/-!
WS1 Stage 1b — the SYSTEMATIC env-audit beyond #201 (probe battery
`tests/forge-harness/lowering-unify-audit`, 32 real-EVM Forge tests, all PASS
on pinned solc 0.8.35). Divergent-before-fix positions pinned below:

  H1. `new uint256[](a + b)` allocation size (model RETURNED 300)
  H2. external-call argument `this.sink(a + b)` (model: callee-side decode
      revert instead of the caller-side Panic 0x11)
  H3. `try this.sink(a + b)` — the panic fires during ARGUMENT evaluation in
      the caller and is NOT caught (model previously took the catch arm)
  H4. `addmod(a + b, 1, 7)` (model returned (300+1)%7 = 0)
  H5. nested wide index key `arr[arr[a + b]]` (model Panicked 0x32 OOB
      instead of 0x11 at the inner narrow key)
  H6. inline array literal `uint8[2] memory t = [a + b, 1]` — OVER-REJECT
      (the whole contract failed to lower), now lowers and Panics 0x11
      (safe values return 7)

Green controls: named emit/revert args, struct ctor (positional + named),
tuple assign/decl, lib/fn-pointer/modifier args, push, for-init, delete map
key, indexed emit, unchecked wrap-width (44), the #196 chain values
(chain3/chain4 = 27/32 — correct: those shapes lower through the boundary
call path, not the colliding hoister), and the two-phase indexed emit
schedule (E2I topics x=2, y=1).
-/
namespace SolidCore
namespace Solidity
namespace Witness
namespace LoweringUnifyAudit

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev U := SolidCore.Solidity.SolcAstImport.LoweringUnifyAuditWitness.importedSourceUnit

def unitAccepted : Bool :=
  SolidCore.Solidity.SolcAstImport.LoweringUnifyAuditWitness.importedContractAccepted

def callP (fn : Name) (args : List Value) : Except TypeError CallResult :=
  CheckedInput.callContract 900 U "AuditProbe" (CallTarget.name fn)
    State.empty args

def panics17 (fn : Name) (args : List Value) : Bool :=
  match callP fn args with
  | Except.ok (CallResult.reverted _ (RevertData.panic code)) => wordEq code 0x11
  | _ => false

def retWord (fn : Name) (args : List Value) (expected : Word) : Bool :=
  match callP fn args with
  | Except.ok (CallResult.returned _ [value]) =>
      match Value.asWord? value with
      | some w => wordEq w expected
      | none => false
  | _ => false

def ab : List Value := [Value.word 200, Value.word 100]
def safe : List Value := [Value.word 3, Value.word 4]
def x10 : List Value := [Value.word 10, Value.word 0]

-- H1..H6 (divergent before this branch)
#guard unitAccepted
#guard panics17 "newSize" ab
#guard panics17 "extArg" ab
#guard panics17 "tryArg" ab
#guard panics17 "addmodArg" ab
#guard panics17 "idxNested" ab
#guard panics17 "arrLit" ab
-- controls that must stay green
#guard panics17 "emitNamed" ab
#guard panics17 "revNamed" ab
#guard panics17 "structCtor" ab
#guard panics17 "structNamed" ab
#guard panics17 "tupleAssign" ab
#guard panics17 "tupleDecl" ab
#guard panics17 "libArg" ab
#guard panics17 "fnPtrArg" ab
#guard panics17 "modArg" ab
#guard panics17 "pushArg" ab
#guard panics17 "forInit" ab
#guard panics17 "delMapKey" ab
#guard panics17 "emitIndexed" ab
-- safe / wrap-width values (exact real-EVM results)
#guard retWord "unchkVd" ab 44
#guard retWord "unchkTuple" ab 44
#guard retWord "tupleDecl" safe 7
#guard retWord "arrLit" safe 7
#guard retWord "newSize" safe 7
#guard retWord "libArg" safe 7
#guard retWord "usingArg" x10 27
-- #196 chain shapes (correct values; the depth-suffixed gensym keeps them)
#guard retWord "chain3" [Value.word 10] 27
#guard retWord "chain4" [Value.word 10] 32
#guard retWord "chain3lib" [Value.word 10] 27
#guard retWord "chain3vd" [Value.word 10] 27

-- chain3emit: EI topic value 27; emit2Idx: two-phase indexed schedule x=2,y=1
def chain3emitTopic27 : Bool :=
  match callP "chain3emit" [Value.word 10] with
  | Except.ok (CallResult.returned st _) =>
      match st.events with
      | [event] =>
          event.topics == [Keccak.digestWord "EI(uint8)", 27]
      | _ => false
  | _ => false

def emit2IdxTwoPhase : Bool :=
  match callP "emit2Idx" [] with
  | Except.ok (CallResult.returned st [Value.word 2]) =>
      match st.events with
      | [event] =>
          event.topics == [Keccak.digestWord "E2I(uint256,uint256)", 2, 1]
      | _ => false
  | _ => false

#guard chain3emitTopic27
#guard emit2IdxTwoPhase

end LoweringUnifyAudit
end Witness
end Solidity
end SolidCore

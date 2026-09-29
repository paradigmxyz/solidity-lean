import SolidCore.Witness.Prepared
import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
import SolidCore.Witness.Interface

set_option maxHeartbeats 8000000

/-!
R3 VALUE-TYPING witness (rearchitecture phase 2): pins for the three bug
families rooted in type-erased runtime values, plus semantic-preservation
controls.

* #175 class — bytesN indexing is now INTRINSIC: the runtime value carries
  its width (`Value.fixedBytes size w`), so a site shape the lowering cannot
  statically type — `(cond ? a : b)[i]` — extracts the byte (previously
  Panic 0x00) and still Panics 0x32 out of bounds. Controls pin bytesN
  `&`/`<<`/`>>`/`~`/`==`/`uint32(...)`/`abi.encode` word-for-word.
* #188 — an internal/library fn returning a storage pointer from an
  INDEXED/MEMBER path (`return arr[i]` / `m[k]` / `o.inner`) re-points the
  caller's alias: the return-assignment lowering now emits
  `storageAliasAssign(From)Path` for path RHS, the ANF hoist temp of a
  storage-returning call is a STORAGE alias local, and
  `coerceLike?` re-points a storage-ref value meeting a ref template.
  Write-through values (42/77/88/55/42/99 + library 42/42) anvil-pinned
  (Forge lane `storage-ref-path-return`).
* #192 — `keccak256`/`sha256`/`erc7201`/`abi.encode*`/`concat` of a bare
  storage `bytes`/`string`/array materialize the storage value at the
  boundary (`materializeStorageValueUseCore` in the lowering +
  `Runtime.materializeForValueUse` at the eval arms). Hashes pinned to
  `cast keccak` ground truth (Forge lane `storage-value-boundary`).

Contract ASTs below are rendered from real solc 0.8.35 source AST by
`scripts/solc_ast_to_lean_source.py` (sources in the paired Forge lanes /
`audit-r3` probes).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace ValueTyping

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

namespace V175

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/audit-r3/P175.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "P175"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "sv",
    ty := Ty.bytesN 32,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "0x1112131415161718192021222324252627282930313233343536373839404142")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t1",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "i", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.bytesN 32, location := none }] (some (Expr.literal (Literal.number "0x1112131415161718192021222324252627282930313233343536373839404142"))), Stmt.returnValues (some (Expr.index (Expr.ident "a") (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t2",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.index (Expr.ident "x") (Expr.literal (Literal.number "2"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t3",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0xaa11"))])])), Stmt.varDecl [{ name := some "b", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0xbb22"))])])), Stmt.returnValues (some (Expr.index (Expr.ternary (Expr.ident "c") (Expr.ident "a") (Expr.ident "b")) (Expr.literal (Literal.number "31"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t4",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "sv") (Expr.literal (Literal.number "3"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t5",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "p", ty := Ty.bytesN 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "p") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t6",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "1"))])])])), Stmt.returnValues (some (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "0"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "oob",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "4"))), Stmt.returnValues (some (Expr.index (Expr.ident "x") (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c1",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.varDecl [{ name := some "y", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.binary BinaryOp.eq (Expr.ident "x") (Expr.ident "y")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c2",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.binary BinaryOp.bitAnd (Expr.ident "x") (Expr.literal (Literal.number "0xff00ff00"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c3",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.binary BinaryOp.shl (Expr.ident "x") (Expr.literal (Literal.number "8"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c4",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.binary BinaryOp.shr (Expr.ident "x") (Expr.literal (Literal.number "8"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c5",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.ident "x")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c6",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "x")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c7",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 4, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.bytesN 4, location := none }] (some (Expr.literal (Literal.number "0x11223344"))), Stmt.returnValues (some (Expr.unary UnaryOp.bitNot (Expr.ident "x")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "c8",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 1, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0xaa11"))])])), Stmt.varDecl [{ name := some "b", ty := Ty.bytesN 32, location := none }] (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0xbb22"))])])), Stmt.varDecl [{ name := some "z", ty := Ty.bytesN 32, location := none }] (some (Expr.ternary (Expr.ident "c") (Expr.ident "a") (Expr.ident "b"))), Stmt.returnValues (some (Expr.index (Expr.ident "z") (Expr.literal (Literal.number "30"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end V175

namespace V188

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/audit-r3/P188.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "P188"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.structDecl
  { name := "O",
    fields := [{ name := "inner", ty := Ty.user ({ segments := ["S"] }) }] }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.user ({ segments := ["S"] })) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.user ({ segments := ["S"] })),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "mu",
    ty := Ty.mapping (Ty.uint 256) (Ty.array (Ty.uint 256) (none)),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "u",
    ty := Ty.array (Ty.uint 256) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "o",
    ty := Ty.user ({ segments := ["O"] }),
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
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.literal (Literal.number "2"))])]), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.literal (Literal.number "3")), Arg.positional (Expr.literal (Literal.number "4"))])]), Stmt.expr (Expr.call (Expr.member (Expr.ident "u") "push") [Arg.positional (Expr.literal (Literal.number "10"))]), Stmt.expr (Expr.call (Expr.member (Expr.ident "u") "push") [Arg.positional (Expr.literal (Literal.number "20"))]), Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "mu") (Expr.literal (Literal.number "5"))) "push") [Arg.positional (Expr.literal (Literal.number "30"))]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "7"))) AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.literal (Literal.number "5")), Arg.positional (Expr.literal (Literal.number "6"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refS",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "i", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "arr") (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refM",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "k", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.ident "k")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refU",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "mu") (Expr.literal (Literal.number "5"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refInner",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.member (Expr.ident "o") "inner"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "refWhole",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.user ({ segments := ["S"] })) (none), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "arr"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t1",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refS") [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "a") AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t2",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.call (Expr.ident "refS") [Arg.positional (Expr.literal (Literal.number "0"))]) "b") AssignOp.assign (Expr.literal (Literal.number "77"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) "b"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t3",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refM") [Arg.positional (Expr.literal (Literal.number "7"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "b") AssignOp.assign (Expr.literal (Literal.number "88"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "7"))) "b"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t4",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "p", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refU") [])), Stmt.expr (Expr.call (Expr.member (Expr.ident "p") "push") [Arg.positional (Expr.literal (Literal.number "55"))]), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "mu") (Expr.literal (Literal.number "5"))) (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t5",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refInner") [])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "a") AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.returnValues (some (Expr.member (Expr.member (Expr.ident "o") "inner") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t6",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "p", ty := Ty.array (Ty.user ({ segments := ["S"] })) (none), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refWhole") [])), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "p") (Expr.literal (Literal.number "0"))) "a") AssignOp.assign (Expr.literal (Literal.number "99"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) "a"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end V188

namespace V188L

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/audit-r3/P188L.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "Lib"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "at",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "self", ty := Ty.array (Ty.user ({ segments := ["S"] })) (none), location := some DataLocation.storage }, { name := some "i", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "self") (Expr.ident "i")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "self", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.ident "self") "a") AssignOp.assign (Expr.literal (Literal.number "42")))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "P188L"
  abstract := false
  bases := []
  items := [(ContractItem.usingDecl
  { library := { segments := ["Lib"] },
    functions := [],
    target := some (Ty.array (Ty.user ({ segments := ["Lib", "S"] })) (none)),
    global := false }), (ContractItem.usingDecl
  { library := { segments := ["Lib"] },
    functions := [],
    target := some (Ty.user ({ segments := ["Lib", "S"] })),
    global := false }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.user ({ segments := ["Lib", "S"] })) (none),
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
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.user ({ segments := ["Lib", "S"] }))) [Arg.positional (Expr.literal (Literal.number "1")), Arg.positional (Expr.literal (Literal.number "2"))])]), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.user ({ segments := ["Lib", "S"] }))) [Arg.positional (Expr.literal (Literal.number "3")), Arg.positional (Expr.literal (Literal.number "4"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t7",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["Lib", "S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.member (Expr.ident "arr") "at") [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "a") AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t8",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.call (Expr.member (Expr.ident "arr") "at") [Arg.positional (Expr.literal (Literal.number "0"))]) "bump") []), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "0"))) "a"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end V188L

namespace V192

def importedSourceName : String := "/private/tmp/claude-502/-Users-dan-Projects-solid-core-spine/a31e5b4d-dfd9-4ad6-82fd-d3eba32b9252/scratchpad/audit-r3/P192.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "P192"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "stored5",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "stored31",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "stored32",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "stored33",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "sstr",
    ty := Ty.string,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "arr",
    ty := Ty.array (Ty.uint 256) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.structDecl
  { name := "Box",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "inner", ty := Ty.bytes }] }), (ContractItem.stateVar
  { name := "box",
    ty := Ty.user ({ segments := ["Box"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "mb",
    ty := Ty.mapping (Ty.uint 256) (Ty.bytes),
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
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "stored5") AssignOp.assign (Expr.literal (Literal.hexString "1122334455"))), Stmt.expr (Expr.assign (Expr.ident "stored31") AssignOp.assign (Expr.literal (Literal.hexString "01020304050607080910111213141516171819202122232425262728293031"))), Stmt.expr (Expr.assign (Expr.ident "stored32") AssignOp.assign (Expr.literal (Literal.hexString "0102030405060708091011121314151617181920212223242526272829303132"))), Stmt.expr (Expr.assign (Expr.ident "stored33") AssignOp.assign (Expr.literal (Literal.hexString "010203040506070809101112131415161718192021222324252627282930313233"))), Stmt.expr (Expr.assign (Expr.ident "sstr") AssignOp.assign (Expr.literal (Literal.string "hello"))), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.literal (Literal.number "7"))]), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") [Arg.positional (Expr.literal (Literal.number "9"))]), Stmt.expr (Expr.assign (Expr.member (Expr.ident "box") "a") AssignOp.assign (Expr.literal (Literal.number "1"))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "box") "inner") AssignOp.assign (Expr.literal (Literal.hexString "aabbcc"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "mb") (Expr.literal (Literal.number "3"))) AssignOp.assign (Expr.literal (Literal.hexString "ddeeff")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h5",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.ident "stored5")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h31",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.ident "stored31")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h32",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.ident "stored32")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h33",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.ident "stored33")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hs",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "sha256") [Arg.positional (Expr.ident "stored5")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "henc",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "arr")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hencp",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.ident "arr")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hbox",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.member (Expr.ident "box") "inner")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hmap",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.index (Expr.ident "mb") (Expr.literal (Literal.number "3")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hmem",
    visibility := some Visibility.public_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "m", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.hexString "1122334455"))), Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.ident "m")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hstr",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.typeName (Ty.bytes)) [Arg.positional (Expr.ident "sstr")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "hpstored",
    visibility := some Visibility.public_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.ident "stored5")])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end V192

private def preparedP175 : Prepared.Contract :=
  CheckedInput.contract V175.importedSourceUnit "P175"

private def preparedP188 : Prepared.Contract :=
  CheckedInput.contract V188.importedSourceUnit "P188"

private def preparedP188L : Prepared.Contract :=
  CheckedInput.contract V188L.importedSourceUnit "P188L"

private def preparedP192 : Prepared.Contract :=
  CheckedInput.contract V192.importedSourceUnit "P192"

-- Constructor-initialized state for a generated one-contract unit.
private def ctorState (contract : Prepared.Contract) : State :=
  match Prepared.construct 512 contract State.empty [] with
  | Except.ok (CallResult.returned st _) => st
  | _ => State.empty

-- Whole-program call whose single result word (tag-agnostic) matches.
private def callWordIs (contract : Prepared.Contract)
    (st : State) (fn : Name) (args : List Value) (expected : Word) : Bool :=
  match
    Prepared.call 512 contract
      (CallTarget.name fn) st args with
  | Except.ok (CallResult.returned _ [v]) => v.asWord? == some expected
  | _ => false

private def callPanicIs (contract : Prepared.Contract)
    (st : State) (fn : Name) (args : List Value) (code : Word) : Bool :=
  match
    Prepared.call 512 contract
      (CallTarget.name fn) st args with
  | Except.ok (CallResult.reverted _ (RevertData.panic c)) => c == code
  | _ => false

-- ### #175 class: intrinsic bytesN indexing ------------------------------

private def st175 : State := ctorState preparedP175

-- `(cond ? a : b)[31]` — a base shape with NO static fixed-bytes routing:
-- dispatch happens on the width-tagged VALUE. Was Panic 0x00.
-- Ternary through a LOCAL (control: worked before, unchanged).
-- bytes4/param/local/state/keccak-result indexing + OOB Panic 0x32.

-- SEMANTIC PRESERVATION controls (raw words identical to pre-R3 runs):

-- ### #188: storage-ref returns from indexed/member paths -----------------

private def st188 : State := ctorState preparedP188


private def st188L : State := ctorState preparedP188L


-- ### #192: storage materialization at value boundaries -------------------

private def st192 : State := ctorState preparedP192

-- keccak256(storedN) for byte-array lengths 5/31/32/33 — `cast keccak` pins.
-- keccak256(abi.encode(storageArr)) / keccak256(abi.encodePacked(storageArr)).
-- Nested storage-bytes member + mapping-value bytes (already worked = controls).
-- CONTROLS (worked before, must be unchanged): memory keccak, bytes(sstr),
-- encodePacked(storedBytes).

-- sha256(storedBytes): lowers + runs; the precompile CALLDATA is exactly the
-- materialized storage bytes (responder keyed on it) and the canned word
-- round-trips as the result.
def shaStoredMatches : Except TypeError Bool := do
  let program ← CheckedInput.program V192.importedSourceUnit
  let contract ← CheckedProgram.contract program "P192"
  let result ←
    CheckedContract.callFunctionWithContextFailOpen 64
      (responderOfResults
        [ Executable.Examples.successfulPrecompileWordCall
            SolidCore.Solidity.Shared.Precompile.Kind.sha256
            [0x11, 0x22, 0x33, 0x44, 0x55] 0xabcd ]
        [])
      contract "hs" contract.core.context st192 []
  match result with
  | CallResult.returned _ [v] => Except.ok (v.asWord? == some 0xabcd)
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false


#eval Prepared.assertChecks [
  ("ValueTyping:750", (
    callWordIs preparedP175 st175 "t3" [Value.word 1] 0x11
  )),
  ("ValueTyping:751", (
    callWordIs preparedP175 st175 "t3" [Value.word 0] 0x22
  )),
  ("ValueTyping:753", (
    callWordIs preparedP175 st175 "c8" [Value.word 1] 0xaa
  )),
  ("ValueTyping:755", (
    callWordIs preparedP175 st175 "t2" [] 0x33
  )),
  ("ValueTyping:756", (
    callWordIs preparedP175 st175 "t4" [] 0x14
  )),
  ("ValueTyping:757", (
    callWordIs preparedP175 st175 "t1" [Value.word 3] 0x14
  )),
  ("ValueTyping:759", (
    callWordIs preparedP175 st175 "t5"
  [Value.word 0x1122334455667788] 0x22
  )),
  ("ValueTyping:760", (
    callWordIs preparedP175 st175 "t6" [] 0xb1
  )),
  ("ValueTyping:761", (
    callPanicIs preparedP175 st175 "oob" [] 0x32
  )),
  ("ValueTyping:764", (
    callWordIs preparedP175 st175 "c1" [] 1
  )),
  ("ValueTyping:765", (
    callWordIs preparedP175 st175 "c2" [] 0x11003300
  )),
  ("ValueTyping:766", (
    callWordIs preparedP175 st175 "c3" [] 0x22334400
  )),
  ("ValueTyping:767", (
    callWordIs preparedP175 st175 "c4" [] 0x00112233
  )),
  ("ValueTyping:768", (
    callWordIs preparedP175 st175 "c5" [] 0x11223344
  )),
  ("ValueTyping:770", (
    callWordIs preparedP175 st175 "c6" []
  0x4508e625236b765f449ba1c8acea2c5fc6d35a12e3efb36fb267e0225b1069a5
  )),
  ("ValueTyping:771", (
    callWordIs preparedP175 st175 "c7" [] 0xeeddccbb
  )),
  ("ValueTyping:777", (
    callWordIs preparedP188 st188 "t1" [] 42  -- arr[i] elem
  )),
  ("ValueTyping:778", (
    callWordIs preparedP188 st188 "t2" [] 77  -- call-as-lvalue base
  )),
  ("ValueTyping:779", (
    callWordIs preparedP188 st188 "t3" [] 88  -- mapping value
  )),
  ("ValueTyping:780", (
    callWordIs preparedP188 st188 "t4" [] 55  -- uint[] via mapping, push
  )),
  ("ValueTyping:781", (
    callWordIs preparedP188 st188 "t5" [] 42  -- nested member o.inner
  )),
  ("ValueTyping:782", (
    callWordIs preparedP188 st188 "t6" [] 99  -- CONTROL whole-var return
  )),
  ("ValueTyping:786", (
    callWordIs preparedP188L st188L "t7" [] 42 -- using-for boundary
  )),
  ("ValueTyping:787", (
    callWordIs preparedP188L st188L "t8" [] 42 -- lib receiver write-through
  )),
  ("ValueTyping:795", (
    callWordIs preparedP192 st192 "h5" []
  0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e
  )),
  ("ValueTyping:797", (
    callWordIs preparedP192 st192 "h31" []
  0x36299799c00f1e584433782420b22c96b9df65c02cd04f2d48f30d46be856ec5
  )),
  ("ValueTyping:799", (
    callWordIs preparedP192 st192 "h32" []
  0x2cfe17dc69e953b28d77cdb7cdc86ce378dfe1e846f4be9cbe9dfb18efa5dfb5
  )),
  ("ValueTyping:801", (
    callWordIs preparedP192 st192 "h33" []
  0xd529e5852759a362ba426afed12b33dfb83d9029bcaa3cdd3e865dc904828fcb
  )),
  ("ValueTyping:804", (
    callWordIs preparedP192 st192 "henc" []
  0x69f3a7d692ca055c9f54ae9803e527761c5593a4715f41502d94fbcadbbffbe7
  )),
  ("ValueTyping:806", (
    callWordIs preparedP192 st192 "hencp" []
  0xae6299332bcd708cd60e3a8defa55de28078a50a4cf2b3de3a546253240ff9e1
  )),
  ("ValueTyping:809", (
    callWordIs preparedP192 st192 "hbox" []
  0xccad3f5300e77cf5347e3c6200a08bd8cf71f94a0b347bcb39486b17b88a8a71
  )),
  ("ValueTyping:811", (
    callWordIs preparedP192 st192 "hmap" []
  0x6619b407baede597919db7245e6662bd28bed07dad7580f0769d0e94bd0c16fe
  )),
  ("ValueTyping:815", (
    callWordIs preparedP192 st192 "hmem" []
  0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e
  )),
  ("ValueTyping:817", (
    callWordIs preparedP192 st192 "hstr" []
  0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8
  )),
  ("ValueTyping:819", (
    callWordIs preparedP192 st192 "hpstored" []
  0x6ccdf593017c9d38b36c1cb00572feae81abc15173860a4e0904a6c45d3b086e
  )),
  ("ValueTyping:843", (
    V175.importedContractAccepted
  )),
  ("ValueTyping:844", (
    V188.importedContractAccepted
  )),
  ("ValueTyping:845", (
    V188L.importedContractAccepted
  )),
  ("ValueTyping:846", (
    V192.importedContractAccepted
  )),
  ("ValueTyping:847", (
    isOkTrue shaStoredMatches
  ))
]
end ValueTyping
end Witness
end Solidity
end SolidCore

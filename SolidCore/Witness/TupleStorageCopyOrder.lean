import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-STORAGE-COPY-ORDER: a tuple component that names a storage array,
struct, `bytes` or `string` is evaluated to a storage reference and copied to
memory only when the whole tuple is converted to its target types, after the
later components ran. So in `return` (`pairV` below) and in a tuple
assignment, a later component's internal call that pushes to the same storage
is visible in the copy. A value read such as `v.length` is taken where it
stands, before the later call.

```solidity
contract C {
    struct S { uint8[] a; uint8 k; }
    uint8[] v;
    S s;
    bytes b;

    function pushV() internal returns (uint8) { v.push(7); return 1; }
    function pushS() internal returns (uint8) { s.a.push(7); return 1; }
    function pushB() internal returns (uint8) { b.push(0x07); return 1; }

    function pairV() internal returns (uint8[] memory, uint8) { return (v, pushV()); }
    function pairS() internal returns (S memory, uint8) { return (s, pushS()); }
    function pairM() internal returns (uint8[] memory, uint8) { return (s.a, pushS()); }
    function pairB() internal returns (bytes memory, uint8) { return (b, pushB()); }
    function pairLen() internal returns (uint256, uint8) { return (v.length, pushV()); }

    function ret() external returns (uint256) {
        delete v;
        (uint8[] memory c, uint8 m) = pairV();
        return c.length + m;
    }

    function retStruct() external returns (uint256) {
        delete s;
        (S memory c, uint8 m) = pairS();
        return c.a.length + m;
    }

    function retMember() external returns (uint256) {
        delete s;
        (uint8[] memory c, uint8 m) = pairM();
        return c.length + m;
    }

    function retBytes() external returns (uint256) {
        delete b;
        (bytes memory c, uint8 m) = pairB();
        return c.length + m;
    }

    function assign() external returns (uint256) {
        delete v;
        uint8[] memory c;
        uint8 m;
        (c, m) = (v, pushV());
        return c.length + m;
    }

    function len() external returns (uint256) {
        delete v;
        (uint256 c, uint8 m) = pairLen();
        return c + m;
    }
}
```

Ground truth, solc 0.8.35 legacy and via-IR on the EVM, from empty storage:
`ret`, `retStruct`, `retMember`, `retBytes` and `assign` return 2 (the copy has
the pushed element), `len` returns 1.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleStorageCopyOrder

def importedSourceName : String := "tuple-storage-copy-order.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.array (Ty.uint 8) (none) }, { name := "k", ty := Ty.uint 8 }] }), (ContractItem.stateVar
  { name := "v",
    ty := Ty.array (Ty.uint 8) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "s",
    ty := Ty.user ({ segments := ["S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "b",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushV",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "v") "push") [Arg.positional (Expr.literal (Literal.number "7"))]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushS",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.member (Expr.ident "s") "a") "push") [Arg.positional (Expr.literal (Literal.number "7"))]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pushB",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "b") "push") [Arg.positional (Expr.literal (Literal.number "0x07"))]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pairV",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.uint 8) (none), location := some DataLocation.memory }, { name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "v"), TupleItem.value (Expr.call (Expr.ident "pushV") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pairS",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }, { name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "s"), TupleItem.value (Expr.call (Expr.ident "pushS") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pairM",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.uint 8) (none), location := some DataLocation.memory }, { name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.ident "s") "a"), TupleItem.value (Expr.call (Expr.ident "pushS") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pairB",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }, { name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.ident "b"), TupleItem.value (Expr.call (Expr.ident "pushB") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pairLen",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }, { name := none, ty := Ty.uint 8, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.member (Expr.ident "v") "length"), TupleItem.value (Expr.call (Expr.ident "pushV") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "ret",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "v")), Stmt.varDecl [{ name := some "c", ty := Ty.array (Ty.uint 8) (none), location := some DataLocation.memory }, { name := some "m", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "pairV") [])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.member (Expr.ident "c") "length") (Expr.ident "m")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "retStruct",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "s")), Stmt.varDecl [{ name := some "c", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.memory }, { name := some "m", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "pairS") [])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.member (Expr.member (Expr.ident "c") "a") "length") (Expr.ident "m")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "retMember",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "s")), Stmt.varDecl [{ name := some "c", ty := Ty.array (Ty.uint 8) (none), location := some DataLocation.memory }, { name := some "m", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "pairM") [])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.member (Expr.ident "c") "length") (Expr.ident "m")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "retBytes",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "b")), Stmt.varDecl [{ name := some "c", ty := Ty.bytes, location := some DataLocation.memory }, { name := some "m", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "pairB") [])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.member (Expr.ident "c") "length") (Expr.ident "m")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assign",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "v")), Stmt.varDecl [{ name := some "c", ty := Ty.array (Ty.uint 8) (none), location := some DataLocation.memory }] none, Stmt.varDecl [{ name := some "m", ty := Ty.uint 8, location := none }] none, Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "c"), TupleItem.value (Expr.ident "m")]) AssignOp.assign (Expr.tuple [TupleItem.value (Expr.ident "v"), TupleItem.value (Expr.call (Expr.ident "pushV") [])])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.member (Expr.ident "c") "length") (Expr.ident "m")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "len",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "v")), Stmt.varDecl [{ name := some "c", ty := Ty.uint 256, location := none }, { name := some "m", ty := Ty.uint 8, location := none }] (some (Expr.call (Expr.ident "pairLen") [])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "c") (Expr.ident "m")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleStorageCopyOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleStorageCopyOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev Fam := SolidCore.Solidity.SolcAstImport.TupleStorageCopyOrder.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.TupleStorageCopyOrder.importedContractAccepted

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

-- `(v, pushV())` returned from an internal function: the copy has the push.
def ret_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "ret" State.empty [] 2

-- The same for a storage struct whose array member the call pushes to.
def retStruct_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "retStruct" State.empty [] 2

-- ... for a member path into that struct.
def retMember_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "retMember" State.empty [] 2

-- ... for a storage `bytes`.
def retBytes_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "retBytes" State.empty [] 2

-- ... and for a tuple assignment to memory locals.
def assign_is_2 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "assign" State.empty [] 2

-- Control: `v.length` is a value, read before the later call.
def len_is_1 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 Fam "len" State.empty [] 1

#guard accepted
#guard isOkTrue ret_is_2
#guard isOkTrue retStruct_is_2
#guard isOkTrue retMember_is_2
#guard isOkTrue retBytes_is_2
#guard isOkTrue assign_is_2
#guard isOkTrue len_is_1

end TupleStorageCopyOrder
end Witness
end Solidity
end SolidCore

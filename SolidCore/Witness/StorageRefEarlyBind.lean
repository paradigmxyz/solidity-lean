import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
WS2 STORAGE-REF EARLY BINDING (#146 / #177): a storage pointer captures its
CONCRETE slot at the binding access (bounds check runs there, once), then
dereferences raw with no length recheck — matching solc/EVM.

Real-EVM Forge ground truth: `tests/forge-harness/storage-ref-early-bind`
(9 tests PASS on pinned solc 0.8.35 + the EVM):

  t1 pop-then-deref            -> 0     (the #146/#177 fix; was Panic 0x32)
  t2 pop-then-push-then-deref  -> 9     (control, already matched)
  t3(+t3code) bind-time OOB    -> Panic 0x32 (unchanged; raised AT bind)
  t4 live mutation via arr[1]  -> 33    (pointer reads live slot data)
  t5 mapping-value ref write   -> 88    (control)
  t6 dangling write-then-read  -> 5     (write lands in the freed slot)
  t7/t8/t9 #188 write-through re-pins (indexed/mapping/uint[] storage-ref
  RETURNS: 42 / 88 / 55)

`#eval`-confirmed booleans pinned with `#guard` (the project avoids
`native_decide`).
-/


namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StorageRefEarlyBindWitness

def importedSourceName : String :=
  "tests/forge-harness/storage-ref-early-bind/src/StorageRefEarlyBind.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "StorageRefEarlyBindTarget"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.uint 256 }, { name := "b", ty := Ty.uint 256 }] }), (ContractItem.stateVar
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
  { name := "nums",
    ty := Ty.array (Ty.uint 256) (none),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t1",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a") AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "pop") []), Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t2",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a") AssignOp.assign (Expr.literal (Literal.number "7"))), Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "pop") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a") AssignOp.assign (Expr.literal (Literal.number "9"))), Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t3",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "2")))), Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t3code",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.tryCatchReturns (Expr.call (Expr.member (Expr.ident "this") "t3") []) [{ name := none, ty := Ty.uint 256, location := none }] (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) [CatchClause.clause (some "Panic") [{ name := some "code", ty := Ty.uint 256, location := none }] (Stmt.block [Stmt.returnValues (some (Expr.ident "code"))])]]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t4",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.assign (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a") AssignOp.assign (Expr.literal (Literal.number "33"))), Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t5",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "3")))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "p") "a") AssignOp.assign (Expr.literal (Literal.number "88"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "3"))) "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t6",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.varDecl [{ name := some "p", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "pop") []), Stmt.expr (Expr.assign (Expr.member (Expr.ident "p") "a") AssignOp.assign (Expr.literal (Literal.number "5"))), Stmt.returnValues (some (Expr.member (Expr.ident "p") "a"))]) }), (ContractItem.function
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
    name := some "refN",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.storage }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "nums"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t7",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.expr (Expr.call (Expr.member (Expr.ident "arr") "push") []), Stmt.varDecl [{ name := some "s", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refS") [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "s") "a") AssignOp.assign (Expr.literal (Literal.number "42"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "arr") (Expr.literal (Literal.number "1"))) "a"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t8",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "q", ty := Ty.user ({ segments := ["S"] }), location := some DataLocation.storage }] (some (Expr.call (Expr.ident "refM") [Arg.positional (Expr.literal (Literal.number "5"))])), Stmt.expr (Expr.assign (Expr.member (Expr.ident "q") "b") AssignOp.assign (Expr.literal (Literal.number "88"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "5"))) "b"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "t9",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.call (Expr.ident "refN") []) "push") [Arg.positional (Expr.literal (Literal.number "55"))]), Stmt.returnValues (some (Expr.index (Expr.ident "nums") (Expr.literal (Literal.number "0"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StorageRefEarlyBindWitness
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StorageRefEarlyBind

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C :=
  SolidCore.Solidity.SolcAstImport.StorageRefEarlyBindWitness.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StorageRefEarlyBindWitness.importedContractAccepted

-- The #146/#177 fix: dereferencing a pointer bound to arr[1] AFTER arr.pop()
-- reads the freed (pop-zeroed) slot -> 0 (was Panic 0x32).
def t1_pop_then_deref_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t1" State.empty [] 0
-- Control: pop-then-push-then-deref (length restored) still 9.
def t2_pop_push_deref_is_9 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t2" State.empty [] 9
-- Out-of-bounds at the BINDING access still Panics 0x32 (now raised at the
-- bind itself, as solc does).
def t3_bind_oob_panics_0x32 : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 512 C "t3" State.empty [] 0x32
-- ... and the catch observes code 0x32 through the external self-call.
def t3code_is_0x32 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t3code" State.empty [] 0x32
-- Early binding fixes the SLOT, not the value: a mutation through another
-- path is visible through the pointer.
def t4_live_mutation_is_33 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t4" State.empty [] 33
-- Mapping-value pointer write-through control.
def t5_mapping_ref_is_88 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t5" State.empty [] 88
-- Dangling WRITE through the captured slot, read back through it.
def t6_dangling_write_is_5 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t6" State.empty [] 5
-- #188 write-through re-pins: indexed / mapping-value / uint[] storage-ref
-- RETURNS still re-point and write through.
def t7_ref_return_writes_42 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t7" State.empty [] 42
def t8_mapping_return_writes_88 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t8" State.empty [] 88
def t9_array_return_push_55 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "t9" State.empty [] 55

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue t1_pop_then_deref_is_0
#guard isOkTrue t2_pop_push_deref_is_9
#guard isOkTrue t3_bind_oob_panics_0x32
#guard isOkTrue t3code_is_0x32
#guard isOkTrue t4_live_mutation_is_33
#guard isOkTrue t5_mapping_ref_is_88
#guard isOkTrue t6_dangling_write_is_5
#guard isOkTrue t7_ref_return_writes_42
#guard isOkTrue t8_mapping_return_writes_88
#guard isOkTrue t9_array_return_push_55

end StorageRefEarlyBind
end Witness
end Solidity
end SolidCore

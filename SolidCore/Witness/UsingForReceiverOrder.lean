import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for the evaluation order of attached (using-for) internal calls.

For an internal library function or a free function attached with
using L for T, solc 0.8.35 (legacy codegen, ExpressionCompiler.cpp
lines 704-723, FunctionType::Kind::Internal) evaluates the call
arguments before the bound receiver: recv.g(args) runs args left to
right and evaluates recv last. Explicit L.g(recv, args) stays left to
right. The model rewrote recv.g(args) into the positional helper call
helper(recv, args), so n.g(bump()) read n before bump() ran and
(10 / c).g(x + 100) reported Panic(0x12) instead of the argument's
Panic(0x11).

The fix rewrites such a call, when the order is observable, to the
function's receiver-last twin g__recv_last(args, recv), whose ordinary
left-to-right argument evaluation is solc's order. The storage-pointer
receiver case failed to lower before the fix.

Covers the submission, a free function, chained and two-argument calls, a
call receiver, index and storage-pointer receivers, nested positions
(binary operand, explicit call argument, ternary), an argument that
assigns the receiver, the Panic order, and controls (explicit library
call, local receiver, side-effect-free operands). Expected values are
from forge on solc 0.8.35.
-/

namespace SolidCore.Solidity.Witness.UsingForReceiverOrder

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

/-- Solidity source of the unit below (imported AST):

    
    library L {
        function g(uint256 a, uint256 b) internal pure returns (uint256) {
            return a + b;
        }
    
        function h(uint256 a, uint256 b) internal pure returns (uint256) {
            return a * 1000 + b;
        }
    
        function k3(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
            return a * 1000000 + b * 1000 + c;
        }
    
        function get(uint256[] storage s, uint256 i) internal view returns (uint256) {
            return s[i];
        }
    }
    
    function fg(uint256 a, uint256 b) pure returns (uint256) {
        return a * 1000 + b;
    }
    
    contract C {
        using L for uint256;
        using L for uint256[];
        using {fg} for uint256;
    
        uint256 n;
        uint256 k;
        uint256[3] vals;
        mapping(uint256 => uint256[]) m;
    
        function bump() internal returns (uint256) {
            n += 1;
            return n;
        }
    
        function setK(uint256 v) internal returns (uint256) {
            k = v;
            return v;
        }
    
        function f() external returns (uint256) {
            return n.g(bump());
        }
    
        function freeFn() external returns (uint256) {
            return n.fg(bump());
        }
    
        function chained() external returns (uint256) {
            return n.h(bump()).h(bump());
        }
    
        function twoArgs() external returns (uint256) {
            return n.k3(bump(), bump());
        }
    
        function recvCall() external returns (uint256) {
            return bump().h(n);
        }
    
        function indexRecv() external returns (uint256) {
            vals[0] = 10;
            vals[1] = 20;
            vals[2] = 30;
            return vals[k].g(setK(2));
        }
    
        function storageRefRecv() external returns (uint256) {
            m[0].push(1);
            m[0].push(2);
            m[1].push(3);
            m[1].push(4);
            return m[k].get(setK(1));
        }
    
        function panicOrder(uint256 c, uint256 x) external pure returns (uint256) {
            return (10 / c).g(x + 100);
        }
    
        function inBinary() external returns (uint256) {
            return n + n.g(bump());
        }
    
        function inExplicitArg() external returns (uint256) {
            return L.h(n.g(bump()), n);
        }
    
        function explicitControl() external returns (uint256) {
            return L.h(n, bump());
        }
    
        function assignArg() external pure returns (uint256) {
            uint256 x = 3;
            return x.h(x = 5);
        }
    
        function inTernary(bool c) external returns (uint256) {
            return c ? n.h(bump()) : 7;
        }
    
        function localRecv() external returns (uint256) {
            uint256 x = 4;
            return x.h(bump());
        }
    
        function pureControl(uint256 a, uint256 b) external pure returns (uint256) {
            return a.h(b);
        }
    }
-/
def importedSourceName : String := "Main.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.library
  name := "L"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "1000"))) (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "k3",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }, { name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "1000000"))) (Expr.binary BinaryOp.mul (Expr.ident "b") (Expr.literal (Literal.number "1000")))) (Expr.ident "c")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.internal_,
    mutability := StateMutability.view,
    params := [{ name := some "s", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.storage }, { name := some "i", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "s") (Expr.ident "i")))]) })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.usingDecl
  { library := { segments := ["L"] },
    functions := [],
    target := some (Ty.uint 256),
    global := false }), (ContractItem.usingDecl
  { library := { segments := ["L"] },
    functions := [],
    target := some (Ty.array (Ty.uint 256) (none)),
    global := false }), (ContractItem.usingDecl
  { library := { segments := [] },
    functions := [{ function := { segments := ["fg"] }, operator? := none }],
    target := some (Ty.uint 256),
    global := false }), (ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "k",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "vals",
    ty := Ty.array (Ty.uint 256) (some 3),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.uint 256) (Ty.array (Ty.uint 256) (none)),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "setK",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "k") AssignOp.assign (Expr.ident "v")), Stmt.returnValues (some (Expr.ident "v"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "n") "g") [Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "freeFn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "n") "fg") [Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "chained",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.call (Expr.member (Expr.ident "n") "h") [Arg.positional (Expr.call (Expr.ident "bump") [])]) "h") [Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "twoArgs",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "n") "k3") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "recvCall",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.call (Expr.ident "bump") []) "h") [Arg.positional (Expr.ident "n")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "indexRecv",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "vals") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.literal (Literal.number "10"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "vals") (Expr.literal (Literal.number "1"))) AssignOp.assign (Expr.literal (Literal.number "20"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "vals") (Expr.literal (Literal.number "2"))) AssignOp.assign (Expr.literal (Literal.number "30"))), Stmt.returnValues (some (Expr.call (Expr.member (Expr.index (Expr.ident "vals") (Expr.ident "k")) "g") [Arg.positional (Expr.call (Expr.ident "setK") [Arg.positional (Expr.literal (Literal.number "2"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "storageRefRecv",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) "push") [Arg.positional (Expr.literal (Literal.number "1"))]), Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "0"))) "push") [Arg.positional (Expr.literal (Literal.number "2"))]), Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1"))) "push") [Arg.positional (Expr.literal (Literal.number "3"))]), Stmt.expr (Expr.call (Expr.member (Expr.index (Expr.ident "m") (Expr.literal (Literal.number "1"))) "push") [Arg.positional (Expr.literal (Literal.number "4"))]), Stmt.returnValues (some (Expr.call (Expr.member (Expr.index (Expr.ident "m") (Expr.ident "k")) "get") [Arg.positional (Expr.call (Expr.ident "setK") [Arg.positional (Expr.literal (Literal.number "1"))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "panicOrder",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "c", ty := Ty.uint 256, location := none }, { name := some "x", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.binary BinaryOp.div (Expr.literal (Literal.number "10")) (Expr.ident "c")) "g") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inBinary",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "n") (Expr.call (Expr.member (Expr.ident "n") "g") [Arg.positional (Expr.call (Expr.ident "bump") [])])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inExplicitArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "h") [Arg.positional (Expr.call (Expr.member (Expr.ident "n") "g") [Arg.positional (Expr.call (Expr.ident "bump") [])]), Arg.positional (Expr.ident "n")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "explicitControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.typeName (Ty.user ({ segments := ["L"] }))) "h") [Arg.positional (Expr.ident "n"), Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "assignArg",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "3"))), Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "x") "h") [Arg.positional (Expr.assign (Expr.ident "x") AssignOp.assign (Expr.literal (Literal.number "5")))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "inTernary",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "c", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ternary (Expr.ident "c") (Expr.call (Expr.member (Expr.ident "n") "h") [Arg.positional (Expr.call (Expr.ident "bump") [])]) (Expr.literal (Literal.number "7"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "localRecv",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "x", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "4"))), Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "x") "h") [Arg.positional (Expr.call (Expr.ident "bump") [])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pureControl",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "a") "h") [Arg.positional (Expr.ident "b")]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0, SourceItem.freeFunction
  { kind := FunctionKind.function,
    name := some "fg",
    visibility := none,
    mutability := StateMutability.pure,
    params := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.binary BinaryOp.mul (Expr.ident "a") (Expr.literal (Literal.number "1000"))) (Expr.ident "b")))]) }, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

def callWordEq (fn : Name) (args : List Value) (expected : Word) : Bool :=
  match CheckedInput.callContract 1024 importedSourceUnit "C"
      (CallTarget.name fn) State.empty args with
  | Except.ok (CallResult.returned _ [value]) =>
      match Value.asWord? value with
      | some word => wordEq word expected
      | none => false
  | _ => false

def callPanicEq (fn : Name) (args : List Value) (code : Word) : Bool :=
  match CheckedInput.callContract 1024 importedSourceUnit "C"
      (CallTarget.name fn) State.empty args with
  | Except.ok (CallResult.reverted _ (RevertData.panic c)) => wordEq c code
  | _ => false

-- submission: bump() runs before the receiver n is read
def check_f : Bool :=
  callWordEq "f" [] 2

-- free function attached with using
def check_freeFn : Bool :=
  callWordEq "freeFn" [] 1001

-- chained x.h(a()).h(b()): outer argument, then the inner call
def check_chained : Bool :=
  callWordEq "chained" [] 2002001

-- both arguments, left to right, then the receiver
def check_twoArgs : Bool :=
  callWordEq "twoArgs" [] 2001002

-- receiver is itself a call: argument n is read first
def check_recvCall : Bool :=
  callWordEq "recvCall" [] 1000

-- index receiver vals[k] is evaluated after setK(2)
def check_indexRecv : Bool :=
  callWordEq "indexRecv" [] 32

-- storage-pointer receiver m[k] is evaluated after setK(1)
def check_storageRefRecv : Bool :=
  callWordEq "storageRefRecv" [] 4

-- attached call as a binary operand
def check_inBinary : Bool :=
  callWordEq "inBinary" [] 3

-- attached call as an explicit call argument
def check_inExplicitArg : Bool :=
  callWordEq "inExplicitArg" [] 2001

-- control: explicit L.h(n, bump()) stays left to right
def check_explicitControl : Bool :=
  callWordEq "explicitControl" [] 1

-- argument assigns the receiver variable
def check_assignArg : Bool :=
  callWordEq "assignArg" [] 5005

-- attached call in a ternary branch
def check_inTernary_11 : Bool :=
  callWordEq "inTernary" [Value.word 1] 1001

-- untaken ternary branch
def check_inTernary_12 : Bool :=
  callWordEq "inTernary" [Value.word 0] 7

-- control: local receiver
def check_localRecv : Bool :=
  callWordEq "localRecv" [] 4001

-- control: side-effect-free operands
def check_pureControl : Bool :=
  callWordEq "pureControl" [Value.word 3, Value.word 4] 3004

-- the argument overflow (Panic 0x11) wins over the receiver division by zero
def check_panicOrder : Bool :=
  callPanicEq "panicOrder" [Value.word 0, Value.word (2 ^ 256 - 1)] 0x11

#guard importedContractAccepted
#guard check_f
#guard check_freeFn
#guard check_chained
#guard check_twoArgs
#guard check_recvCall
#guard check_indexRecv
#guard check_storageRefRecv
#guard check_inBinary
#guard check_inExplicitArg
#guard check_explicitControl
#guard check_assignArg
#guard check_inTernary_11
#guard check_inTernary_12
#guard check_localRecv
#guard check_pureControl
#guard check_panicOrder

end SolidCore.Solidity.Witness.UsingForReceiverOrder
